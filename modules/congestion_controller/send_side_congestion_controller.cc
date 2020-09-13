/*
 *  Copyright (c) 2012 The WebRTC project authors. All Rights Reserved.
 *
 *  Use of this source code is governed by a BSD-style license
 *  that can be found in the LICENSE file in the root of the source
 *  tree. An additional intellectual property rights grant can be found
 *  in the file PATENTS.  All contributing project authors may
 *  be found in the AUTHORS file in the root of the source tree.
 */

#include "modules/congestion_controller/include/send_side_congestion_controller.h"

#include <algorithm>
#include <memory>
#include <vector>
#include <cstring>
#include <string>
#include <arpa/inet.h>
#include <sys/socket.h>
#include <unistd.h>
#include <stdlib.h>
#include <iostream>
#include <stdio.h>
#include <math.h>
#include <cstdlib>
#include <fstream>
#include <fcntl.h>
#include <sys/time.h>

#include "absl/memory/memory.h"
#include "modules/bitrate_controller/include/bitrate_controller.h"
#include "modules/congestion_controller/congestion_window_pushback_controller.h"
#include "modules/congestion_controller/goog_cc/acknowledged_bitrate_estimator.h"
#include "modules/congestion_controller/goog_cc/probe_controller.h"
#include "modules/remote_bitrate_estimator/include/bwe_defines.h"
#include "rtc_base/checks.h"
#include "rtc_base/format_macros.h"
#include "rtc_base/logging.h"
#include "rtc_base/numerics/safe_conversions.h"
#include "rtc_base/rate_limiter.h"
#include "rtc_base/socket.h"
#include "rtc_base/timeutils.h"
#include "system_wrappers/include/field_trial.h"
#include "system_wrappers/include/runtime_enabled_features.h"
#include "rtc_base/json.h"
int RL_flag = 0;
namespace webrtc {
namespace {

const char kCwndExperiment[] = "WebRTC-CwndExperiment";
const char kPacerPushbackExperiment[] = "WebRTC-PacerPushbackExperiment";

// When CongestionWindowPushback is enabled, the pacer is oblivious to
// the congestion window. The relation between outstanding data and
// the congestion window affects encoder allocations directly.
const char kCongestionPushbackExperiment[] = "WebRTC-CongestionWindowPushback";

const int64_t kDefaultAcceptedQueueMs = 250;
int client = -1;
int portnum = 9999;
int bufsize = 1024;
//int begin_flag = 0;
//int send_succ = 0;
int conn = -1;
int Recv_flag = 0;
//int sent_info = 0;
int errorTimes = 0;
//int recvTimes = 0;;
bool CwndExperimentEnabled() {
  std::string experiment_string =
      webrtc::field_trial::FindFullName(kCwndExperiment);
  // The experiment is enabled iff the field trial string begins with "Enabled".
  return experiment_string.find("Enabled") == 0;
}

bool ReadCwndExperimentParameter(int64_t* accepted_queue_ms) {
  RTC_DCHECK(accepted_queue_ms);
  std::string experiment_string =
      webrtc::field_trial::FindFullName(kCwndExperiment);
  int parsed_values =
      sscanf(experiment_string.c_str(), "Enabled-%" PRId64, accepted_queue_ms);
  if (parsed_values == 1) {
    RTC_CHECK_GE(*accepted_queue_ms, 0)
        << "Accepted must be greater than or equal to 0.";
    return true;
  }
  return false;
}

bool IsCongestionWindowPushbackExperimentEnabled() {
  return webrtc::field_trial::IsEnabled(kCongestionPushbackExperiment) &&
         webrtc::field_trial::IsEnabled(kCwndExperiment);
}

std::unique_ptr<CongestionWindowPushbackController>
MaybeCreateCongestionWindowPushbackController() {
  return IsCongestionWindowPushbackExperimentEnabled()
             ? absl::make_unique<CongestionWindowPushbackController>()
             : nullptr;
}

static const int64_t kRetransmitWindowSizeMs = 500;

// Makes sure that the bitrate and the min, max values are in valid range.
static void ClampBitrates(int* bitrate_bps,
                          int* min_bitrate_bps,
                          int* max_bitrate_bps) {
  // TODO(holmer): We should make sure the default bitrates are set to 10 kbps,
  // and that we don't try to set the min bitrate to 0 from any applications.
  // The congestion controller should allow a min bitrate of 0.
  if (*min_bitrate_bps < congestion_controller::GetMinBitrateBps())
    *min_bitrate_bps = congestion_controller::GetMinBitrateBps();
  if (*max_bitrate_bps > 0)
    *max_bitrate_bps = std::max(*min_bitrate_bps, *max_bitrate_bps);
  if (*bitrate_bps > 0)
    *bitrate_bps = std::max(*min_bitrate_bps, *bitrate_bps);
}

std::vector<webrtc::PacketFeedback> ReceivedPacketFeedbackVector(
    const std::vector<webrtc::PacketFeedback>& input) {
  std::vector<PacketFeedback> received_packet_feedback_vector;
  auto is_received = [](const webrtc::PacketFeedback& packet_feedback) {
    return packet_feedback.arrival_time_ms !=
           webrtc::PacketFeedback::kNotReceived;
  };
  std::copy_if(input.begin(), input.end(),
               std::back_inserter(received_packet_feedback_vector),
               is_received);
  return received_packet_feedback_vector;
}

void SortPacketFeedbackVector(
    std::vector<webrtc::PacketFeedback>* const input) {
  RTC_DCHECK(input);
  std::sort(input->begin(), input->end(), PacketFeedbackComparator());
}

bool IsPacerPushbackExperimentEnabled() {
  return webrtc::field_trial::IsEnabled(kPacerPushbackExperiment) ||
         (!webrtc::field_trial::IsDisabled(kPacerPushbackExperiment) &&
          webrtc::runtime_enabled_features::IsFeatureEnabled(
              webrtc::runtime_enabled_features::kDualStreamModeFeatureName));
}

}  // namespace

SendSideCongestionController::SendSideCongestionController(
    const Clock* clock,
    Observer* observer,
    RtcEventLog* event_log,
    PacedSender* pacer)
    : clock_(clock),
      observer_(observer),
      event_log_(event_log),
      pacer_(pacer),
      bitrate_controller_(
          BitrateController::CreateBitrateController(clock_, event_log)),
      acknowledged_bitrate_estimator_(
          absl::make_unique<AcknowledgedBitrateEstimator>()),
      probe_controller_(new ProbeController()),
      retransmission_rate_limiter_(
          new RateLimiter(clock, kRetransmitWindowSizeMs)),
      transport_feedback_adapter_(clock_),
      last_reported_bitrate_bps_(0),
      last_reported_fraction_loss_(0),
      last_reported_rtt_(0),
      last_feedback_send_time_ms_(0),
      last_feedback_arrival_time_ms_(0),
      //last_update_bitrate_time_ms_(0),
      last_throughput_(0),
      network_state_(kNetworkUp),
      pause_pacer_(false),
      pacer_paused_(false),
      min_bitrate_bps_(congestion_controller::GetMinBitrateBps()),
      delay_based_bwe_(new DelayBasedBwe(event_log_)),
      in_cwnd_experiment_(CwndExperimentEnabled()),
      accepted_queue_ms_(kDefaultAcceptedQueueMs),
      was_in_alr_(false),
      send_side_bwe_with_overhead_(
          webrtc::field_trial::IsEnabled("WebRTC-SendSideBwe-WithOverhead")),
      transport_overhead_bytes_per_packet_(0),
      pacer_pushback_experiment_(IsPacerPushbackExperimentEnabled()),
      congestion_window_pushback_controller_(
          MaybeCreateCongestionWindowPushbackController()) {
  delay_based_bwe_->SetMinBitrate(min_bitrate_bps_);
  if (in_cwnd_experiment_ &&
      !ReadCwndExperimentParameter(&accepted_queue_ms_)) {
    RTC_LOG(LS_WARNING) << "Failed to parse parameters for CwndExperiment "
                           "from field trial string. Experiment disabled.";
    in_cwnd_experiment_ = false;
  }
}

SendSideCongestionController::~SendSideCongestionController() {}
int64_t last_update_throughput_time_ms = 0;
float last_throughput = 0;
void SendSideCongestionController::RegisterPacketFeedbackObserver(
    PacketFeedbackObserver* observer) {
  transport_feedback_adapter_.RegisterPacketFeedbackObserver(observer);
}

void SendSideCongestionController::DeRegisterPacketFeedbackObserver(
    PacketFeedbackObserver* observer) {
  transport_feedback_adapter_.DeRegisterPacketFeedbackObserver(observer);
}

void SendSideCongestionController::RegisterNetworkObserver(Observer* observer) {
  rtc::CritScope cs(&observer_lock_);
  RTC_DCHECK(observer_ == nullptr);
  observer_ = observer;
}

void SendSideCongestionController::DeRegisterNetworkObserver(
    Observer* observer) {
  rtc::CritScope cs(&observer_lock_);
  RTC_DCHECK_EQ(observer_, observer);
  observer_ = nullptr;
}

void SendSideCongestionController::SetBweBitrates(int min_bitrate_bps,
                                                  int start_bitrate_bps,
                                                  int max_bitrate_bps) {
  ClampBitrates(&start_bitrate_bps, &min_bitrate_bps, &max_bitrate_bps);
  bitrate_controller_->SetBitrates(start_bitrate_bps, min_bitrate_bps,
                                   max_bitrate_bps);

  {
    rtc::CritScope cs(&probe_lock_);
    probe_controller_->SetBitrates(min_bitrate_bps, start_bitrate_bps,
                                   max_bitrate_bps,
                                   clock_->TimeInMilliseconds());
    SendPendingProbes();
  }

  {
    rtc::CritScope cs(&bwe_lock_);
    if (start_bitrate_bps > 0)
      delay_based_bwe_->SetStartBitrate(start_bitrate_bps);
    min_bitrate_bps_ = min_bitrate_bps;
    delay_based_bwe_->SetMinBitrate(min_bitrate_bps_);
  }
  MaybeTriggerOnNetworkChanged();
}

void SendSideCongestionController::SetAllocatedSendBitrateLimits(
    int64_t min_send_bitrate_bps,
    int64_t max_padding_bitrate_bps,
    int64_t max_total_bitrate_bps) {
  pacer_->SetSendBitrateLimits(min_send_bitrate_bps, max_padding_bitrate_bps);

  rtc::CritScope cs(&probe_lock_);
  probe_controller_->OnMaxTotalAllocatedBitrate(max_total_bitrate_bps,
                                                clock_->TimeInMilliseconds());
  SendPendingProbes();
}

// TODO(holmer): Split this up and use SetBweBitrates in combination with
// OnNetworkRouteChanged.
void SendSideCongestionController::OnNetworkRouteChanged(
    const rtc::NetworkRoute& network_route,
    int bitrate_bps,
    int min_bitrate_bps,
    int max_bitrate_bps) {
  ClampBitrates(&bitrate_bps, &min_bitrate_bps, &max_bitrate_bps);
  // TODO(honghaiz): Recreate this object once the bitrate controller is
  // no longer exposed outside SendSideCongestionController.
  bitrate_controller_->ResetBitrates(bitrate_bps, min_bitrate_bps,
                                     max_bitrate_bps);

  transport_feedback_adapter_.SetNetworkIds(network_route.local_network_id,
                                            network_route.remote_network_id);
  {
    rtc::CritScope cs(&bwe_lock_);
    transport_overhead_bytes_per_packet_ = network_route.packet_overhead;
    min_bitrate_bps_ = min_bitrate_bps;
    delay_based_bwe_.reset(new DelayBasedBwe(event_log_));
    acknowledged_bitrate_estimator_.reset(new AcknowledgedBitrateEstimator());
    delay_based_bwe_->SetStartBitrate(bitrate_bps);
    delay_based_bwe_->SetMinBitrate(min_bitrate_bps);
  }
  {
    rtc::CritScope cs(&probe_lock_);
    probe_controller_->Reset(clock_->TimeInMilliseconds());
    probe_controller_->SetBitrates(min_bitrate_bps, bitrate_bps,
                                   max_bitrate_bps,
                                   clock_->TimeInMilliseconds());
    SendPendingProbes();
  }

  MaybeTriggerOnNetworkChanged();
}

BitrateController* SendSideCongestionController::GetBitrateController() const {
  return bitrate_controller_.get();
}

bool SendSideCongestionController::AvailableBandwidth(
    uint32_t* bandwidth) const {
  return bitrate_controller_->AvailableBandwidth(bandwidth);
}

RtcpBandwidthObserver* SendSideCongestionController::GetBandwidthObserver() {
  return bitrate_controller_.get();
}

RtcpBandwidthObserver* SendSideCongestionController::GetBandwidthObserver()
    const {
  return bitrate_controller_.get();
}

RateLimiter* SendSideCongestionController::GetRetransmissionRateLimiter() {
  return retransmission_rate_limiter_.get();
}

void SendSideCongestionController::SetPerPacketFeedbackAvailable(
    bool available) {}

void SendSideCongestionController::EnablePeriodicAlrProbing(bool enable) {
  rtc::CritScope cs(&probe_lock_);
  probe_controller_->EnablePeriodicAlrProbing(enable);
}

int64_t SendSideCongestionController::GetPacerQueuingDelayMs() const {
  return IsNetworkDown() ? 0 : pacer_->QueueInMs();
}

int64_t SendSideCongestionController::GetFirstPacketTimeMs() const {
  return pacer_->FirstSentPacketTimeMs();
}

TransportFeedbackObserver*
SendSideCongestionController::GetTransportFeedbackObserver() {
  return this;
}

void SendSideCongestionController::SignalNetworkState(NetworkState state) {
  RTC_LOG(LS_INFO) << "SignalNetworkState "
                   << (state == kNetworkUp ? "Up" : "Down");
  {
    rtc::CritScope cs(&network_state_lock_);
    pause_pacer_ = state == kNetworkDown;
    network_state_ = state;
  }

  {
    rtc::CritScope cs(&probe_lock_);
    NetworkAvailability msg;
    msg.at_time = Timestamp::ms(clock_->TimeInMilliseconds());
    msg.network_available = state == kNetworkUp;
    probe_controller_->OnNetworkAvailability(msg);
    SendPendingProbes();
  }
  MaybeTriggerOnNetworkChanged();
}

void SendSideCongestionController::SetTransportOverhead(
    size_t transport_overhead_bytes_per_packet) {
  rtc::CritScope cs(&bwe_lock_);
  transport_overhead_bytes_per_packet_ = transport_overhead_bytes_per_packet;
}

void SendSideCongestionController::OnSentPacket(
    const rtc::SentPacket& sent_packet) {
  // We're not interested in packets without an id, which may be stun packets,
  // etc, sent on the same transport.
  if (sent_packet.packet_id == -1)
    return;
  transport_feedback_adapter_.OnSentPacket(sent_packet.packet_id,
                                           sent_packet.send_time_ms);
  if (in_cwnd_experiment_)
    LimitOutstandingBytes(transport_feedback_adapter_.GetOutstandingBytes());
}

void SendSideCongestionController::OnRttUpdate(int64_t avg_rtt_ms,
                                               int64_t max_rtt_ms) {
  rtc::CritScope cs(&bwe_lock_);
  delay_based_bwe_->OnRttUpdate(avg_rtt_ms);
}

int64_t SendSideCongestionController::TimeUntilNextProcess() {
  return bitrate_controller_->TimeUntilNextProcess();
}

void SendSideCongestionController::SendPendingProbes() {
  for (auto probe_config : probe_controller_->GetAndResetPendingProbes()) {
    pacer_->CreateProbeCluster(probe_config.target_data_rate.bps());
  }
}

void SendSideCongestionController::Process() {
  bool pause_pacer;
  // TODO(holmer): Once this class is running on a task queue we should
  // replace this with a task instead.
  {
    rtc::CritScope lock(&network_state_lock_);
    pause_pacer = pause_pacer_;
  }
  if (pause_pacer && !pacer_paused_) {
    pacer_->Pause();
    pacer_paused_ = true;
  } else if (!pause_pacer && pacer_paused_) {
    pacer_->Resume();
    pacer_paused_ = false;
  }
  bitrate_controller_->Process();

  {
    rtc::CritScope cs(&probe_lock_);
    probe_controller_->SetAlrStartTimeMs(
        pacer_->GetApplicationLimitedRegionStartTime());
    probe_controller_->Process(clock_->TimeInMilliseconds());
    SendPendingProbes();
  }
  MaybeTriggerOnNetworkChanged();
}

void SendSideCongestionController::AddPacket(
    uint32_t ssrc,
    uint16_t sequence_number,
    size_t length,
    const PacedPacketInfo& pacing_info) {
  if (send_side_bwe_with_overhead_) {
    rtc::CritScope cs(&bwe_lock_);
    length += transport_overhead_bytes_per_packet_;
  }
  transport_feedback_adapter_.AddPacket(ssrc, sequence_number, length,
                                        pacing_info);
}

int ConvertToNum(char buf[])
{
  int sum = 0;
  int i = 0;
  while(buf[i] != '%' && i<8)
  {
    sum = sum * 10;
    sum = sum + (buf[i] - '0');
    i = i + 1;
  }
  return sum;
}
bool check_exit_for_socket(const char *s) {
	for (int i = 0; i < int(strlen(s)); ++i) {
		if (s[i] == '#')
			return true;
	}
	return false;
}
//2019 infocom

std::string to_String(int n)
{
    int max =100;
    int m = n;
    char s[max];
    char ss[max];
    int i=0,j=0;
    if(n == 0)
    {
      ss[0] = '0';
      ss[1] = '\0';
      return ss;
    }
    if (n < 0)// 处理负数
    {
        m = 0 - m;
        j = 1;
        ss[0] = '-';
    }
    while (m>0)
    {
        s[i++] = m % 10 + '0';
        m /= 10;
    }
    s[i] = '\0';
    i = i - 1;
    while (i >= 0)
    {
        ss[j++] = s[i--];
    }
    ss[j] = '\0';
    return ss;
}

std::string long_to_String(int64_t n)
{
    int max =100;
    int64_t m = n;
    char s[max];
    char ss[max];
    int i=0,j=0;
    if (n < 0)// 处理负数
    {
        m = 0 - m;
        j = 1;
        ss[0] = '-';
    }
    while (m>0)
    {
        s[i++] = m % 10 + '0';
        m /= 10;
    }
    s[i] = '\0';
    i = i - 1;
    while (i >= 0)
    {
        ss[j++] = s[i--];
    }
    ss[j] = '\0';
    return ss;
}
//2019 infocom end
std::string FloatToString(float num)
{
  std::ostringstream oss;
  oss<<num;
  std::string str(oss.str());
  return str;
}
//2020-3-11 start
int SendToSever(int packet_length, float input_throughput[], float input_delay_interval[], float input_loss, int input_rtt, int input_pacer_bitrate)
//2020-3-11 end
{
  struct timeval tv;
  gettimeofday(&tv,NULL);
  struct tm* pTime;
  pTime = localtime(&tv.tv_sec);        
  //std::ofstream out("number.txt",std::ios::app);
  //out<<pTime->tm_hour<<":"<<pTime->tm_min<<":"<<pTime->tm_sec<<":"<<tv.tv_usec/1000<<" "<<errorTimes<<" "<<recvTimes<<std::endl;
  //out.close();
  int ret1 = 0;	
  if(errorTimes >10)
	return -1;	
  printf("WebRTC client number is %d",client);
  struct sockaddr_in serv_addr;
  if(client < 0)
  {   
		
                client = socket(AF_INET, SOCK_STREAM, 0);
		// set recv timeout
		struct timeval timeout = {0,120000};
		//setsockopt(client,SOL_SOCKET,SO_RCVTIMEO,(char*)&timeout,sizeof(struct timeval));
		//setsockopt(client,SOL_SOCKET,SO_SNDTIMEO,(char*)&timeout,sizeof(struct timeval));
		//printf("WebRTC client number is %d",client);
		serv_addr.sin_family = AF_INET;
		serv_addr.sin_port = htons(portnum);
		inet_pton(AF_INET, "127.0.0.1", &serv_addr.sin_addr);
		//int flag = fcntl(client, F_GETFD,0);
		fcntl(client,F_SETFL,fcntl(client,F_GETFD,0) | O_NONBLOCK);
		//flag &= ~O_NONBLOCK;
		//fcntl(client, F_SETFL, flag);
		
 
      //change 2020.2.12 re connect
        ret1 = connect(client, (const struct sockaddr*)&serv_addr, sizeof(serv_addr));
  //std::ofstream out("PCC_RL_hou.txt",std::ios::app);
  	//out<<"before"<<std::endl;
  	//out.close();	
	   if (ret1 == 0)
	   {
			 
		        //dont know why
			std::cout<<"connect suddccessfully"<<std::endl;
                        //std::ofstream out("PCC_RL_hou.txt",std::ios::app);
	  		//out<<"connect succ"<<std::endl;
	  		//out.close();
	  }
	  else
	  {		
			if(errno != EINPROGRESS)
			{
				std::cout<<"connect failed"<<std::endl;	
				//client = -1;
				//close(conn);
				close(client);
				client = -1;
				//conn = -1;
				errorTimes++;
		 		//std::ofstream out("PCC_RL_hou.txt",std::ios::app);
		  		//out<<"connect failed"<<std::endl;
		  		//out.close();
				return -1;
			}
			fd_set wset;
			FD_ZERO(&wset);  
    			FD_SET(client, &wset);  
    			//wset = rset; 
                        ret1 = select(client+1,NULL, &wset, NULL, &timeout);
			if ( ret1 == 0) {  
        			//close(client); /* timeout */  
	 			//close(conn);
				close(client);
				client = -1;
				//conn = -1;
        			//errno = ETIMEDOUT;  
				errorTimes++;
        			return -1;  
    			}  		
			int error = 0;
			if ( FD_ISSET(client, &wset)) {  
				socklen_t len = sizeof(error); 
				ret1 =  getsockopt(client, SOL_SOCKET, SO_ERROR, &error, &len);
				if ( ret1 < 0 || error != 0) { 
				//close(conn);
					close(client);
					client = -1;
					//conn = -1;
					errorTimes++;
					//std::ofstream out("PCC_RL_hou.txt",std::ios::app);
		  			//out<<"PENDING ERROR"<<std::endl;
		  			//out.close();
			    		return -1; /* Solaris pending error */  
				}
			} 
			else {  
			 	//close(conn);
					close(client);
					client = -1;
					errorTimes++;
					//conn = -1;
					//std::ofstream out("PCC_RL_hou.txt",std::ios::app);
		  			//out<<"CLIENT NOT SET"<<std::endl;
		  			//out.close();
	
					return -1;
		    	}  
           }
          
	
		 
		std::string user_id = "1234567890"; user_id = "ID["+user_id+"]";
		std::string user_isp = "china_mobile"; user_isp = "ISP["+ user_isp+"]";
		std::string user_network = "wifi"; user_network = "NET["+ user_network + "]";
		std::string user_starttime = "2020-3-2 15:00:00"; user_starttime = "TIME["+user_starttime + "]";
		std::string info  = user_id + user_isp + user_network + user_starttime;
		char userinfo[bufsize];
                memset(userinfo,'%',bufsize);
                for(int if_index = 0;if_index < int(info.length()); if_index++)
                {
			userinfo[if_index] = info[if_index];
                }
                int ret = send(client, userinfo, bufsize, 0);
		  //send(client, PPO_buffer, bufsize, 0);
		  if(ret < 0)
		  {
			std::cout<< "send info failed " << ret <<std::endl;
			
				close(conn);		
				close(client);
				client = -1;
				conn = -1;
				errorTimes++;
				//begin_flag = 0;
				//sent_info = 0;
				//2020-3-12
				//send_succ = 0;
		
			
                        //2020-3-3
                        RL_flag = 0;
			//std::ofstream out("PCC_RL_hou.txt",std::ios::app);
  			//out<<"send info failed "<<std::endl;
  			//out.close();
                        //errorTimes++;
			return -1;

		  }
		  else if(ret == 0)
		  {
			std::cout<< "Info connect interrupted" <<ret <<std::endl;
			//std::ofstream out("PCC_RL_hou.txt",std::ios::app);
  			//out<<"Info connect interrupted"<<std::endl;
  			//out.close();
                        //2020-3-3
			RL_flag = 0;
                        errorTimes++;
			
		  }
		  else
		  {
			std::cout<< "send Info successfully " << ret<<std::endl;
			//std::ofstream out("PCC_RL_hou.txt",std::ios::app);
  			//out<<"send Info successfully"<<std::endl;
  			//out.close();
		  }
  }
  char buffer[bufsize];
  memset(buffer,'%',bufsize);
  int i = 0;
  int j = 0;
  int k = 0;
  buffer[0] = packet_length + '0';
  for(i = 1; i < packet_length + 1; i++,j++)
  {
    buffer[i] = FloatToString(input_throughput[j]).length() + '0';// record the length of each throughput value
  }
  j = 0;
  k = i;

  for(k = i; k < i + packet_length; k++,j++)
  {
    buffer[k] = FloatToString(input_delay_interval[j]).length() + '0';// record the length of each delay_interval value
  }

  buffer[k] = FloatToString(input_loss).length() + '0';// record the length of loss value
  buffer[k+1] = to_String(input_rtt).length() + '0';// record the length of rtt value
  //2020-3-11 start
  buffer[k+2] = to_String(input_pacer_bitrate).length() + '0';
  int content_start = k + 3;//The real content starts after the recording of length
  //2020-3-11 end
  std::string content = "";

  for(i = 0;i < packet_length; i++)
    content += FloatToString(input_throughput[i]); // add  throughput values into the string

  for(i = 0;i < packet_length; i++)
    content += FloatToString(input_delay_interval[i]); // add delay_interval values into string

  content += FloatToString(input_loss); // add a single loss as the common value of this feedback packet
  content += to_String(input_rtt);// add a single rtt as the common value of this feedback packet
  //2020-3-11 start
  content += to_String(input_pacer_bitrate);
  //2020-3-11 end

  for(i = content_start, j = 0; j < int(content.length()); i++,j++)
    buffer[i] = content[j];// add the whole content into buffer

  char PPO_buffer[bufsize];
  memset(PPO_buffer,'%',bufsize);
  for(j=1;j<i+1;j++)
     PPO_buffer[j] = buffer[j-1];
  PPO_buffer[0] = '[';
  //PPO_buffer[j] = '\0';
  PPO_buffer[j] = ']';
  for(int k = 0;k<10;k++)
    printf("%c",PPO_buffer[k]);
  //buffer[i] = '\0';
  printf("WebRTC client number is %d\n",client);


  /*Json::Value jroot;
  Json::FastWriter jwriter;
  	jroot["abc"] = "test";
	for(int i = 0; i < packet_length; i++){
		root["throughput"].append(input_throughput[i]);
		root["loss"].append(input_loss);
		//root["throughput"].append(input_th)
		
	}
	std::string jsonContent = "";
	//Json::FastWriter fastWriter;
	jsonContent = jwriter.write(jroot);
	std::cout<<"json content "<<jroot<<std::endl;*/

  int ret = send(client, PPO_buffer, bufsize, 0);
  //send(client, PPO_buffer, bufsize, 0);
  if(ret < 0)
  {
	std::cout<< "send failed " << ret <<std::endl;
        //if(send_succ == 1)
        {
		close(conn);		
		close(client);
		client = -1;
		conn = -1;
		errorTimes++;
		//begin_flag = 0;
		//2020-3-3
                //sent_info = 0;
                //2020-3-12
		//send_succ = 0;
		
        }
       //std::ofstream out("PCC_RL_hou.txt",std::ios::app);
  	//out<<"send failed "<<std::endl;
        //out.close();

  }
  else if(ret == 0)
  {
	std::cout<< "connect interrupted" <<ret <<std::endl;
        close(conn);		
		close(client);
		client = -1;
		conn = -1;
		errorTimes++;
  }
  else
  {
	std::cout<< "send successfully " << ret<<std::endl;
       // if(send_succ == 0)
		//send_succ = 1;
  }
  //std::cout << "error is "<< errno <<std::endl;
  //printf("send error is %s, %d\n",strerror(errno),errno);
  std::cout << " flag = 0 send finish\n";
  return ret;
}


int GetResultFromServer()
{
  //char *ip = "127.0.0.1";
  
  char buffer[bufsize];
  memset(buffer,'%',bufsize);
  //int Bitrate_from_server = 1200000;

  //struct sockaddr_in serv_addr;
  //client = socket(AF_INET, SOCK_STREAM, 0);
  if(client < 0)
  {
    std::cout<<"回收速率建立连接失败";
    //2020-3-3
    RL_flag = 0;
    return 500000;
  }
	std::string temp;
	std::string str = "";
  printf("WebRTC client number is %d",client);
  int ret = recv(client, buffer, bufsize, 0);
  if((ret< 0 && (errno ==EINTR || errno == EWOULDBLOCK || errno == EAGAIN))||ret > 0)
  {
    std::cout << "recv succ "<<ret << std::endl;
  
  //std::cout<<"error is : " errno << std::endl;
  
	std::cout << std::endl;
	 char Tempbuffer[bufsize];
	 memset(Tempbuffer,'%',bufsize);
	 int i = 0;
	 while(buffer[i] == '%')
	 	i++;
	//2020-3-2 change to recv RL_flag
	 Recv_flag = buffer[i]-'0';
	 if(Recv_flag == 0 || Recv_flag == 1)
	 	RL_flag = Recv_flag;
	 else
		RL_flag = 0;
	 std::cout<<"recv flag is "<<Recv_flag<<std::endl;
	 i++;
	 for(int k=0; i<bufsize;k++,i++)
		Tempbuffer[k] = buffer[i];
		//close(conn);
		//close(client);
	for(int i=0;i<10;i++)
	     printf("%c",Tempbuffer[i]);
	return ConvertToNum(Tempbuffer);
  }
  /*else if(ret == 0)
  { 
    std::cout << "recv down "<<ret << std::endl;
    recvTimes++;
  }*/
  else
  {
    std::cout << "recv failed "<<ret << std::endl;
    errorTimes++;
    close(client);
    client = -1;
    return -1;
  }

}

void SendSideCongestionController::OnTransportFeedback(
    const rtcp::TransportFeedback& feedback) {
  RTC_DCHECK_RUNS_SERIALIZED(&worker_race_);
  transport_feedback_adapter_.OnTransportFeedback(feedback);
  std::vector<PacketFeedback> feedback_vector = ReceivedPacketFeedbackVector(
      transport_feedback_adapter_.GetTransportFeedbackVector());
  SortPacketFeedbackVector(&feedback_vector);

  bool currently_in_alr =
      pacer_->GetApplicationLimitedRegionStartTime().has_value();
  if (was_in_alr_ && !currently_in_alr) {
    int64_t now_ms = rtc::TimeMillis();
    acknowledged_bitrate_estimator_->SetAlrEndedTimeMs(now_ms);
    rtc::CritScope cs(&probe_lock_);
    probe_controller_->SetAlrEndedTimeMs(now_ms);
  }
  was_in_alr_ = currently_in_alr;
  std::cout<<"In send side congestion control"<<std::endl;
  acknowledged_bitrate_estimator_->IncomingPacketFeedbackVector(
      feedback_vector);
  DelayBasedBwe::Result result;
  {
    rtc::CritScope cs(&bwe_lock_);
    result = delay_based_bwe_->IncomingPacketFeedbackVector(
        feedback_vector, acknowledged_bitrate_estimator_->bitrate_bps(),
        clock_->TimeInMilliseconds());
  }
  if (result.updated) {
    bitrate_controller_->OnDelayBasedBweResult(result);
    // Update the estimate in the ProbeController, in case we want to probe.
    MaybeTriggerOnNetworkChanged();
  }
  if (result.recovered_from_overuse) {
    rtc::CritScope cs(&probe_lock_);
    probe_controller_->SetAlrStartTimeMs(
        pacer_->GetApplicationLimitedRegionStartTime());
    probe_controller_->RequestProbe(clock_->TimeInMilliseconds());
  }
  if (in_cwnd_experiment_) {
    LimitOutstandingBytes(transport_feedback_adapter_.GetOutstandingBytes());
  }
  
  int check_length = 0;
  float no_use = 0.0;
  for(const auto& packet_feedback : feedback_vector)
  {
    check_length++;
    no_use = packet_feedback.payload_size;
    
  }
  no_use = 0;
  printf("The feedback length is %d\n",check_length);
  rtc::CritScope lock(&network_state_lock_);

  int packet_length = 0;
  float input_throughput[20];
  float input_delay_interval_ms[20];
  //float packet_size = 0.0;
  float sum = 0;
  for(const auto& packet_feedback : feedback_vector)
  {
    //if(last_ten_index < 10)
    {
	if(packet_length > 10)
		continue;
    	//pkt_size[last_ten_index] = packet_feedback.payload_size;
    	//pkt_arrival_time[last_ten_index] = packet_feedback.arrival_time_ms;
    	float delay_interval_ms = static_cast<float>(
	      (packet_feedback.arrival_time_ms - packet_feedback.send_time_ms) -
	      (last_feedback_arrival_time_ms_ - last_feedback_send_time_ms_)); //callulate each packet's delay_interval

	    float packet_arrival_interval = static_cast<float>(
		  (packet_feedback.arrival_time_ms - last_feedback_arrival_time_ms_ )); //calculate each

	    float packet_size  = packet_feedback.payload_size; //calculate each packet's payload size

	    //pkt_sum += packet_size;
	    //std::cout<<"time interval is "<< <<std::endl;
	    last_feedback_arrival_time_ms_ = packet_feedback.arrival_time_ms;
	    last_feedback_send_time_ms_ = packet_feedback.send_time_ms;

	    if(last_throughput_ == 0 && packet_arrival_interval ==0)
	    {
		    last_throughput_ = 1.0;
        	    input_throughput[packet_length] = last_throughput_;
	    }
	    else if(packet_arrival_interval == 0)
	    {
		    input_throughput[packet_length] = last_throughput_;
	    }
	    else
	    {
    		input_throughput[packet_length] = packet_size * 8 / packet_arrival_interval /1000;
    		last_throughput_ = input_throughput[packet_length];
	    }
	    	
	    printf("packet_length is %d\n",packet_length);
	    input_delay_interval_ms[packet_length] = delay_interval_ms;
	    packet_length++;
	    //last_ten_index++;
	
    }
    /*
    else
    {
	    float delay_interval_ms = static_cast<float>(
	      (packet_feedback.arrival_time_ms - packet_feedback.send_time_ms) -
	      (last_feedback_arrival_time_ms_ - last_feedback_send_time_ms_)); //callulate each packet's delay_interval

	    float packet_arrival_interval = static_cast<float>(
		(packet_feedback.arrival_time_ms - pkt_arrival_time[0] )); //calculate sum
	    float sum = 0;
	    for(int temp = 1;temp<10;temp++)
	    {
		      sum += pkt_size[temp];
      }

	    float packet_size  = packet_feedback.payload_size + sum; //calculate each packet's payload size

	    //pkt_sum += packet_size;
	    //std::cout<<"time interval is "<< <<std::endl;
	    for(int temp = 0;temp < 9;temp++)
	    {
		    pkt_size[temp] = pkt_size[temp+1];
      } 
	    pkt_size[9] = packet_feedback.payload_size;
	    for(int temp = 0;temp < 9;temp++)
	    {
		    pkt_arrival_time[temp] = pkt_arrival_time[temp+1];
      } 
      pkt_arrival_time[9] = packet_feedback.arrival_time_ms;
	    last_feedback_arrival_time_ms_ = packet_feedback.arrival_time_ms;
	    last_feedback_send_time_ms_ = packet_feedback.send_time_ms;

	    if(last_throughput_ == 0 && packet_arrival_interval ==0)
	    {
		    last_throughput_ = 1.0;
        input_throughput[packet_length] = last_throughput_;
	    }
	    else if(packet_arrival_interval == 0)
	    {
		    input_throughput[packet_length] = last_throughput_;
	    }
	    else
	    {
    		input_throughput[packet_length] = packet_size * 8 / packet_arrival_interval / 1000;
    		last_throughput_ = input_throughput[packet_length];
	    }
	    	

	    input_delay_interval_ms[packet_length] = delay_interval_ms;
	    packet_length++;
    }*/
	sum += packet_feedback.payload_size;
  }
  int64_t throughput_now_time = clock_->TimeInMilliseconds();
  float throughput = 0.0;
  if((throughput_now_time - last_update_throughput_time_ms) == 0 ){
	throughput = last_throughput;
	last_update_throughput_time_ms = throughput_now_time;
  }
  else{
  throughput = sum*8 / (throughput_now_time - last_update_throughput_time_ms);
  last_throughput = throughput;
  last_update_throughput_time_ms = throughput_now_time;
  }
  struct timeval tv;
  gettimeofday(&tv,NULL);
  struct tm* pTime;
  pTime = localtime(&tv.tv_sec);

  //cancel throughput.txt 
  std::ofstream out("throughput.txt",std::ios::app);
  out<<pTime->tm_hour<<":"<<pTime->tm_min<<":"<<pTime->tm_sec<<":"<<tv.tv_usec/1000<<" "<< throughput <<std::endl;
  out.close();


  //time_interval = last_feedback_arrival_time_ms_ - last_feedback_tail_ms;
  //last_feedback_tail_ms = last_feedback_arrival_time_ms_;
  //std::cout<< "delay interval is "<<the_last <<std::endl;

  //rtc::CritScope lock(&network_state_lock_);
  float input_loss = last_reported_fraction_loss_ * 100.0 / 256.0;
  float input_rtt = last_reported_rtt_;
  //std::cout<< "loss is "<< input_loss<<std::endl;
  //std::cout<<"pkt sum is "<<pkt_sum<<std::endl;
  //std::cout << "time interval is "<<time_interval<<std::endl;
  //float throughput = pkt_sum / time_interval;
  //printf("input loss = %f ,delay interval = %f ,throughput = %f\n",input_loss,the_last,throughput );
  //printf("The relative length is %d   %d    %d\n",int(FloatToString(input_loss).length()),int(FloatToString(the_last).length()),int(FloatToString(throughput).length()));
  //printf("The converted result is %s\n",FloatToString(throughput).c_str());

  //SendToSever(input_loss, the_last);
  //printf("packet length is %d",packet_length);
  //std::ofstream out("time_consuming.txt",std::ios::app);
  //out<<clock_->TimeInMilliseconds()<<std::endl;
  printf("loss is ");
  printf("%s",FloatToString(input_loss).c_str());

  //rtc::CritScope lock(&network+state_lock_);
  //if(Clock::GetRealTimeClock()->TimeInMilliseconds() - last_update_bitrate_time_ms_ > 1000)
  {
	//int value[6] = {300,500,800,1000,1200,1500};	
        int rl_based_bitrate = 1000000;
	//2020-3-11 start
	int report_pacer_bitrate = int(pacer_->CalculatePacingBitrateForServer());
        //std::ofstream out("pacing.txt",std::ios::app);
        //out<<report_pacer_bitrate<<std::endl;
        //out.close();
        std::cout<< "Changing rates:"<< rl_based_bitrate << std::endl;
	if(SendToSever(packet_length,input_throughput,input_delay_interval_ms,input_loss, input_rtt, report_pacer_bitrate) <= 0)
        //2020-3-11 end
        {
		rl_based_bitrate = 500000;
		//2020-3-3
		RL_flag = 0;
		std::cout<<"wrong send"<<std::endl;
        }
        else
        {
                //std::ofstream out("time.txt",std::ios::app);
                //int64_t st = Clock::GetRealTimeClock()->TimeInMilliseconds();
 		 
  		rl_based_bitrate = GetResultFromServer();
		//int64_t et = Clock::GetRealTimeClock()->TimeInMilliseconds();
                //std::cout<<" getback rate is "<<rl_based_bitrate<<std::endl;
		//out<<st<<" "<<et<<std::endl;
 		//out.close();
                if(rl_based_bitrate <= 0 || rl_based_bitrate > 2500000)
                {
                   std::cout<<"wrong getback rate"<<std::endl;
                   rl_based_bitrate = 600000;
		   //2020-3-3
		   RL_flag = 0;
                }
                else
                  std::cout<<" getback rate is "<<rl_based_bitrate<<std::endl;
                //rl_based_bitrate = 600000;
        }
  	//if(rl_based_bitrate > 2000000)
		//rl_based_bitrate = 2000000;
	/*
	if(Clock::GetRealTimeClock()->TimeInMilliseconds() - last_update_bitrate_time_ms_ > 10*1000)
	{
		rl_based_bitrate = value[std::rand() % 6] * 1e3;
		last_check_bitrate = rl_based_bitrate;
		std::ofstream bitrate_log("random_bitrate.txt",std::ios::app);
  		bitrate_log<<rl_based_bitrate<<std::endl;
  		bitrate_log.close();
		last_update_bitrate_time_ms_ = Clock::GetRealTimeClock()->TimeInMilliseconds();
	}*/
  	bitrate_controller_->OnRLBasedBweResult(rl_based_bitrate);
        MaybeTriggerOnNetworkChanged();
	//last_update_bitrate_time_ms_ = Clock::GetRealTimeClock()->TimeInMilliseconds();
  }
  
  //out<<clock_->TimeInMilliseconds()<<std::endl;
  //out.close();
  //std::cout<< "Changing rates:"<< rl_based_bitrate << std::endl;
  


  //int rl_based_bitrate = GetResultFromServer();
  //std::ofstream out("PCC_RL_hou.txt",std::ios::app);
  //out<<rl_based_bitrate<<std::endl;
  //out.close();
//  bitrate_controller_->OnRLBasedBweResult(rl_based_bitrate);
  //std::cout<< "Changing rates:"<< rl_based_bitrate << std::endl;
  

}

void SendSideCongestionController::LimitOutstandingBytes(
    size_t num_outstanding_bytes) {
  RTC_DCHECK(in_cwnd_experiment_);
  rtc::CritScope lock(&network_state_lock_);
  absl::optional<int64_t> min_rtt_ms =
      transport_feedback_adapter_.GetMinFeedbackLoopRtt();
  // No valid RTT. Could be because send-side BWE isn't used, in which case
  // we don't try to limit the outstanding packets.
  if (!min_rtt_ms)
    return;
  const size_t kMinCwndBytes = 2 * 1500;
  size_t max_outstanding_bytes =
      std::max<size_t>((*min_rtt_ms + accepted_queue_ms_) *
                           last_reported_bitrate_bps_ / 1000 / 8,
                       kMinCwndBytes);
  RTC_LOG(LS_INFO) << clock_->TimeInMilliseconds()
                   << " Outstanding bytes: " << num_outstanding_bytes
                   << " pacer queue: " << pacer_->QueueInMs()
                   << " max outstanding: " << max_outstanding_bytes;
  RTC_LOG(LS_INFO) << "Feedback rtt: " << *min_rtt_ms
                   << " Bitrate: " << last_reported_bitrate_bps_;
  if (congestion_window_pushback_controller_) {
    congestion_window_pushback_controller_->UpdateOutstandingData(
        num_outstanding_bytes);
    congestion_window_pushback_controller_->UpdateMaxOutstandingData(
        max_outstanding_bytes);
  } else {
    pause_pacer_ = num_outstanding_bytes > max_outstanding_bytes;
  }
}

std::vector<PacketFeedback>
SendSideCongestionController::GetTransportFeedbackVector() const {
  RTC_DCHECK_RUNS_SERIALIZED(&worker_race_);
  return transport_feedback_adapter_.GetTransportFeedbackVector();
}

void SendSideCongestionController::SetPacingFactor(float pacing_factor) {
  pacer_->SetPacingFactor(pacing_factor);
}

void SendSideCongestionController::SetAllocatedBitrateWithoutFeedback(
    uint32_t bitrate_bps) {
  acknowledged_bitrate_estimator_->SetAllocatedBitrateWithoutFeedback(
      bitrate_bps);
}

void SendSideCongestionController::MaybeTriggerOnNetworkChanged() {
  uint32_t bitrate_bps;
  uint8_t fraction_loss;
  int64_t rtt;
  bool estimate_changed = bitrate_controller_->GetNetworkParameters(
      &bitrate_bps, &fraction_loss, &rtt);
  if (estimate_changed) {
    pacer_->SetEstimatedBitrate(bitrate_bps);
    {
      rtc::CritScope cs(&probe_lock_);
      probe_controller_->SetEstimatedBitrate(bitrate_bps,
                                             clock_->TimeInMilliseconds());
    }
    retransmission_rate_limiter_->SetMaxRate(bitrate_bps);
  }

  if (IsNetworkDown()) {
    bitrate_bps = 0;
  } else if (congestion_window_pushback_controller_) {
    rtc::CritScope lock(&network_state_lock_);
    bitrate_bps = congestion_window_pushback_controller_->UpdateTargetBitrate(
        bitrate_bps);
  } else if (!pacer_pushback_experiment_) {
    bitrate_bps = IsSendQueueFull() ? 0 : bitrate_bps;
  } else {
    int64_t queue_length_ms = pacer_->ExpectedQueueTimeMs();

    if (queue_length_ms == 0) {
      encoding_rate_ = 1.0;
    } else if (queue_length_ms > 50) {
      float encoding_rate = 1.0 - queue_length_ms / 1000.0;
      encoding_rate_ = std::min(encoding_rate_, encoding_rate);
      encoding_rate_ = std::max(encoding_rate_, 0.0f);
    }

    bitrate_bps *= encoding_rate_;
    bitrate_bps = bitrate_bps < 50000 ? 0 : bitrate_bps;
  }

  if (HasNetworkParametersToReportChanged(bitrate_bps, fraction_loss, rtt)) {
    int64_t probing_interval_ms;
    {
      rtc::CritScope cs(&bwe_lock_);
      probing_interval_ms = delay_based_bwe_->GetExpectedBwePeriodMs();
    }
    {
      rtc::CritScope cs(&observer_lock_);
      if (observer_) {
        observer_->OnNetworkChanged(bitrate_bps, fraction_loss, rtt,
                                    probing_interval_ms);
      }
    }
  }
}

bool SendSideCongestionController::HasNetworkParametersToReportChanged(
    uint32_t bitrate_bps,
    uint8_t fraction_loss,
    int64_t rtt) {
  rtc::CritScope cs(&network_state_lock_);
  bool changed =
      last_reported_bitrate_bps_ != bitrate_bps ||
      (bitrate_bps > 0 && (last_reported_fraction_loss_ != fraction_loss ||
                           last_reported_rtt_ != rtt));
  if (changed && (last_reported_bitrate_bps_ == 0 || bitrate_bps == 0)) {
    RTC_LOG(LS_INFO) << "Bitrate estimate state changed, BWE: " << bitrate_bps
                     << " bps.";
  }
  last_reported_bitrate_bps_ = bitrate_bps;
  last_reported_fraction_loss_ = fraction_loss;
  last_reported_rtt_ = rtt;
  return changed;
}

bool SendSideCongestionController::IsSendQueueFull() const {
  return pacer_->ExpectedQueueTimeMs() > PacedSender::kMaxQueueLengthMs;
}

bool SendSideCongestionController::IsNetworkDown() const {
  rtc::CritScope cs(&network_state_lock_);
  return network_state_ == kNetworkDown;
}

}  // namespace webrtc
