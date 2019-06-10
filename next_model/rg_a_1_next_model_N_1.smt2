;N_1
;base
(declare-sort |iml.ports.Port| 0)

(declare-sort |__unnamed__.iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>| 0)

(declare-sort |SWIMLAnnex.Command| 0)

(declare-sort |SWIMLAnnex.MC_SW| 0)

(declare-sort |SWIMLAnnex.WaypointManager| 0)

(declare-sort |SWIMLAnnex.RadioDriver| 0)

(declare-sort |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>| 0)

(declare-sort |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>>| 0)

(declare-sort |SWIMLAnnex.FlightPattern| 0)

(declare-sort |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>| 0)

(declare-sort |__unnamed__.iml.connectivity.Connector<iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>>| 0)

(declare-sort |SWIMLAnnex.Coordinate| 0)

(declare-sort |SWIMLAnnex.MissionWindow_dot_Impl| 0)

(declare-sort |SWIMLAnnex.UARTDriver| 0)

(declare-sort |SWIMLAnnex.Mission| 0)

(declare-sort |SWIMLAnnex.Map| 0)

(declare-sort |SWIMLAnnex.FlightPlanner| 0)

(declare-sort |SWIMLAnnex.Command_dot_Impl| 0)

(declare-sort |iml.ports.FlowPoint| 0)

(declare-sort |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>| 0)

(declare-sort |SWIMLAnnex.Mission_dot_Impl| 0)

(declare-sort |SWIMLAnnex.Coordinate_dot_Impl| 0)

(declare-sort |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>>| 0)

(declare-sort |SWIMLAnnex.MissionWindow| 0)

(declare-sort |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>>| 0)

(declare-sort |SWIMLAnnex.Map_dot_Impl| 0)

(declare-sort |SWIMLAnnex.MC_SW_dot_Impl| 0)

(declare-fun |SWIMLAnnex.MC_SW.position_status| (|SWIMLAnnex.MC_SW|) |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>|)

(declare-fun |SWIMLAnnex.MC_SW_dot_Impl.c5| (|SWIMLAnnex.MC_SW_dot_Impl|) |__unnamed__.iml.connectivity.Connector<iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>>|)

(declare-fun |SWIMLAnnex.RadioDriver.recv_map_in| (|SWIMLAnnex.RadioDriver|) |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>|)

(declare-fun |SWIMLAnnex.MC_SW_dot_Impl.c6| (|SWIMLAnnex.MC_SW_dot_Impl|) |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>>|)

(declare-fun |SWIMLAnnex.MC_SW_dot_Impl.c7| (|SWIMLAnnex.MC_SW_dot_Impl|) |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>>|)

(declare-fun |SWIMLAnnex.MC_SW_dot_Impl.c1| (|SWIMLAnnex.MC_SW_dot_Impl|) |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>>|)

(declare-fun |SWIMLAnnex.MC_SW_dot_Impl.c2| (|SWIMLAnnex.MC_SW_dot_Impl|) |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>>|)

(declare-const |SWIMLAnnex.inst|  |SWIMLAnnex.MC_SW_dot_Impl|)

(declare-fun |SWIMLAnnex.MC_SW_dot_Impl.c3| (|SWIMLAnnex.MC_SW_dot_Impl|) |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>>|)

(declare-fun |SWIMLAnnex.Map_dot_Impl.wp1| (|SWIMLAnnex.Map_dot_Impl|) |SWIMLAnnex.Coordinate_dot_Impl|)

(declare-fun |SWIMLAnnex.Map_dot_Impl.wp2| (|SWIMLAnnex.Map_dot_Impl|) |SWIMLAnnex.Coordinate_dot_Impl|)

(declare-fun |iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.data| (|__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>|) |SWIMLAnnex.Coordinate_dot_Impl|)

(declare-fun |iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>>.source| (|__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>>|) |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>|)

(declare-fun |SWIMLAnnex.Map_dot_Impl.wp3| (|SWIMLAnnex.Map_dot_Impl|) |SWIMLAnnex.Coordinate_dot_Impl|)

(declare-fun |SWIMLAnnex.Map_dot_Impl.wp4| (|SWIMLAnnex.Map_dot_Impl|) |SWIMLAnnex.Coordinate_dot_Impl|)

(declare-fun |SWIMLAnnex.MC_SW_dot_Impl.RADIO| (|SWIMLAnnex.MC_SW_dot_Impl|) |SWIMLAnnex.RadioDriver|)

(declare-fun |SWIMLAnnex.MissionWindow_dot_Impl.extends_SWIMLAnnex.MissionWindow| (|SWIMLAnnex.MissionWindow_dot_Impl|) |SWIMLAnnex.MissionWindow|)

(declare-fun |iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>>.source| (|__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>>|) |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>|)

(declare-fun |SWIMLAnnex.MC_SW_dot_Impl.c8| (|SWIMLAnnex.MC_SW_dot_Impl|) |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>>|)

(declare-fun |SWIMLAnnex.MC_SW_dot_Impl.c9| (|SWIMLAnnex.MC_SW_dot_Impl|) |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>>|)

(declare-fun |iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.flowpoint| (|__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>|) |iml.ports.FlowPoint|)

(declare-fun |__unnamed__.__some_iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>>_2033268925| (|__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>| |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>|) |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>>|)

(declare-fun |SWIMLAnnex.Command_dot_Impl.HMAC| (|SWIMLAnnex.Command_dot_Impl|) |Bool|)

(declare-fun |SWIMLAnnex.good_HMAC| (|Bool|) |Bool|)

(declare-fun |SWIMLAnnex.RadioDriver.send_status_out| (|SWIMLAnnex.RadioDriver|) |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>|)

(declare-fun |__unnamed__.__some_iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>>_2033268925| (|__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>| |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>|) |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>>|)

(declare-fun |iml.ports.FlowPoint.lowerBound| (|iml.ports.FlowPoint|) |Real|)

(declare-fun |SWIMLAnnex.WaypointManager.g1| (|SWIMLAnnex.WaypointManager|) |Bool|)

(declare-fun |iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.flowpoint| (|__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>|) |iml.ports.FlowPoint|)

(declare-fun |SWIMLAnnex.FlightPlanner.a1| (|SWIMLAnnex.FlightPlanner|) |Bool|)

(declare-fun |SWIMLAnnex.FlightPlanner.a2| (|SWIMLAnnex.FlightPlanner|) |Bool|)

(declare-fun |SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Coordinate_dot_Impl|) |Int|)

(declare-fun |SWIMLAnnex.FlightPlanner.recv_map| (|SWIMLAnnex.FlightPlanner|) |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>|)

(declare-fun |SWIMLAnnex.Mission_dot_Impl.extends_SWIMLAnnex.Mission| (|SWIMLAnnex.Mission_dot_Impl|) |SWIMLAnnex.Mission|)

(declare-fun |iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>>.target| (|__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>>|) |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>|)

(declare-fun |SWIMLAnnex.good_coordinate| (|SWIMLAnnex.Coordinate_dot_Impl|) |Bool|)

(declare-fun |iml.connectivity.Connector<iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>>.source| (|__unnamed__.iml.connectivity.Connector<iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>>|) |__unnamed__.iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>|)

(declare-fun |SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Coordinate_dot_Impl|) |Int|)

(declare-fun |SWIMLAnnex.MC_SW.recv_map| (|SWIMLAnnex.MC_SW|) |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>|)

(declare-fun |SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.FlightPlanner|) |__unnamed__.iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>|)

(declare-fun |iml.ports.FlowPoint.event| (|iml.ports.FlowPoint|) |Bool|)

(declare-fun |iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>|) |SWIMLAnnex.Command_dot_Impl|)

(declare-fun |SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.WaypointManager|) |__unnamed__.iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>|)

(declare-fun |SWIMLAnnex.UARTDriver.waypoint_in| (|SWIMLAnnex.UARTDriver|) |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>|)

(declare-fun |iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|__unnamed__.iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>|) |SWIMLAnnex.Mission_dot_Impl|)

(declare-fun |iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>|) |SWIMLAnnex.MissionWindow_dot_Impl|)

(declare-fun |SWIMLAnnex.UARTDriver.position_status_out| (|SWIMLAnnex.UARTDriver|) |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>|)

(declare-fun |SWIMLAnnex.good_gs_command| (|SWIMLAnnex.Command_dot_Impl|) |Bool|)

(declare-fun |iml.ports.FlowPoint.upperBound| (|iml.ports.FlowPoint|) |Real|)

(declare-fun |SWIMLAnnex.Map_dot_Impl.extends_SWIMLAnnex.Map| (|SWIMLAnnex.Map_dot_Impl|) |SWIMLAnnex.Map|)

(declare-fun |iml.connectivity.connect<iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>>| (|__unnamed__.iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>| |__unnamed__.iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>|) |__unnamed__.iml.connectivity.Connector<iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>>|)

(declare-fun |iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.extends_iml.ports.Port| (|__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>|) |iml.ports.Port|)

(declare-fun |SWIMLAnnex.RadioDriver.recv_map_out| (|SWIMLAnnex.RadioDriver|) |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>|)

(declare-fun |iml.connectivity.connect<iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>>| (|__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>| |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>|) |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>>|)

(declare-fun |SWIMLAnnex.UARTDriver.position_status_in| (|SWIMLAnnex.UARTDriver|) |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>|)

(declare-fun |iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.flowpoint| (|__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>|) |iml.ports.FlowPoint|)

(declare-fun |SWIMLAnnex.MC_SW_dot_Impl.FPLN| (|SWIMLAnnex.MC_SW_dot_Impl|) |SWIMLAnnex.FlightPlanner|)

(declare-fun |SWIMLAnnex.MC_SW.a1| (|SWIMLAnnex.MC_SW|) |Bool|)

(declare-fun |SWIMLAnnex.Mission_dot_Impl.wp10| (|SWIMLAnnex.Mission_dot_Impl|) |SWIMLAnnex.Coordinate_dot_Impl|)

(declare-fun |SWIMLAnnex.MC_SW_dot_Impl.c10| (|SWIMLAnnex.MC_SW_dot_Impl|) |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>>|)

(declare-fun |SWIMLAnnex.Command_dot_Impl.Map| (|SWIMLAnnex.Command_dot_Impl|) |SWIMLAnnex.Map_dot_Impl|)

(declare-fun |SWIMLAnnex.MC_SW_dot_Impl.c11| (|SWIMLAnnex.MC_SW_dot_Impl|) |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>>|)

(declare-fun |SWIMLAnnex.Mission_dot_Impl.wp8| (|SWIMLAnnex.Mission_dot_Impl|) |SWIMLAnnex.Coordinate_dot_Impl|)

(declare-fun |SWIMLAnnex.Mission_dot_Impl.wp7| (|SWIMLAnnex.Mission_dot_Impl|) |SWIMLAnnex.Coordinate_dot_Impl|)

(declare-fun |SWIMLAnnex.Mission_dot_Impl.wp9| (|SWIMLAnnex.Mission_dot_Impl|) |SWIMLAnnex.Coordinate_dot_Impl|)

(declare-fun |iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>>.target| (|__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>>|) |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>|)

(declare-fun |SWIMLAnnex.Mission_dot_Impl.wp4| (|SWIMLAnnex.Mission_dot_Impl|) |SWIMLAnnex.Coordinate_dot_Impl|)

(declare-fun |SWIMLAnnex.Mission_dot_Impl.wp3| (|SWIMLAnnex.Mission_dot_Impl|) |SWIMLAnnex.Coordinate_dot_Impl|)

(declare-fun |SWIMLAnnex.Mission_dot_Impl.wp6| (|SWIMLAnnex.Mission_dot_Impl|) |SWIMLAnnex.Coordinate_dot_Impl|)

(declare-fun |SWIMLAnnex.Mission_dot_Impl.wp5| (|SWIMLAnnex.Mission_dot_Impl|) |SWIMLAnnex.Coordinate_dot_Impl|)

(declare-fun |SWIMLAnnex.FlightPlanner.position_status| (|SWIMLAnnex.FlightPlanner|) |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>|)

(declare-fun |SWIMLAnnex.MC_SW_dot_Impl.extends_SWIMLAnnex.MC_SW| (|SWIMLAnnex.MC_SW_dot_Impl|) |SWIMLAnnex.MC_SW|)

(declare-fun |SWIMLAnnex.UARTDriver.g1| (|SWIMLAnnex.UARTDriver|) |Bool|)

(declare-fun |SWIMLAnnex.WaypointManager.waypoint| (|SWIMLAnnex.WaypointManager|) |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>|)

(declare-fun |SWIMLAnnex.MC_SW_dot_Impl.UART| (|SWIMLAnnex.MC_SW_dot_Impl|) |SWIMLAnnex.UARTDriver|)

(declare-fun |SWIMLAnnex.Mission_dot_Impl.wp2| (|SWIMLAnnex.Mission_dot_Impl|) |SWIMLAnnex.Coordinate_dot_Impl|)

(declare-fun |SWIMLAnnex.Mission_dot_Impl.wp1| (|SWIMLAnnex.Mission_dot_Impl|) |SWIMLAnnex.Coordinate_dot_Impl|)

(declare-fun |SWIMLAnnex.MC_SW_dot_Impl.WPM| (|SWIMLAnnex.MC_SW_dot_Impl|) |SWIMLAnnex.WaypointManager|)

(declare-fun |SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Coordinate_dot_Impl|) |Int|)

(declare-fun |SWIMLAnnex.Command_dot_Impl.extends_SWIMLAnnex.Command| (|SWIMLAnnex.Command_dot_Impl|) |SWIMLAnnex.Command|)

(declare-fun |iml.connectivity.connect<iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>>| (|__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>| |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>|) |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>>|)

(declare-fun |SWIMLAnnex.MissionWindow_dot_Impl.wp1| (|SWIMLAnnex.MissionWindow_dot_Impl|) |SWIMLAnnex.Coordinate_dot_Impl|)

(declare-fun |SWIMLAnnex.MissionWindow_dot_Impl.wp2| (|SWIMLAnnex.MissionWindow_dot_Impl|) |SWIMLAnnex.Coordinate_dot_Impl|)

(declare-fun |SWIMLAnnex.MissionWindow_dot_Impl.wp3| (|SWIMLAnnex.MissionWindow_dot_Impl|) |SWIMLAnnex.Coordinate_dot_Impl|)

(declare-fun |SWIMLAnnex.RadioDriver.send_status_in| (|SWIMLAnnex.RadioDriver|) |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>|)

(declare-fun |SWIMLAnnex.MissionWindow_dot_Impl.wp4| (|SWIMLAnnex.MissionWindow_dot_Impl|) |SWIMLAnnex.Coordinate_dot_Impl|)

(declare-fun |SWIMLAnnex.RadioDriver.a1| (|SWIMLAnnex.RadioDriver|) |Bool|)

(declare-fun |SWIMLAnnex.UARTDriver.waypoint_out| (|SWIMLAnnex.UARTDriver|) |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>|)

(declare-fun |SWIMLAnnex.good_mission| (|SWIMLAnnex.Mission_dot_Impl|) |Bool|)

(declare-fun |iml.connectivity.Connector<iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>>.target| (|__unnamed__.iml.connectivity.Connector<iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>>|) |__unnamed__.iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>|)

(declare-fun |SWIMLAnnex.MC_SW.send_status| (|SWIMLAnnex.MC_SW|) |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>|)

(declare-fun |iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.flowpoint| (|__unnamed__.iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>|) |iml.ports.FlowPoint|)

(declare-fun |SWIMLAnnex.Coordinate_dot_Impl.extends_SWIMLAnnex.Coordinate| (|SWIMLAnnex.Coordinate_dot_Impl|) |SWIMLAnnex.Coordinate|)

(declare-fun |SWIMLAnnex.WaypointManager.a1| (|SWIMLAnnex.WaypointManager|) |Bool|)

(declare-fun |iml.connectivity.connect<iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>>| (|__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>| |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>|) |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>>|)

(declare-fun |SWIMLAnnex.WaypointManager.position_status| (|SWIMLAnnex.WaypointManager|) |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>|)

(declare-fun |SWIMLAnnex.good_map| (|SWIMLAnnex.Map_dot_Impl|) |Bool|)

(declare-fun |__unnamed__.__some_iml.connectivity.Connector<iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>>_2033268925| (|__unnamed__.iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>| |__unnamed__.iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>|) |__unnamed__.iml.connectivity.Connector<iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>>|)

(declare-fun |iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>>.source| (|__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>>|) |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>|)

(declare-fun |iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.event| (|__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>|) |Bool|)

(declare-fun |SWIMLAnnex.UARTDriver.a1| (|SWIMLAnnex.UARTDriver|) |Bool|)

(declare-fun |__unnamed__.__some_iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>>_2033268925| (|__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>| |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>|) |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>>|)

(declare-fun |SWIMLAnnex.Command_dot_Impl.Pattern| (|SWIMLAnnex.Command_dot_Impl|) |SWIMLAnnex.FlightPattern|)

(declare-fun |SWIMLAnnex.MC_SW.waypoint| (|SWIMLAnnex.MC_SW|) |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>|)

(declare-fun |iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.extends_iml.ports.Port| (|__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>|) |iml.ports.Port|)

(declare-fun |SWIMLAnnex.MissionWindow_dot_Impl.crc| (|SWIMLAnnex.MissionWindow_dot_Impl|) |Bool|)

(declare-fun |SWIMLAnnex.good_mission_window| (|SWIMLAnnex.MissionWindow_dot_Impl|) |Bool|)

(declare-fun |iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.event| (|__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>|) |Bool|)

(declare-fun |SWIMLAnnex.MC_SW.g1| (|SWIMLAnnex.MC_SW|) |Bool|)

(declare-fun |iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.extends_iml.ports.Port| (|__unnamed__.iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>|) |iml.ports.Port|)

(declare-fun |SWIMLAnnex.FlightPlanner.g1| (|SWIMLAnnex.FlightPlanner|) |Bool|)

(declare-fun |iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.extends_iml.ports.Port| (|__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>|) |iml.ports.Port|)

(declare-fun |iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>>.target| (|__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>>|) |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>|)

(declare-fun |SWIMLAnnex.RadioDriver.g1| (|SWIMLAnnex.RadioDriver|) |Bool|)

(declare-fun |iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.event| (|__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>|) |Bool|)

(assert (forall ((x |__unnamed__.iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>|) 
(y |__unnamed__.iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>|)) 
(= (|iml.connectivity.connect<iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>>| x y) 
(|__unnamed__.__some_iml.connectivity.Connector<iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>>_2033268925| x y))))

(assert (forall ((__inst__ |SWIMLAnnex.MC_SW_dot_Impl|)) 
(= (|SWIMLAnnex.MC_SW_dot_Impl.c5| __inst__) 
(|iml.connectivity.connect<iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>>| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| __inst__)) 
(|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| __inst__))))))

(assert (forall ((__inst__ |SWIMLAnnex.MC_SW_dot_Impl|)) 
(= (|SWIMLAnnex.MC_SW_dot_Impl.c6| __inst__) 
(|iml.connectivity.connect<iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>>| (|SWIMLAnnex.WaypointManager.waypoint| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| __inst__)) 
(|SWIMLAnnex.UARTDriver.waypoint_in| (|SWIMLAnnex.MC_SW_dot_Impl.UART| __inst__))))))

(assert (forall ((__inst__ |SWIMLAnnex.MC_SW_dot_Impl|)) 
(= (|SWIMLAnnex.MC_SW_dot_Impl.c7| __inst__) 
(|iml.connectivity.connect<iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>>| (|SWIMLAnnex.UARTDriver.position_status_out| (|SWIMLAnnex.MC_SW_dot_Impl.UART| __inst__)) 
(|SWIMLAnnex.WaypointManager.position_status| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| __inst__))))))

(assert (forall ((x |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>|) 
(y |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>|)) 
(= (|iml.connectivity.connect<iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>>| x y) 
(|__unnamed__.__some_iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>>_2033268925| x y))))

(assert (forall ((__inst__ |SWIMLAnnex.MC_SW_dot_Impl|)) 
(= (|SWIMLAnnex.MC_SW_dot_Impl.c1| __inst__) 
(|iml.connectivity.connect<iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>>| (|SWIMLAnnex.MC_SW.recv_map| (|SWIMLAnnex.MC_SW_dot_Impl.extends_SWIMLAnnex.MC_SW| __inst__)) 
(|SWIMLAnnex.RadioDriver.recv_map_in| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| __inst__))))))

(assert (forall ((__inst__ |SWIMLAnnex.MC_SW_dot_Impl|)) 
(= (|SWIMLAnnex.MC_SW_dot_Impl.c2| __inst__) 
(|iml.connectivity.connect<iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>>| (|SWIMLAnnex.RadioDriver.send_status_out| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| __inst__)) 
(|SWIMLAnnex.MC_SW.send_status| (|SWIMLAnnex.MC_SW_dot_Impl.extends_SWIMLAnnex.MC_SW| __inst__))))))

(assert (forall ((__inst__ |SWIMLAnnex.MC_SW_dot_Impl|)) 
(= (|SWIMLAnnex.MC_SW_dot_Impl.c3| __inst__) 
(|iml.connectivity.connect<iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>>| (|SWIMLAnnex.RadioDriver.recv_map_out| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| __inst__)) 
(|SWIMLAnnex.FlightPlanner.recv_map| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| __inst__))))))

(assert (forall ((coord |SWIMLAnnex.Coordinate_dot_Impl|)) 
(= (|SWIMLAnnex.good_coordinate| coord) 
(and (and (and (and (and (>= (|SWIMLAnnex.Coordinate_dot_Impl.lat| coord) 
(- 90)) 
(<= (|SWIMLAnnex.Coordinate_dot_Impl.lat| coord) 90)) 
(>= (|SWIMLAnnex.Coordinate_dot_Impl.long| coord) 
(- 180))) 
(<= (|SWIMLAnnex.Coordinate_dot_Impl.long| coord) 180)) 
(>= (|SWIMLAnnex.Coordinate_dot_Impl.alt| coord) 0)) 
(<= (|SWIMLAnnex.Coordinate_dot_Impl.alt| coord) 15000)))))

(assert (forall ((__inst__ |SWIMLAnnex.WaypointManager|)) 
(= (|SWIMLAnnex.WaypointManager.a1| __inst__) 
(|SWIMLAnnex.good_mission| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.flight_plan| __inst__))))))

(assert (forall ((x |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>|) 
(y |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>|)) 
(= (|iml.connectivity.connect<iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>>| x y) 
(|__unnamed__.__some_iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>>_2033268925| x y))))

(assert (forall ((map |SWIMLAnnex.Map_dot_Impl|)) 
(= (|SWIMLAnnex.good_map| map) 
(and (and (and (|SWIMLAnnex.good_coordinate| (|SWIMLAnnex.Map_dot_Impl.wp1| map)) 
(|SWIMLAnnex.good_coordinate| (|SWIMLAnnex.Map_dot_Impl.wp2| map))) 
(|SWIMLAnnex.good_coordinate| (|SWIMLAnnex.Map_dot_Impl.wp3| map))) 
(|SWIMLAnnex.good_coordinate| (|SWIMLAnnex.Map_dot_Impl.wp4| map))))))

(assert (forall ((__inst__ |SWIMLAnnex.MC_SW|)) 
(= (|SWIMLAnnex.MC_SW.a1| __inst__) 
(= (|SWIMLAnnex.Command_dot_Impl.HMAC| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.MC_SW.recv_map| __inst__))) true))))

(assert (forall ((x |__unnamed__.iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>|) 
(y |__unnamed__.iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>|)) 
(and (= (|iml.connectivity.Connector<iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>>.source| (|__unnamed__.__some_iml.connectivity.Connector<iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>>_2033268925| y x)) x) 
(= (|iml.connectivity.Connector<iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>>.target| (|__unnamed__.__some_iml.connectivity.Connector<iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>>_2033268925| y x)) y))))

(assert (forall ((__inst__ |SWIMLAnnex.MC_SW_dot_Impl|)) 
(= (|SWIMLAnnex.MC_SW_dot_Impl.c10| __inst__) 
(|iml.connectivity.connect<iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>>| (|SWIMLAnnex.UARTDriver.waypoint_out| (|SWIMLAnnex.MC_SW_dot_Impl.UART| __inst__)) 
(|SWIMLAnnex.MC_SW.waypoint| (|SWIMLAnnex.MC_SW_dot_Impl.extends_SWIMLAnnex.MC_SW| __inst__))))))

(assert (forall ((__inst__ |SWIMLAnnex.MC_SW_dot_Impl|)) 
(= (|SWIMLAnnex.MC_SW_dot_Impl.c11| __inst__) 
(|iml.connectivity.connect<iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>>| (|SWIMLAnnex.MC_SW.position_status| (|SWIMLAnnex.MC_SW_dot_Impl.extends_SWIMLAnnex.MC_SW| __inst__)) 
(|SWIMLAnnex.UARTDriver.position_status_in| (|SWIMLAnnex.MC_SW_dot_Impl.UART| __inst__))))))

(assert (forall ((__inst__ |SWIMLAnnex.UARTDriver|)) 
(= (|SWIMLAnnex.UARTDriver.a1| __inst__) 
(|SWIMLAnnex.good_mission_window| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.waypoint_in| __inst__))))))

(assert (forall ((x |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>|) 
(y |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>|)) 
(and (= (|iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>>.source| (|__unnamed__.__some_iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>>_2033268925| y x)) x) 
(= (|iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>>.target| (|__unnamed__.__some_iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>>_2033268925| y x)) y))))

(assert (forall ((__inst__ |SWIMLAnnex.UARTDriver|)) 
(= (|SWIMLAnnex.UARTDriver.g1| __inst__) 
(= (|SWIMLAnnex.MissionWindow_dot_Impl.crc| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.waypoint_out| __inst__))) true))))

(assert (forall ((__inst__ |SWIMLAnnex.MC_SW_dot_Impl|)) 
(= (|SWIMLAnnex.MC_SW_dot_Impl.c8| __inst__) 
(|iml.connectivity.connect<iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>>| (|SWIMLAnnex.UARTDriver.position_status_out| (|SWIMLAnnex.MC_SW_dot_Impl.UART| __inst__)) 
(|SWIMLAnnex.FlightPlanner.position_status| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| __inst__))))))

(assert (forall ((__inst__ |SWIMLAnnex.MC_SW_dot_Impl|)) 
(= (|SWIMLAnnex.MC_SW_dot_Impl.c9| __inst__) 
(|iml.connectivity.connect<iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>>| (|SWIMLAnnex.UARTDriver.position_status_out| (|SWIMLAnnex.MC_SW_dot_Impl.UART| __inst__)) 
(|SWIMLAnnex.RadioDriver.send_status_in| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| __inst__))))))

(assert (forall ((x |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>|) 
(y |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>|)) 
(and (= (|iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>>.source| (|__unnamed__.__some_iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>>_2033268925| y x)) x) 
(= (|iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>>.target| (|__unnamed__.__some_iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>>_2033268925| y x)) y))))

(assert (forall ((hmac |Bool|)) 
(= (|SWIMLAnnex.good_HMAC| hmac) 
(or (= hmac true) 
(= hmac false)))))

(assert (forall ((x |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>|) 
(y |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>|)) 
(= (|iml.connectivity.connect<iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>>| x y) 
(|__unnamed__.__some_iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>>_2033268925| x y))))

(assert (forall ((win |SWIMLAnnex.MissionWindow_dot_Impl|)) 
(= (|SWIMLAnnex.good_mission_window| win) 
(and (and (and (|SWIMLAnnex.good_coordinate| (|SWIMLAnnex.MissionWindow_dot_Impl.wp1| win)) 
(|SWIMLAnnex.good_coordinate| (|SWIMLAnnex.MissionWindow_dot_Impl.wp2| win))) 
(|SWIMLAnnex.good_coordinate| (|SWIMLAnnex.MissionWindow_dot_Impl.wp3| win))) 
(|SWIMLAnnex.good_coordinate| (|SWIMLAnnex.MissionWindow_dot_Impl.wp4| win))))))

(assert (forall ((x |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>|) 
(y |__unnamed__.iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>|)) 
(and (= (|iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>>.source| (|__unnamed__.__some_iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>>_2033268925| y x)) x) 
(= (|iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>>.target| (|__unnamed__.__some_iml.connectivity.Connector<iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>>_2033268925| y x)) y))))

(assert (forall ((cmd |SWIMLAnnex.Command_dot_Impl|)) 
(= (|SWIMLAnnex.good_gs_command| cmd) 
(and (|SWIMLAnnex.good_map| (|SWIMLAnnex.Command_dot_Impl.Map| cmd)) 
(|SWIMLAnnex.good_HMAC| (|SWIMLAnnex.Command_dot_Impl.HMAC| cmd))))))

(assert (forall ((__inst__ |SWIMLAnnex.MC_SW|)) 
(= (|SWIMLAnnex.MC_SW.g1| __inst__) 
(= (|SWIMLAnnex.MissionWindow_dot_Impl.crc| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.MC_SW.waypoint| __inst__))) true))))

(assert (forall ((__inst__ |SWIMLAnnex.WaypointManager|)) 
(= (|SWIMLAnnex.WaypointManager.g1| __inst__) 
(|SWIMLAnnex.good_mission_window| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.waypoint| __inst__))))))

(assert (forall ((__inst__ |SWIMLAnnex.FlightPlanner|)) 
(= (|SWIMLAnnex.FlightPlanner.g1| __inst__) 
(|SWIMLAnnex.good_mission| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.flight_plan| __inst__))))))

(assert (forall ((__inst__ |SWIMLAnnex.RadioDriver|)) 
(= (|SWIMLAnnex.RadioDriver.g1| __inst__) 
(= (|SWIMLAnnex.Command_dot_Impl.HMAC| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.recv_map_out| __inst__))) true))))

(assert (forall ((__inst__ |SWIMLAnnex.FlightPlanner|)) 
(= (|SWIMLAnnex.FlightPlanner.a1| __inst__) 
(= (|SWIMLAnnex.Command_dot_Impl.HMAC| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.recv_map| __inst__))) true))))

(assert (forall ((__inst__ |SWIMLAnnex.RadioDriver|)) 
(= (|SWIMLAnnex.RadioDriver.a1| __inst__) 
(= (|SWIMLAnnex.Command_dot_Impl.HMAC| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.recv_map_in| __inst__))) true))))

(assert (forall ((mission |SWIMLAnnex.Mission_dot_Impl|)) 
(= (|SWIMLAnnex.good_mission| mission) 
(and (and (and (and (and (and (and (and (and (|SWIMLAnnex.good_coordinate| (|SWIMLAnnex.Mission_dot_Impl.wp1| mission)) 
(|SWIMLAnnex.good_coordinate| (|SWIMLAnnex.Mission_dot_Impl.wp2| mission))) 
(|SWIMLAnnex.good_coordinate| (|SWIMLAnnex.Mission_dot_Impl.wp3| mission))) 
(|SWIMLAnnex.good_coordinate| (|SWIMLAnnex.Mission_dot_Impl.wp4| mission))) 
(|SWIMLAnnex.good_coordinate| (|SWIMLAnnex.Mission_dot_Impl.wp5| mission))) 
(|SWIMLAnnex.good_coordinate| (|SWIMLAnnex.Mission_dot_Impl.wp6| mission))) 
(|SWIMLAnnex.good_coordinate| (|SWIMLAnnex.Mission_dot_Impl.wp7| mission))) 
(|SWIMLAnnex.good_coordinate| (|SWIMLAnnex.Mission_dot_Impl.wp8| mission))) 
(|SWIMLAnnex.good_coordinate| (|SWIMLAnnex.Mission_dot_Impl.wp9| mission))) 
(|SWIMLAnnex.good_coordinate| (|SWIMLAnnex.Mission_dot_Impl.wp10| mission))))))

(assert (forall ((__inst__ |SWIMLAnnex.FlightPlanner|)) 
(= (|SWIMLAnnex.FlightPlanner.a2| __inst__) 
(|SWIMLAnnex.good_gs_command| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.recv_map| __inst__))))))

;N_1
;kb
(assert (and (and (and (and (|SWIMLAnnex.MC_SW.a1| (|SWIMLAnnex.MC_SW_dot_Impl.extends_SWIMLAnnex.MC_SW| |SWIMLAnnex.inst|)) 
(=> (|SWIMLAnnex.RadioDriver.a1| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)) 
(|SWIMLAnnex.RadioDriver.g1| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))) 
(=> (and (|SWIMLAnnex.FlightPlanner.a1| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|)) 
(|SWIMLAnnex.FlightPlanner.a2| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))) 
(|SWIMLAnnex.FlightPlanner.g1| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|)))) 
(=> (|SWIMLAnnex.WaypointManager.a1| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|)) 
(|SWIMLAnnex.WaypointManager.g1| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|)))) 
(=> (|SWIMLAnnex.UARTDriver.a1| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|)) 
(|SWIMLAnnex.UARTDriver.g1| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|))))) 

;N_1
;goal
(assert (not  (|SWIMLAnnex.MC_SW.g1| (|SWIMLAnnex.MC_SW_dot_Impl.extends_SWIMLAnnex.MC_SW| |SWIMLAnnex.inst|)) ))

(check-sat)
(get-model)

;N_1
;cmodel
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Map_dot_Impl.wp1| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.recv_map_in| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Map_dot_Impl.wp1| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.recv_map_in| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Map_dot_Impl.wp1| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.recv_map_in| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Map_dot_Impl.wp2| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.recv_map_in| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Map_dot_Impl.wp2| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.recv_map_in| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Map_dot_Impl.wp2| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.recv_map_in| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Map_dot_Impl.wp3| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.recv_map_in| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Map_dot_Impl.wp3| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.recv_map_in| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Map_dot_Impl.wp3| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.recv_map_in| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Map_dot_Impl.wp4| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.recv_map_in| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Map_dot_Impl.wp4| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.recv_map_in| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Map_dot_Impl.wp4| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.recv_map_in| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Command_dot_Impl.HMAC| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.recv_map_in| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.event| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.flowpoint| (|SWIMLAnnex.RadioDriver.recv_map_in| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.upperBound| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.flowpoint| (|SWIMLAnnex.RadioDriver.recv_map_in| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.lowerBound| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.flowpoint| (|SWIMLAnnex.RadioDriver.recv_map_in| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.event| (|SWIMLAnnex.RadioDriver.recv_map_in| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.send_status_out| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.send_status_out| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.send_status_out| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.event| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.flowpoint| (|SWIMLAnnex.RadioDriver.send_status_out| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.upperBound| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.flowpoint| (|SWIMLAnnex.RadioDriver.send_status_out| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.lowerBound| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.flowpoint| (|SWIMLAnnex.RadioDriver.send_status_out| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.event| (|SWIMLAnnex.RadioDriver.send_status_out| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.send_status_in| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.send_status_in| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.send_status_in| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.event| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.flowpoint| (|SWIMLAnnex.RadioDriver.send_status_in| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.upperBound| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.flowpoint| (|SWIMLAnnex.RadioDriver.send_status_in| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.lowerBound| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.flowpoint| (|SWIMLAnnex.RadioDriver.send_status_in| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.event| (|SWIMLAnnex.RadioDriver.send_status_in| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Map_dot_Impl.wp1| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.recv_map_out| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Map_dot_Impl.wp1| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.recv_map_out| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Map_dot_Impl.wp1| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.recv_map_out| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Map_dot_Impl.wp2| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.recv_map_out| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Map_dot_Impl.wp2| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.recv_map_out| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Map_dot_Impl.wp2| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.recv_map_out| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Map_dot_Impl.wp3| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.recv_map_out| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Map_dot_Impl.wp3| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.recv_map_out| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Map_dot_Impl.wp3| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.recv_map_out| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Map_dot_Impl.wp4| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.recv_map_out| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Map_dot_Impl.wp4| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.recv_map_out| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Map_dot_Impl.wp4| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.recv_map_out| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Command_dot_Impl.HMAC| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.RadioDriver.recv_map_out| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.event| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.flowpoint| (|SWIMLAnnex.RadioDriver.recv_map_out| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.upperBound| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.flowpoint| (|SWIMLAnnex.RadioDriver.recv_map_out| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.lowerBound| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.flowpoint| (|SWIMLAnnex.RadioDriver.recv_map_out| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.event| (|SWIMLAnnex.RadioDriver.recv_map_out| (|SWIMLAnnex.MC_SW_dot_Impl.RADIO| |SWIMLAnnex.inst|))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Mission_dot_Impl.wp1| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Mission_dot_Impl.wp1| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Mission_dot_Impl.wp1| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Mission_dot_Impl.wp2| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Mission_dot_Impl.wp2| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Mission_dot_Impl.wp2| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Mission_dot_Impl.wp3| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Mission_dot_Impl.wp3| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Mission_dot_Impl.wp3| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Mission_dot_Impl.wp4| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Mission_dot_Impl.wp4| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Mission_dot_Impl.wp4| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Mission_dot_Impl.wp5| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Mission_dot_Impl.wp5| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Mission_dot_Impl.wp5| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Mission_dot_Impl.wp6| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Mission_dot_Impl.wp6| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Mission_dot_Impl.wp6| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Mission_dot_Impl.wp7| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Mission_dot_Impl.wp7| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Mission_dot_Impl.wp7| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Mission_dot_Impl.wp8| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Mission_dot_Impl.wp8| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Mission_dot_Impl.wp8| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Mission_dot_Impl.wp9| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Mission_dot_Impl.wp9| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Mission_dot_Impl.wp9| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Mission_dot_Impl.wp10| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Mission_dot_Impl.wp10| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Mission_dot_Impl.wp10| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.event| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.flowpoint| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.upperBound| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.flowpoint| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.lowerBound| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.flowpoint| (|SWIMLAnnex.FlightPlanner.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Map_dot_Impl.wp1| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.recv_map| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Map_dot_Impl.wp1| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.recv_map| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Map_dot_Impl.wp1| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.recv_map| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Map_dot_Impl.wp2| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.recv_map| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Map_dot_Impl.wp2| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.recv_map| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Map_dot_Impl.wp2| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.recv_map| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Map_dot_Impl.wp3| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.recv_map| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Map_dot_Impl.wp3| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.recv_map| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Map_dot_Impl.wp3| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.recv_map| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Map_dot_Impl.wp4| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.recv_map| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Map_dot_Impl.wp4| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.recv_map| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Map_dot_Impl.wp4| (|SWIMLAnnex.Command_dot_Impl.Map| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.recv_map| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|)))))) ) ) 
;( get-value ( (|SWIMLAnnex.Command_dot_Impl.HMAC| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.recv_map| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.event| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.flowpoint| (|SWIMLAnnex.FlightPlanner.recv_map| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.upperBound| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.flowpoint| (|SWIMLAnnex.FlightPlanner.recv_map| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.lowerBound| (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.flowpoint| (|SWIMLAnnex.FlightPlanner.recv_map| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.EventDataPort<SWIMLAnnex.Command_dot_Impl>.event| (|SWIMLAnnex.FlightPlanner.recv_map| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.position_status| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.position_status| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.data| (|SWIMLAnnex.FlightPlanner.position_status| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.event| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.flowpoint| (|SWIMLAnnex.FlightPlanner.position_status| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.upperBound| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.flowpoint| (|SWIMLAnnex.FlightPlanner.position_status| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.lowerBound| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.flowpoint| (|SWIMLAnnex.FlightPlanner.position_status| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.event| (|SWIMLAnnex.FlightPlanner.position_status| (|SWIMLAnnex.MC_SW_dot_Impl.FPLN| |SWIMLAnnex.inst|))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Mission_dot_Impl.wp1| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Mission_dot_Impl.wp1| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Mission_dot_Impl.wp1| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Mission_dot_Impl.wp2| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Mission_dot_Impl.wp2| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Mission_dot_Impl.wp2| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Mission_dot_Impl.wp3| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Mission_dot_Impl.wp3| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Mission_dot_Impl.wp3| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Mission_dot_Impl.wp4| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Mission_dot_Impl.wp4| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Mission_dot_Impl.wp4| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Mission_dot_Impl.wp5| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Mission_dot_Impl.wp5| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Mission_dot_Impl.wp5| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Mission_dot_Impl.wp6| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Mission_dot_Impl.wp6| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Mission_dot_Impl.wp6| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Mission_dot_Impl.wp7| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Mission_dot_Impl.wp7| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Mission_dot_Impl.wp7| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Mission_dot_Impl.wp8| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Mission_dot_Impl.wp8| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Mission_dot_Impl.wp8| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Mission_dot_Impl.wp9| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Mission_dot_Impl.wp9| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Mission_dot_Impl.wp9| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.Mission_dot_Impl.wp10| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.Mission_dot_Impl.wp10| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.Mission_dot_Impl.wp10| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.event| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.flowpoint| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.upperBound| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.flowpoint| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.lowerBound| (|iml.ports.DataPort<SWIMLAnnex.Mission_dot_Impl>.flowpoint| (|SWIMLAnnex.WaypointManager.flight_plan| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.MissionWindow_dot_Impl.wp1| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.waypoint| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.MissionWindow_dot_Impl.wp1| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.waypoint| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.MissionWindow_dot_Impl.wp1| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.waypoint| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.MissionWindow_dot_Impl.wp2| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.waypoint| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.MissionWindow_dot_Impl.wp2| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.waypoint| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.MissionWindow_dot_Impl.wp2| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.waypoint| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.MissionWindow_dot_Impl.wp3| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.waypoint| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.MissionWindow_dot_Impl.wp3| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.waypoint| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.MissionWindow_dot_Impl.wp3| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.waypoint| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.MissionWindow_dot_Impl.wp4| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.waypoint| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.MissionWindow_dot_Impl.wp4| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.waypoint| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.MissionWindow_dot_Impl.wp4| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.waypoint| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.MissionWindow_dot_Impl.crc| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.waypoint| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.event| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.flowpoint| (|SWIMLAnnex.WaypointManager.waypoint| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.upperBound| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.flowpoint| (|SWIMLAnnex.WaypointManager.waypoint| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.lowerBound| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.flowpoint| (|SWIMLAnnex.WaypointManager.waypoint| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.event| (|SWIMLAnnex.WaypointManager.waypoint| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.position_status| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.position_status| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.data| (|SWIMLAnnex.WaypointManager.position_status| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.event| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.flowpoint| (|SWIMLAnnex.WaypointManager.position_status| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.upperBound| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.flowpoint| (|SWIMLAnnex.WaypointManager.position_status| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.lowerBound| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.flowpoint| (|SWIMLAnnex.WaypointManager.position_status| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.event| (|SWIMLAnnex.WaypointManager.position_status| (|SWIMLAnnex.MC_SW_dot_Impl.WPM| |SWIMLAnnex.inst|))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.position_status_in| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.position_status_in| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.position_status_in| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.event| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.flowpoint| (|SWIMLAnnex.UARTDriver.position_status_in| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.upperBound| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.flowpoint| (|SWIMLAnnex.UARTDriver.position_status_in| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.lowerBound| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.flowpoint| (|SWIMLAnnex.UARTDriver.position_status_in| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.event| (|SWIMLAnnex.UARTDriver.position_status_in| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.MissionWindow_dot_Impl.wp1| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.waypoint_out| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.MissionWindow_dot_Impl.wp1| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.waypoint_out| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.MissionWindow_dot_Impl.wp1| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.waypoint_out| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.MissionWindow_dot_Impl.wp2| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.waypoint_out| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.MissionWindow_dot_Impl.wp2| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.waypoint_out| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.MissionWindow_dot_Impl.wp2| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.waypoint_out| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.MissionWindow_dot_Impl.wp3| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.waypoint_out| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.MissionWindow_dot_Impl.wp3| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.waypoint_out| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.MissionWindow_dot_Impl.wp3| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.waypoint_out| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.MissionWindow_dot_Impl.wp4| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.waypoint_out| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.MissionWindow_dot_Impl.wp4| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.waypoint_out| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.MissionWindow_dot_Impl.wp4| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.waypoint_out| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.MissionWindow_dot_Impl.crc| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.waypoint_out| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.event| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.flowpoint| (|SWIMLAnnex.UARTDriver.waypoint_out| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.upperBound| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.flowpoint| (|SWIMLAnnex.UARTDriver.waypoint_out| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.lowerBound| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.flowpoint| (|SWIMLAnnex.UARTDriver.waypoint_out| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.event| (|SWIMLAnnex.UARTDriver.waypoint_out| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.position_status_out| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.position_status_out| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.position_status_out| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.event| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.flowpoint| (|SWIMLAnnex.UARTDriver.position_status_out| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.upperBound| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.flowpoint| (|SWIMLAnnex.UARTDriver.position_status_out| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.lowerBound| (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.flowpoint| (|SWIMLAnnex.UARTDriver.position_status_out| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.EventDataPort<SWIMLAnnex.Coordinate_dot_Impl>.event| (|SWIMLAnnex.UARTDriver.position_status_out| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.MissionWindow_dot_Impl.wp1| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.waypoint_in| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.MissionWindow_dot_Impl.wp1| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.waypoint_in| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.MissionWindow_dot_Impl.wp1| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.waypoint_in| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.MissionWindow_dot_Impl.wp2| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.waypoint_in| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.MissionWindow_dot_Impl.wp2| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.waypoint_in| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.MissionWindow_dot_Impl.wp2| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.waypoint_in| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.MissionWindow_dot_Impl.wp3| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.waypoint_in| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.MissionWindow_dot_Impl.wp3| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.waypoint_in| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.MissionWindow_dot_Impl.wp3| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.waypoint_in| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.lat| (|SWIMLAnnex.MissionWindow_dot_Impl.wp4| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.waypoint_in| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.long| (|SWIMLAnnex.MissionWindow_dot_Impl.wp4| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.waypoint_in| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.Coordinate_dot_Impl.alt| (|SWIMLAnnex.MissionWindow_dot_Impl.wp4| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.waypoint_in| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|))))) ) ) 
;( get-value ( (|SWIMLAnnex.MissionWindow_dot_Impl.crc| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.data| (|SWIMLAnnex.UARTDriver.waypoint_in| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.event| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.flowpoint| (|SWIMLAnnex.UARTDriver.waypoint_in| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.upperBound| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.flowpoint| (|SWIMLAnnex.UARTDriver.waypoint_in| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.FlowPoint.lowerBound| (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.flowpoint| (|SWIMLAnnex.UARTDriver.waypoint_in| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|)))) ) ) 
;( get-value ( (|iml.ports.EventDataPort<SWIMLAnnex.MissionWindow_dot_Impl>.event| (|SWIMLAnnex.UARTDriver.waypoint_in| (|SWIMLAnnex.MC_SW_dot_Impl.UART| |SWIMLAnnex.inst|))) ) ) ) ) 






