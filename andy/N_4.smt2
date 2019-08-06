;edge E_16 from __ to N_4.base
(declare-sort |SWB.MC_SW_dot_Impl| 0)
(declare-sort |__unnamed__.iml.connectivity.Connector<iml.ports.DataPort<SWB.Mission_dot_Impl>>| 0)
(declare-sort |SWB.Map| 0)
(declare-sort |SWB.Command| 0)
(declare-sort |__unnamed__.iml.ports.DataPort<SWB.Mission_dot_Impl>| 0)
(declare-sort |SWB.Mission| 0)
(declare-sort |__unnamed__.iml.ports.EventDataPort<SWB.Command_dot_Impl>| 0)
(declare-sort |SWB.WaypointManager| 0)
(declare-sort |SWB.MC_SW| 0)
(declare-sort |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.MissionWindow_dot_Impl>>| 0)
(declare-sort |SWB.Mission_dot_Impl| 0)
(declare-sort |iml.ports.FlowPoint| 0)
(declare-sort |SWB.MissionWindow| 0)
(declare-sort |__unnamed__.iml.ports.EventDataPort<SWB.Coordinate_dot_Impl>| 0)
(declare-sort |SWB.Command_dot_Impl| 0)
(declare-sort |SWB.Coordinate_dot_Impl| 0)
(declare-sort |SWB.Map_dot_Impl| 0)
(declare-sort |SWB.FlightPlanner| 0)
(declare-sort |iml.ports.Port| 0)
(declare-sort |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.Coordinate_dot_Impl>>| 0)
(declare-sort |SWB.Coordinate| 0)
(declare-sort |SWB.FlightPattern| 0)
(declare-sort |__unnamed__.iml.ports.EventDataPort<SWB.MissionWindow_dot_Impl>| 0)
(declare-sort |SWB.UARTDriver| 0)
(declare-sort |SWB.RadioDriver| 0)
(declare-sort |SWB.MissionWindow_dot_Impl| 0)
(declare-sort |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.Command_dot_Impl>>| 0)
(declare-fun |SWB.Map_dot_Impl.__base_SWB.Map| (|SWB.Map_dot_Impl|) |SWB.Map|)
(declare-fun |SWB.Map_dot_Impl.wp1| (|SWB.Map_dot_Impl|) |SWB.Coordinate_dot_Impl|)
(declare-fun |SWB.Map_dot_Impl.wp3| (|SWB.Map_dot_Impl|) |SWB.Coordinate_dot_Impl|)
(declare-fun |SWB.Map_dot_Impl.wp2| (|SWB.Map_dot_Impl|) |SWB.Coordinate_dot_Impl|)
(declare-fun |SWB.Map_dot_Impl.wp4| (|SWB.Map_dot_Impl|) |SWB.Coordinate_dot_Impl|)
(declare-fun |SWB.MC_SW_dot_Impl.__base_SWB.MC_SW| (|SWB.MC_SW_dot_Impl|) |SWB.MC_SW|)
(declare-fun |SWB.MC_SW_dot_Impl.c11| (|SWB.MC_SW_dot_Impl|) |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.Coordinate_dot_Impl>>|)
(declare-fun |SWB.MC_SW_dot_Impl.c10| (|SWB.MC_SW_dot_Impl|) |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.MissionWindow_dot_Impl>>|)
(declare-fun |SWB.MC_SW_dot_Impl.UART| (|SWB.MC_SW_dot_Impl|) |SWB.UARTDriver|)
(declare-fun |SWB.MC_SW_dot_Impl.RADIO| (|SWB.MC_SW_dot_Impl|) |SWB.RadioDriver|)
(declare-fun |SWB.MC_SW_dot_Impl.c9| (|SWB.MC_SW_dot_Impl|) |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.Coordinate_dot_Impl>>|)
(declare-fun |SWB.MC_SW_dot_Impl.c5| (|SWB.MC_SW_dot_Impl|) |__unnamed__.iml.connectivity.Connector<iml.ports.DataPort<SWB.Mission_dot_Impl>>|)
(declare-fun |SWB.MC_SW_dot_Impl.c6| (|SWB.MC_SW_dot_Impl|) |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.MissionWindow_dot_Impl>>|)
(declare-fun |SWB.MC_SW_dot_Impl.c7| (|SWB.MC_SW_dot_Impl|) |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.Coordinate_dot_Impl>>|)
(declare-fun |SWB.MC_SW_dot_Impl.WPM| (|SWB.MC_SW_dot_Impl|) |SWB.WaypointManager|)
(declare-fun |SWB.MC_SW_dot_Impl.c8| (|SWB.MC_SW_dot_Impl|) |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.Coordinate_dot_Impl>>|)
(declare-fun |SWB.MC_SW_dot_Impl.c1| (|SWB.MC_SW_dot_Impl|) |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.Command_dot_Impl>>|)
(declare-fun |SWB.MC_SW_dot_Impl.c2| (|SWB.MC_SW_dot_Impl|) |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.Coordinate_dot_Impl>>|)
(declare-fun |SWB.MC_SW_dot_Impl.c3| (|SWB.MC_SW_dot_Impl|) |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.Command_dot_Impl>>|)
(declare-fun |SWB.MC_SW_dot_Impl.FPLN| (|SWB.MC_SW_dot_Impl|) |SWB.FlightPlanner|)
(declare-fun |SWB.FlightPlanner.g1| (|SWB.FlightPlanner|) |Bool|)
(declare-fun |SWB.FlightPlanner.flight_plan| (|SWB.FlightPlanner|) |__unnamed__.iml.ports.DataPort<SWB.Mission_dot_Impl>|)
(declare-fun |SWB.FlightPlanner.recv_map| (|SWB.FlightPlanner|) |__unnamed__.iml.ports.EventDataPort<SWB.Command_dot_Impl>|)
(declare-fun |SWB.FlightPlanner.position_status| (|SWB.FlightPlanner|) |__unnamed__.iml.ports.EventDataPort<SWB.Coordinate_dot_Impl>|)
(declare-fun |SWB.FlightPlanner.a1| (|SWB.FlightPlanner|) |Bool|)
(declare-fun |SWB.FlightPlanner.a2| (|SWB.FlightPlanner|) |Bool|)
(declare-fun |__unnamed__.iml.connectivity.Connector<iml.ports.DataPort<SWB.Mission_dot_Impl>>.target| (|__unnamed__.iml.connectivity.Connector<iml.ports.DataPort<SWB.Mission_dot_Impl>>|) |__unnamed__.iml.ports.DataPort<SWB.Mission_dot_Impl>|)
(declare-fun |__unnamed__.iml.connectivity.Connector<iml.ports.DataPort<SWB.Mission_dot_Impl>>.source| (|__unnamed__.iml.connectivity.Connector<iml.ports.DataPort<SWB.Mission_dot_Impl>>|) |__unnamed__.iml.ports.DataPort<SWB.Mission_dot_Impl>|)
(declare-fun |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.Coordinate_dot_Impl>>.target| (|__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.Coordinate_dot_Impl>>|) |__unnamed__.iml.ports.EventDataPort<SWB.Coordinate_dot_Impl>|)
(declare-fun |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.Coordinate_dot_Impl>>.source| (|__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.Coordinate_dot_Impl>>|) |__unnamed__.iml.ports.EventDataPort<SWB.Coordinate_dot_Impl>|)
(declare-fun |__unnamed__.iml.ports.EventDataPort<SWB.MissionWindow_dot_Impl>.event| (|__unnamed__.iml.ports.EventDataPort<SWB.MissionWindow_dot_Impl>|) |Bool|)
(declare-fun |__unnamed__.iml.ports.EventDataPort<SWB.MissionWindow_dot_Impl>.flowpoint| (|__unnamed__.iml.ports.EventDataPort<SWB.MissionWindow_dot_Impl>|) |iml.ports.FlowPoint|)
(declare-fun |__unnamed__.iml.ports.EventDataPort<SWB.MissionWindow_dot_Impl>.__base_iml.ports.Port| (|__unnamed__.iml.ports.EventDataPort<SWB.MissionWindow_dot_Impl>|) |iml.ports.Port|)
(declare-fun |__unnamed__.iml.ports.EventDataPort<SWB.MissionWindow_dot_Impl>.data| (|__unnamed__.iml.ports.EventDataPort<SWB.MissionWindow_dot_Impl>|) |SWB.MissionWindow_dot_Impl|)
(declare-fun |__unnamed__.iml.ports.DataPort<SWB.Mission_dot_Impl>.__base_iml.ports.Port| (|__unnamed__.iml.ports.DataPort<SWB.Mission_dot_Impl>|) |iml.ports.Port|)
(declare-fun |__unnamed__.iml.ports.DataPort<SWB.Mission_dot_Impl>.data| (|__unnamed__.iml.ports.DataPort<SWB.Mission_dot_Impl>|) |SWB.Mission_dot_Impl|)
(declare-fun |__unnamed__.iml.ports.DataPort<SWB.Mission_dot_Impl>.flowpoint| (|__unnamed__.iml.ports.DataPort<SWB.Mission_dot_Impl>|) |iml.ports.FlowPoint|)
(declare-fun |SWB.UARTDriver.position_status_out| (|SWB.UARTDriver|) |__unnamed__.iml.ports.EventDataPort<SWB.Coordinate_dot_Impl>|)
(declare-fun |SWB.UARTDriver.position_status_in| (|SWB.UARTDriver|) |__unnamed__.iml.ports.EventDataPort<SWB.Coordinate_dot_Impl>|)
(declare-fun |SWB.UARTDriver.a1| (|SWB.UARTDriver|) |Bool|)
(declare-fun |SWB.UARTDriver.waypoint_in| (|SWB.UARTDriver|) |__unnamed__.iml.ports.EventDataPort<SWB.MissionWindow_dot_Impl>|)
(declare-fun |SWB.UARTDriver.waypoint_out| (|SWB.UARTDriver|) |__unnamed__.iml.ports.EventDataPort<SWB.MissionWindow_dot_Impl>|)
(declare-fun |SWB.UARTDriver.g1| (|SWB.UARTDriver|) |Bool|)
(declare-fun |SWB.RadioDriver.send_status_in| (|SWB.RadioDriver|) |__unnamed__.iml.ports.EventDataPort<SWB.Coordinate_dot_Impl>|)
(declare-fun |SWB.RadioDriver.recv_map_out| (|SWB.RadioDriver|) |__unnamed__.iml.ports.EventDataPort<SWB.Command_dot_Impl>|)
(declare-fun |SWB.RadioDriver.recv_map_in| (|SWB.RadioDriver|) |__unnamed__.iml.ports.EventDataPort<SWB.Command_dot_Impl>|)
(declare-fun |SWB.RadioDriver.a1| (|SWB.RadioDriver|) |Bool|)
(declare-fun |SWB.RadioDriver.send_status_out| (|SWB.RadioDriver|) |__unnamed__.iml.ports.EventDataPort<SWB.Coordinate_dot_Impl>|)
(declare-fun |SWB.RadioDriver.g1| (|SWB.RadioDriver|) |Bool|)
(declare-fun |__unnamed__.iml.ports.EventDataPort<SWB.Command_dot_Impl>.event| (|__unnamed__.iml.ports.EventDataPort<SWB.Command_dot_Impl>|) |Bool|)
(declare-fun |__unnamed__.iml.ports.EventDataPort<SWB.Command_dot_Impl>.flowpoint| (|__unnamed__.iml.ports.EventDataPort<SWB.Command_dot_Impl>|) |iml.ports.FlowPoint|)
(declare-fun |__unnamed__.iml.ports.EventDataPort<SWB.Command_dot_Impl>.__base_iml.ports.Port| (|__unnamed__.iml.ports.EventDataPort<SWB.Command_dot_Impl>|) |iml.ports.Port|)
(declare-fun |__unnamed__.iml.ports.EventDataPort<SWB.Command_dot_Impl>.data| (|__unnamed__.iml.ports.EventDataPort<SWB.Command_dot_Impl>|) |SWB.Command_dot_Impl|)
(declare-fun |SWB.WaypointManager.waypoint| (|SWB.WaypointManager|) |__unnamed__.iml.ports.EventDataPort<SWB.MissionWindow_dot_Impl>|)
(declare-fun |SWB.WaypointManager.g1| (|SWB.WaypointManager|) |Bool|)
(declare-fun |SWB.WaypointManager.flight_plan| (|SWB.WaypointManager|) |__unnamed__.iml.ports.DataPort<SWB.Mission_dot_Impl>|)
(declare-fun |SWB.WaypointManager.position_status| (|SWB.WaypointManager|) |__unnamed__.iml.ports.EventDataPort<SWB.Coordinate_dot_Impl>|)
(declare-fun |SWB.WaypointManager.a1| (|SWB.WaypointManager|) |Bool|)
(declare-fun |SWB.MissionWindow_dot_Impl.wp4| (|SWB.MissionWindow_dot_Impl|) |SWB.Coordinate_dot_Impl|)
(declare-fun |SWB.MissionWindow_dot_Impl.crc| (|SWB.MissionWindow_dot_Impl|) |Bool|)
(declare-fun |SWB.MissionWindow_dot_Impl.__base_SWB.MissionWindow| (|SWB.MissionWindow_dot_Impl|) |SWB.MissionWindow|)
(declare-fun |SWB.MissionWindow_dot_Impl.wp3| (|SWB.MissionWindow_dot_Impl|) |SWB.Coordinate_dot_Impl|)
(declare-fun |SWB.MissionWindow_dot_Impl.wp2| (|SWB.MissionWindow_dot_Impl|) |SWB.Coordinate_dot_Impl|)
(declare-fun |SWB.MissionWindow_dot_Impl.wp1| (|SWB.MissionWindow_dot_Impl|) |SWB.Coordinate_dot_Impl|)
(declare-fun |SWB.MC_SW.position_status| (|SWB.MC_SW|) |__unnamed__.iml.ports.EventDataPort<SWB.Coordinate_dot_Impl>|)
(declare-fun |SWB.MC_SW.recv_map| (|SWB.MC_SW|) |__unnamed__.iml.ports.EventDataPort<SWB.Command_dot_Impl>|)
(declare-fun |SWB.MC_SW.send_status| (|SWB.MC_SW|) |__unnamed__.iml.ports.EventDataPort<SWB.Coordinate_dot_Impl>|)
(declare-fun |SWB.MC_SW.g1| (|SWB.MC_SW|) |Bool|)
(declare-fun |SWB.MC_SW.a1| (|SWB.MC_SW|) |Bool|)
(declare-fun |SWB.MC_SW.waypoint| (|SWB.MC_SW|) |__unnamed__.iml.ports.EventDataPort<SWB.MissionWindow_dot_Impl>|)
(declare-fun |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.MissionWindow_dot_Impl>>.target| (|__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.MissionWindow_dot_Impl>>|) |__unnamed__.iml.ports.EventDataPort<SWB.MissionWindow_dot_Impl>|)
(declare-fun |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.MissionWindow_dot_Impl>>.source| (|__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.MissionWindow_dot_Impl>>|) |__unnamed__.iml.ports.EventDataPort<SWB.MissionWindow_dot_Impl>|)
(declare-fun |SWB.Mission_dot_Impl.wp10| (|SWB.Mission_dot_Impl|) |SWB.Coordinate_dot_Impl|)
(declare-fun |SWB.Mission_dot_Impl.wp1| (|SWB.Mission_dot_Impl|) |SWB.Coordinate_dot_Impl|)
(declare-fun |SWB.Mission_dot_Impl.wp3| (|SWB.Mission_dot_Impl|) |SWB.Coordinate_dot_Impl|)
(declare-fun |SWB.Mission_dot_Impl.wp2| (|SWB.Mission_dot_Impl|) |SWB.Coordinate_dot_Impl|)
(declare-fun |SWB.Mission_dot_Impl.wp5| (|SWB.Mission_dot_Impl|) |SWB.Coordinate_dot_Impl|)
(declare-fun |SWB.Mission_dot_Impl.wp4| (|SWB.Mission_dot_Impl|) |SWB.Coordinate_dot_Impl|)
(declare-fun |SWB.Mission_dot_Impl.wp7| (|SWB.Mission_dot_Impl|) |SWB.Coordinate_dot_Impl|)
(declare-fun |SWB.Mission_dot_Impl.wp6| (|SWB.Mission_dot_Impl|) |SWB.Coordinate_dot_Impl|)
(declare-fun |SWB.Mission_dot_Impl.__base_SWB.Mission| (|SWB.Mission_dot_Impl|) |SWB.Mission|)
(declare-fun |SWB.Mission_dot_Impl.wp9| (|SWB.Mission_dot_Impl|) |SWB.Coordinate_dot_Impl|)
(declare-fun |SWB.Mission_dot_Impl.wp8| (|SWB.Mission_dot_Impl|) |SWB.Coordinate_dot_Impl|)
(declare-fun |iml.ports.FlowPoint.event| (|iml.ports.FlowPoint|) |Bool|)
(declare-fun |iml.ports.FlowPoint.upperBound| (|iml.ports.FlowPoint|) |Real|)
(declare-fun |iml.ports.FlowPoint.lowerBound| (|iml.ports.FlowPoint|) |Real|)
(declare-fun |__unnamed__.iml.ports.EventDataPort<SWB.Coordinate_dot_Impl>.event| (|__unnamed__.iml.ports.EventDataPort<SWB.Coordinate_dot_Impl>|) |Bool|)
(declare-fun |__unnamed__.iml.ports.EventDataPort<SWB.Coordinate_dot_Impl>.flowpoint| (|__unnamed__.iml.ports.EventDataPort<SWB.Coordinate_dot_Impl>|) |iml.ports.FlowPoint|)
(declare-fun |__unnamed__.iml.ports.EventDataPort<SWB.Coordinate_dot_Impl>.__base_iml.ports.Port| (|__unnamed__.iml.ports.EventDataPort<SWB.Coordinate_dot_Impl>|) |iml.ports.Port|)
(declare-fun |__unnamed__.iml.ports.EventDataPort<SWB.Coordinate_dot_Impl>.data| (|__unnamed__.iml.ports.EventDataPort<SWB.Coordinate_dot_Impl>|) |SWB.Coordinate_dot_Impl|)
(declare-fun |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.Command_dot_Impl>>.target| (|__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.Command_dot_Impl>>|) |__unnamed__.iml.ports.EventDataPort<SWB.Command_dot_Impl>|)
(declare-fun |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.Command_dot_Impl>>.source| (|__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.Command_dot_Impl>>|) |__unnamed__.iml.ports.EventDataPort<SWB.Command_dot_Impl>|)
(declare-fun |SWB.Command_dot_Impl.Map| (|SWB.Command_dot_Impl|) |SWB.Map_dot_Impl|)
(declare-fun |SWB.Command_dot_Impl.Pattern| (|SWB.Command_dot_Impl|) |SWB.FlightPattern|)
(declare-fun |SWB.Command_dot_Impl.HMAC| (|SWB.Command_dot_Impl|) |Bool|)
(declare-fun |SWB.Command_dot_Impl.__base_SWB.Command| (|SWB.Command_dot_Impl|) |SWB.Command|)
(declare-const |SWB.inst|  |SWB.MC_SW_dot_Impl|)
(declare-fun |SWB.good_gs_command| (|SWB.Command_dot_Impl|) |Bool|)
(declare-fun |SWB.good_map| (|SWB.Map_dot_Impl|) |Bool|)
(declare-fun |SWB.good_mission| (|SWB.Mission_dot_Impl|) |Bool|)
(declare-fun |SWB.good_coordinate| (|SWB.Coordinate_dot_Impl|) |Bool|)
(declare-fun |SWB.good_HMAC| (|Bool|) |Bool|)
(declare-fun |SWB.good_mission_window| (|SWB.MissionWindow_dot_Impl|) |Bool|)
(declare-fun |SWB.Coordinate_dot_Impl.alt| (|SWB.Coordinate_dot_Impl|) |Int|)
(declare-fun |SWB.Coordinate_dot_Impl.long| (|SWB.Coordinate_dot_Impl|) |Int|)
(declare-fun |SWB.Coordinate_dot_Impl.__base_SWB.Coordinate| (|SWB.Coordinate_dot_Impl|) |SWB.Coordinate|)
(declare-fun |SWB.Coordinate_dot_Impl.lat| (|SWB.Coordinate_dot_Impl|) |Int|)
(assert (forall ((__inst__ |SWB.MC_SW_dot_Impl|)) (= (|SWB.UARTDriver.position_status_out| (|SWB.MC_SW_dot_Impl.UART| __inst__)) (|SWB.RadioDriver.send_status_in| (|SWB.MC_SW_dot_Impl.RADIO| __inst__)))))
(assert (forall ((__inst__ |SWB.MC_SW_dot_Impl|)) (= (|SWB.FlightPlanner.flight_plan| (|SWB.MC_SW_dot_Impl.FPLN| __inst__)) (|SWB.WaypointManager.flight_plan| (|SWB.MC_SW_dot_Impl.WPM| __inst__)))))
(assert (forall ((__inst__ |SWB.MC_SW_dot_Impl|)) (= (|SWB.MC_SW.position_status| (|SWB.MC_SW_dot_Impl.__base_SWB.MC_SW| __inst__)) (|SWB.UARTDriver.position_status_in| (|SWB.MC_SW_dot_Impl.UART| __inst__)))))
(assert (forall ((__inst__ |SWB.MC_SW_dot_Impl|)) (= (|SWB.WaypointManager.waypoint| (|SWB.MC_SW_dot_Impl.WPM| __inst__)) (|SWB.UARTDriver.waypoint_in| (|SWB.MC_SW_dot_Impl.UART| __inst__)))))
(assert (forall ((__inst__ |SWB.MC_SW_dot_Impl|)) (= (|SWB.UARTDriver.waypoint_out| (|SWB.MC_SW_dot_Impl.UART| __inst__)) (|SWB.MC_SW.waypoint| (|SWB.MC_SW_dot_Impl.__base_SWB.MC_SW| __inst__)))))
(assert (forall ((__inst__ |SWB.MC_SW_dot_Impl|)) (= (|SWB.UARTDriver.position_status_out| (|SWB.MC_SW_dot_Impl.UART| __inst__)) (|SWB.WaypointManager.position_status| (|SWB.MC_SW_dot_Impl.WPM| __inst__)))))
(assert (forall ((__inst__ |SWB.MC_SW_dot_Impl|)) (= (|SWB.UARTDriver.position_status_out| (|SWB.MC_SW_dot_Impl.UART| __inst__)) (|SWB.FlightPlanner.position_status| (|SWB.MC_SW_dot_Impl.FPLN| __inst__)))))
(assert (forall ((__inst__ |SWB.MC_SW_dot_Impl|)) (= (|SWB.MC_SW.recv_map| (|SWB.MC_SW_dot_Impl.__base_SWB.MC_SW| __inst__)) (|SWB.RadioDriver.recv_map_in| (|SWB.MC_SW_dot_Impl.RADIO| __inst__)))))
(assert (forall ((__inst__ |SWB.MC_SW_dot_Impl|)) (= (|SWB.RadioDriver.send_status_out| (|SWB.MC_SW_dot_Impl.RADIO| __inst__)) (|SWB.MC_SW.send_status| (|SWB.MC_SW_dot_Impl.__base_SWB.MC_SW| __inst__)))))
(assert (forall ((__inst__ |SWB.MC_SW_dot_Impl|)) (= (|SWB.RadioDriver.recv_map_out| (|SWB.MC_SW_dot_Impl.RADIO| __inst__)) (|SWB.FlightPlanner.recv_map| (|SWB.MC_SW_dot_Impl.FPLN| __inst__)))))
(assert (forall ((__inst__ |SWB.FlightPlanner|)) (= (|SWB.FlightPlanner.g1| __inst__) (|SWB.good_mission| (|__unnamed__.iml.ports.DataPort<SWB.Mission_dot_Impl>.data| (|SWB.FlightPlanner.flight_plan| __inst__))))))
(assert (forall ((__inst__ |SWB.FlightPlanner|)) (= (|SWB.FlightPlanner.a1| __inst__) (= (|SWB.Command_dot_Impl.HMAC| (|__unnamed__.iml.ports.EventDataPort<SWB.Command_dot_Impl>.data| (|SWB.FlightPlanner.recv_map| __inst__))) true))))
(assert (forall ((__inst__ |SWB.FlightPlanner|)) (= (|SWB.FlightPlanner.a2| __inst__) (|SWB.good_gs_command| (|__unnamed__.iml.ports.EventDataPort<SWB.Command_dot_Impl>.data| (|SWB.FlightPlanner.recv_map| __inst__))))))
(assert (forall ((__inst__ |SWB.WaypointManager|)) (= (|SWB.WaypointManager.g1| __inst__) (|SWB.good_mission_window| (|__unnamed__.iml.ports.EventDataPort<SWB.MissionWindow_dot_Impl>.data| (|SWB.WaypointManager.waypoint| __inst__))))))
(assert (forall ((__inst__ |SWB.WaypointManager|)) (= (|SWB.WaypointManager.a1| __inst__) (|SWB.good_mission| (|__unnamed__.iml.ports.DataPort<SWB.Mission_dot_Impl>.data| (|SWB.WaypointManager.flight_plan| __inst__))))))
(assert (forall ((__inst__ |SWB.MC_SW|)) (= (|SWB.MC_SW.g1| __inst__) (= (|SWB.MissionWindow_dot_Impl.crc| (|__unnamed__.iml.ports.EventDataPort<SWB.MissionWindow_dot_Impl>.data| (|SWB.MC_SW.waypoint| __inst__))) true))))
(assert (forall ((__inst__ |SWB.MC_SW|)) (= (|SWB.MC_SW.a1| __inst__) (= (|SWB.Command_dot_Impl.HMAC| (|__unnamed__.iml.ports.EventDataPort<SWB.Command_dot_Impl>.data| (|SWB.MC_SW.recv_map| __inst__))) true))))
(assert (forall ((__inst__ |__unnamed__.iml.connectivity.Connector<iml.ports.DataPort<SWB.Mission_dot_Impl>>|)) (= (|__unnamed__.iml.connectivity.Connector<iml.ports.DataPort<SWB.Mission_dot_Impl>>.source| __inst__) (|__unnamed__.iml.connectivity.Connector<iml.ports.DataPort<SWB.Mission_dot_Impl>>.target| __inst__))))
(assert (forall ((__inst__ |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.MissionWindow_dot_Impl>>|)) (= (|__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.MissionWindow_dot_Impl>>.source| __inst__) (|__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.MissionWindow_dot_Impl>>.target| __inst__))))
(assert (forall ((__inst__ |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.Coordinate_dot_Impl>>|)) (= (|__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.Coordinate_dot_Impl>>.source| __inst__) (|__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.Coordinate_dot_Impl>>.target| __inst__))))
(assert (forall ((__inst__ |__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.Command_dot_Impl>>|)) (= (|__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.Command_dot_Impl>>.source| __inst__) (|__unnamed__.iml.connectivity.Connector<iml.ports.EventDataPort<SWB.Command_dot_Impl>>.target| __inst__))))
(assert (forall ((__inst__ |SWB.UARTDriver|)) (= (|SWB.UARTDriver.a1| __inst__) (|SWB.good_mission_window| (|__unnamed__.iml.ports.EventDataPort<SWB.MissionWindow_dot_Impl>.data| (|SWB.UARTDriver.waypoint_in| __inst__))))))
(assert (forall ((__inst__ |SWB.UARTDriver|)) (= (|SWB.UARTDriver.g1| __inst__) (= (|SWB.MissionWindow_dot_Impl.crc| (|__unnamed__.iml.ports.EventDataPort<SWB.MissionWindow_dot_Impl>.data| (|SWB.UARTDriver.waypoint_out| __inst__))) true))))
(assert (forall ((map |SWB.Map_dot_Impl|)) (= (|SWB.good_map| map) (and (and (and (|SWB.good_coordinate| (|SWB.Map_dot_Impl.wp1| map)) (|SWB.good_coordinate| (|SWB.Map_dot_Impl.wp2| map))) (|SWB.good_coordinate| (|SWB.Map_dot_Impl.wp3| map))) (|SWB.good_coordinate| (|SWB.Map_dot_Impl.wp4| map))))))
(assert (forall ((cmd |SWB.Command_dot_Impl|)) (= (|SWB.good_gs_command| cmd) (and (|SWB.good_map| (|SWB.Command_dot_Impl.Map| cmd)) (|SWB.good_HMAC| (|SWB.Command_dot_Impl.HMAC| cmd))))))
(assert (forall ((mission |SWB.Mission_dot_Impl|)) (= (|SWB.good_mission| mission) (and (and (and (and (and (and (and (and (and (|SWB.good_coordinate| (|SWB.Mission_dot_Impl.wp1| mission)) (|SWB.good_coordinate| (|SWB.Mission_dot_Impl.wp2| mission))) (|SWB.good_coordinate| (|SWB.Mission_dot_Impl.wp3| mission))) (|SWB.good_coordinate| (|SWB.Mission_dot_Impl.wp4| mission))) (|SWB.good_coordinate| (|SWB.Mission_dot_Impl.wp5| mission))) (|SWB.good_coordinate| (|SWB.Mission_dot_Impl.wp6| mission))) (|SWB.good_coordinate| (|SWB.Mission_dot_Impl.wp7| mission))) (|SWB.good_coordinate| (|SWB.Mission_dot_Impl.wp8| mission))) (|SWB.good_coordinate| (|SWB.Mission_dot_Impl.wp9| mission))) (|SWB.good_coordinate| (|SWB.Mission_dot_Impl.wp10| mission))))))
(assert (forall ((coord |SWB.Coordinate_dot_Impl|)) (= (|SWB.good_coordinate| coord) (and (and (and (and (and (>= (|SWB.Coordinate_dot_Impl.lat| coord) (- 90)) (<= (|SWB.Coordinate_dot_Impl.lat| coord) 90)) (>= (|SWB.Coordinate_dot_Impl.long| coord) (- 180))) (<= (|SWB.Coordinate_dot_Impl.long| coord) 180)) (>= (|SWB.Coordinate_dot_Impl.alt| coord) 0)) (<= (|SWB.Coordinate_dot_Impl.alt| coord) 15000)))))
(assert (forall ((hmac |Bool|)) (= (|SWB.good_HMAC| hmac) (or (= hmac true) (= hmac false)))))
(assert (forall ((win |SWB.MissionWindow_dot_Impl|)) (= (|SWB.good_mission_window| win) (and (and (and (|SWB.good_coordinate| (|SWB.MissionWindow_dot_Impl.wp1| win)) (|SWB.good_coordinate| (|SWB.MissionWindow_dot_Impl.wp2| win))) (|SWB.good_coordinate| (|SWB.MissionWindow_dot_Impl.wp3| win))) (|SWB.good_coordinate| (|SWB.MissionWindow_dot_Impl.wp4| win))))))
(assert (forall ((__inst__ |SWB.RadioDriver|)) (= (|SWB.RadioDriver.a1| __inst__) (= (|SWB.Command_dot_Impl.HMAC| (|__unnamed__.iml.ports.EventDataPort<SWB.Command_dot_Impl>.data| (|SWB.RadioDriver.recv_map_in| __inst__))) true))))
(assert (forall ((__inst__ |SWB.RadioDriver|)) (= (|SWB.RadioDriver.g1| __inst__) (= (|SWB.Command_dot_Impl.HMAC| (|__unnamed__.iml.ports.EventDataPort<SWB.Command_dot_Impl>.data| (|SWB.RadioDriver.recv_map_out| __inst__))) true))))
 
;edge E_17 from __ to N_4.kb
(assert (and (and (and (|SWB.MC_SW.a1| (|SWB.MC_SW_dot_Impl.__base_SWB.MC_SW| |SWB.inst|)) (|SWB.RadioDriver.g1| (|SWB.MC_SW_dot_Impl.RADIO| |SWB.inst|))) (|SWB.WaypointManager.g1| (|SWB.MC_SW_dot_Impl.WPM| |SWB.inst|))) (|SWB.UARTDriver.g1| (|SWB.MC_SW_dot_Impl.UART| |SWB.inst|))))

;edge E_18 from __ to N_4.g
(assert (not (|SWB.FlightPlanner.a2| (|SWB.MC_SW_dot_Impl.FPLN| |SWB.inst|))))

(check-sat)