---------------------------- MODULE lock_single ----------------------------

EXTENDS lock_data


(* --algorithm lock_system

\*****************************
\* Define global variables
\*****************************
variables
  \* Variables for locks
  lockOrientation = "west_low",
  doorsOpen = [ls \in LockSide |-> FALSE],
  valvesOpen = [vs \in ValveSide |-> FALSE],
  waterLevel = "low",
  
  \* Variables for single ship
  shipLocation = 0,
  shipStatus = "go_to_east",
  
  \* Command for lock
  \* for command "change_door" the side should be "west" or "east"
  \* for command "change_valve" the side should be "high" or "low"
  lockCommand = [command |-> "finished", open |-> FALSE, side |-> "west"],
  \* Central requests of all ships
  requests = << >>,
  \* Permissions per ship
  permissions = << >>;

define

\*****************************
\* Helper functions
\*****************************
\* Check if ship is within the lock
InLock == IsLock(shipLocation)




\*****************************
\* Type checks
\*****************************
\* Check that variables use the correct type
TypeOK == /\ lockOrientation \in LockOrientation
          /\ \A ls \in LockSide : doorsOpen[ls] \in BOOLEAN
          /\ \A vs \in ValveSide : valvesOpen[vs] \in BOOLEAN
          /\ waterLevel \in WaterLevel
          /\ lockCommand.command \in LockCommand
          /\ lockCommand.open \in BOOLEAN
          /\ lockCommand.side \in LockSide \union ValveSide
          /\ shipLocation \in Locations
          /\ shipStatus \in ShipStatus
          /\ \A i \in 1..Len(permissions):
               /\ permissions[i].lock \in Locks
               /\ permissions[i].granted \in BOOLEAN
          /\ \A i \in 1..Len(requests):
               /\ requests[i].ship \in Ships
               /\ requests[i].lock \in Locks
               /\ requests[i].side \in LockSide

\* Check that message queues are not overflowing
MessagesOK == /\ Len(requests) <= 1
              /\ Len(permissions) <= 1


\*****************************
\* Requirements on lock
\*****************************
\* The eastern pair of doors and the western pair of doors are never simultaneously open
DoorsMutex == ~(doorsOpen["west"] /\ doorsOpen["east"])
\* When the lower/higher pair of doors is open, the higher/lower valve is closed.
DoorsOpenValvesClosed == /\ (doorsOpen[LowSide(lockOrientation)]  => ~valvesOpen["high"])
  /\ (doorsOpen[HighSide(lockOrientation)] => ~valvesOpen["low"])
\* The lower/higher pair of doors is only open when the water level in the lock is low/high
DoorsOpenWaterlevelRight  ==  /\ (doorsOpen[LowSide(lockOrientation)]  => waterLevel = "low")
  /\ (doorsOpen[HighSide(lockOrientation)] => waterLevel = "high")
\* Always if the ship requests to enter the lock, the ship will eventually be inside the lock.
RequestLockFulfilled == []( (\E i \in 1..Len(requests) :
         requests[i].ship \in Ships /\ requests[i].lock \in Locks /\ requests[i].side \in LockSide) => <> InLock )
\* Water level is infinitely many times high/low
WaterlevelChange ==  ([]<>(waterLevel = "high")) /\ ([]<>(waterLevel = "low"))
\* Infinitely many times the ship does requests
RequestsShips == []<>( \E i \in 1..Len(requests) : TRUE )
\* Infinitely many times the ship reaches its end location
ShipsReachGoals == []<>( (shipLocation = WestEnd) \/ (shipLocation = EastEnd) )

end define;


\*****************************
\* Helper macros
\*****************************

\* Update the water level according to the state of doors and valves
macro updateWaterLevel(lock_orientation, doors, valves, waterlevel) begin
  if valves["low"] then
      \* Water can flow out through valve
      waterlevel := "low";
  elsif (lock_orientation = "west_low" /\ doors["west"])
         \/ (lock_orientation = "east_low" /\ doors["east"]) then
      \* Water can flow out through lower door
      waterlevel := "low";
  elsif valves["high"] then
      \* Water can flow in through valve
      waterlevel := "high";
  elsif (lock_orientation = "west_low" /\ doors["east"])
         \/ (lock_orientation = "east_low" /\ doors["west"]) then
      \* Water can flow in through higher door
      waterlevel := "high";
  \* In other case, the water level stays the same
  end if;
end macro

\* Read res from queue.
\* The macro awaits a non-empty queue.
macro read(queue, res) begin
  await queue /= <<>>;
  res := Head(queue);
  queue := Tail(queue);
end macro

\* Write msg to the queue.
macro write(queue, msg) begin
  queue := Append(queue, msg);
end macro
    


\*****************************
\* Process for a lock
\*****************************
fair process lockProcess \in Locks
begin
  LockWaitForCommand:
    while TRUE do
      await lockCommand.command /= "finished";
      if lockCommand.command = "change_door" then
        \* Change status of door
        doorsOpen[lockCommand.side] := lockCommand.open;
      elsif lockCommand.command = "change_valve" then
        \* Change status of valve
        valvesOpen[lockCommand.side] := lockCommand.open;
      else
        \* should not happen
        assert FALSE;
      end if;
  LockUpdateWaterLevel:
      updateWaterLevel(lockOrientation, doorsOpen, valvesOpen, waterLevel);
  LockCommandFinished:
      lockCommand.command := "finished";    
    end while;
end process;


\*****************************
\* Process for a ship
\*****************************
fair process shipProcess \in Ships
variables
  perm = [lock |-> 1, granted |-> FALSE]
begin
  ShipNextIteration:
    while TRUE do
      if shipStatus = "go_to_east" then
        if shipLocation = EastEnd then
  ShipGoalReachedEast:
          shipStatus := "goal_reached";
        else
          if ~InLock then
  ShipRequestWest:
            \* Request west doors of lock
            write(requests, [ship |-> self, lock |-> 1, side |-> "west"]);
  ShipWaitForWest:
            \* Wait for permission
            read(permissions, perm);
            assert perm.lock = GetLock(shipLocation+1);
          else
  ShipRequestEastInLock:
            \* Request east doors of lock
            write(requests, [ship |-> self, lock |-> 1, side |-> "east"]);
  ShipWaitForEastInLock:
            \* Wait for permission
            read(permissions, perm);
            assert perm.lock = GetLock(shipLocation);
          end if;
  ShipMoveEast:
          if perm.granted then
            \* Move ship
            assert doorsOpen[IF InLock THEN "east" ELSE "west"];
            shipLocation := shipLocation + 1;
          end if;
        end if;
      elsif shipStatus = "go_to_west" then
        if shipLocation = WestEnd then
  ShipGoalReachedWest:
          shipStatus := "goal_reached";
        else
          if ~InLock then
  ShipRequestEast:
            \* Request east doors of lock
            write(requests, [ship |-> self, lock |-> 1, side |-> "east"]);
  ShipWaitForEast:
            \* Wait for permission
            read(permissions, perm);
            assert perm.lock = GetLock(shipLocation-1);
          else
  ShipRequestWestInLock:
            \* Request west doors of lock
            write(requests, [ship |-> self, lock |-> 1, side |-> "west"]);
  ShipWaitForWestInLock:
            \* Wait for permission
            read(permissions, perm);
            assert perm.lock = GetLock(shipLocation);
          end if;
  ShipMoveWest:
          if perm.granted then
            \* Move ship
            assert doorsOpen[IF InLock THEN "west" ELSE "east"];
            shipLocation := shipLocation - 1;
          end if;
        end if;
      else
        assert shipStatus = "goal_reached";
  ShipTurnAround:
        \* Turn around
        shipStatus := IF shipLocation = WestEnd THEN "go_to_east" ELSE "go_to_west";
      end if;
    end while;
end process;


\*****************************
\* Process for the controller
\*****************************
fair process controlProcess = 0

variables
req = [ship |-> 2, lock |-> 1, side |-> "west"];
oldLocation = -200;
  
begin
  ControlStart:
    \* Implement behaviour
    \* Four wait permissions: Ship wait for west, ship wait for east in lock,Ship wait for east, Ship wait for West in lock
    \* First Ship wait for west
    while TRUE do
        await lockCommand.command = "finished";
        oldLocation := shipLocation;
        read(requests, req);
        
    OpenValve:
        lockCommand := [command |-> "change_valve", open |-> TRUE, side |-> getValveSide(lockOrientation, req.side)];
        
    CloseValve:
        await lockCommand.command = "finished";
        lockCommand := [command |-> "change_valve", open |-> TRUE, side |-> getValveSide(lockOrientation, req.side)];
        
    OpenDoor:
        await lockCommand.command = "finished";
        lockCommand := [command |-> "change_door", open |-> TRUE, side |-> req.side];
        
    GivePermission:
        await lockCommand.command = "finished";
        write(permissions, [lock |-> 1, granted |-> TRUE]);
        
    WaitForShipToPassAndCloseDoor:
        await shipLocation # oldLocation;
        lockCommand := [command |-> "change_door", open |-> FALSE, side |-> req.side];
    WaitCloseDoor:
        await lockCommand.command = "finished";

    end while;
end process;


end algorithm; *)


\* BEGIN TRANSLATION (chksum(pcal) = "1453a788" /\ chksum(tla) = "9c6dd1b5")
VARIABLES pc, lockOrientation, doorsOpen, valvesOpen, waterLevel, 
          shipLocation, shipStatus, lockCommand, requests, permissions

(* define statement *)
InLock == IsLock(shipLocation)








TypeOK == /\ lockOrientation \in LockOrientation
          /\ \A ls \in LockSide : doorsOpen[ls] \in BOOLEAN
          /\ \A vs \in ValveSide : valvesOpen[vs] \in BOOLEAN
          /\ waterLevel \in WaterLevel
          /\ lockCommand.command \in LockCommand
          /\ lockCommand.open \in BOOLEAN
          /\ lockCommand.side \in LockSide \union ValveSide
          /\ shipLocation \in Locations
          /\ shipStatus \in ShipStatus
          /\ \A i \in 1..Len(permissions):
               /\ permissions[i].lock \in Locks
               /\ permissions[i].granted \in BOOLEAN
          /\ \A i \in 1..Len(requests):
               /\ requests[i].ship \in Ships
               /\ requests[i].lock \in Locks
               /\ requests[i].side \in LockSide


MessagesOK == /\ Len(requests) <= 1
              /\ Len(permissions) <= 1






DoorsMutex == ~(doorsOpen["west"] /\ doorsOpen["east"])

DoorsOpenValvesClosed == /\ (doorsOpen[LowSide(lockOrientation)]  => ~valvesOpen["high"])
  /\ (doorsOpen[HighSide(lockOrientation)] => ~valvesOpen["low"])

DoorsOpenWaterlevelRight  ==  /\ (doorsOpen[LowSide(lockOrientation)]  => waterLevel = "low")
  /\ (doorsOpen[HighSide(lockOrientation)] => waterLevel = "high")

RequestLockFulfilled == []( (\E i \in 1..Len(requests) :
         requests[i].ship \in Ships /\ requests[i].lock \in Locks /\ requests[i].side \in LockSide) => <> InLock )

WaterlevelChange ==  ([]<>(waterLevel = "high")) /\ ([]<>(waterLevel = "low"))

RequestsShips == []<>( \E i \in 1..Len(requests) : TRUE )

ShipsReachGoals == []<>( (shipLocation = WestEnd) \/ (shipLocation = EastEnd) )

VARIABLES perm, req, oldLocation

vars == << pc, lockOrientation, doorsOpen, valvesOpen, waterLevel, 
           shipLocation, shipStatus, lockCommand, requests, permissions, perm, 
           req, oldLocation >>

ProcSet == (Locks) \cup (Ships) \cup {0}

Init == (* Global variables *)
        /\ lockOrientation = "west_low"
        /\ doorsOpen = [ls \in LockSide |-> FALSE]
        /\ valvesOpen = [vs \in ValveSide |-> FALSE]
        /\ waterLevel = "low"
        /\ shipLocation = 0
        /\ shipStatus = "go_to_east"
        /\ lockCommand = [command |-> "finished", open |-> FALSE, side |-> "west"]
        /\ requests = << >>
        /\ permissions = << >>
        (* Process shipProcess *)
        /\ perm = [self \in Ships |-> [lock |-> 1, granted |-> FALSE]]
        (* Process controlProcess *)
        /\ req = [ship |-> 2, lock |-> 1, side |-> "west"]
        /\ oldLocation = -200
        /\ pc = [self \in ProcSet |-> CASE self \in Locks -> "LockWaitForCommand"
                                        [] self \in Ships -> "ShipNextIteration"
                                        [] self = 0 -> "ControlStart"]

LockWaitForCommand(self) == /\ pc[self] = "LockWaitForCommand"
                            /\ lockCommand.command /= "finished"
                            /\ IF lockCommand.command = "change_door"
                                  THEN /\ doorsOpen' = [doorsOpen EXCEPT ![lockCommand.side] = lockCommand.open]
                                       /\ UNCHANGED valvesOpen
                                  ELSE /\ IF lockCommand.command = "change_valve"
                                             THEN /\ valvesOpen' = [valvesOpen EXCEPT ![lockCommand.side] = lockCommand.open]
                                             ELSE /\ Assert(FALSE, 
                                                            "Failure of assertion at line 147, column 9.")
                                                  /\ UNCHANGED valvesOpen
                                       /\ UNCHANGED doorsOpen
                            /\ pc' = [pc EXCEPT ![self] = "LockUpdateWaterLevel"]
                            /\ UNCHANGED << lockOrientation, waterLevel, 
                                            shipLocation, shipStatus, 
                                            lockCommand, requests, permissions, 
                                            perm, req, oldLocation >>

LockUpdateWaterLevel(self) == /\ pc[self] = "LockUpdateWaterLevel"
                              /\ IF valvesOpen["low"]
                                    THEN /\ waterLevel' = "low"
                                    ELSE /\ IF (lockOrientation = "west_low" /\ doorsOpen["west"])
                                                \/ (lockOrientation = "east_low" /\ doorsOpen["east"])
                                               THEN /\ waterLevel' = "low"
                                               ELSE /\ IF valvesOpen["high"]
                                                          THEN /\ waterLevel' = "high"
                                                          ELSE /\ IF (lockOrientation = "west_low" /\ doorsOpen["east"])
                                                                      \/ (lockOrientation = "east_low" /\ doorsOpen["west"])
                                                                     THEN /\ waterLevel' = "high"
                                                                     ELSE /\ TRUE
                                                                          /\ UNCHANGED waterLevel
                              /\ pc' = [pc EXCEPT ![self] = "LockCommandFinished"]
                              /\ UNCHANGED << lockOrientation, doorsOpen, 
                                              valvesOpen, shipLocation, 
                                              shipStatus, lockCommand, 
                                              requests, permissions, perm, req, 
                                              oldLocation >>

LockCommandFinished(self) == /\ pc[self] = "LockCommandFinished"
                             /\ lockCommand' = [lockCommand EXCEPT !.command = "finished"]
                             /\ pc' = [pc EXCEPT ![self] = "LockWaitForCommand"]
                             /\ UNCHANGED << lockOrientation, doorsOpen, 
                                             valvesOpen, waterLevel, 
                                             shipLocation, shipStatus, 
                                             requests, permissions, perm, req, 
                                             oldLocation >>

lockProcess(self) == LockWaitForCommand(self) \/ LockUpdateWaterLevel(self)
                        \/ LockCommandFinished(self)

ShipNextIteration(self) == /\ pc[self] = "ShipNextIteration"
                           /\ IF shipStatus = "go_to_east"
                                 THEN /\ IF shipLocation = EastEnd
                                            THEN /\ pc' = [pc EXCEPT ![self] = "ShipGoalReachedEast"]
                                            ELSE /\ IF ~InLock
                                                       THEN /\ pc' = [pc EXCEPT ![self] = "ShipRequestWest"]
                                                       ELSE /\ pc' = [pc EXCEPT ![self] = "ShipRequestEastInLock"]
                                 ELSE /\ IF shipStatus = "go_to_west"
                                            THEN /\ IF shipLocation = WestEnd
                                                       THEN /\ pc' = [pc EXCEPT ![self] = "ShipGoalReachedWest"]
                                                       ELSE /\ IF ~InLock
                                                                  THEN /\ pc' = [pc EXCEPT ![self] = "ShipRequestEast"]
                                                                  ELSE /\ pc' = [pc EXCEPT ![self] = "ShipRequestWestInLock"]
                                            ELSE /\ Assert(shipStatus = "goal_reached", 
                                                           "Failure of assertion at line 225, column 9.")
                                                 /\ pc' = [pc EXCEPT ![self] = "ShipTurnAround"]
                           /\ UNCHANGED << lockOrientation, doorsOpen, 
                                           valvesOpen, waterLevel, 
                                           shipLocation, shipStatus, 
                                           lockCommand, requests, permissions, 
                                           perm, req, oldLocation >>

ShipGoalReachedEast(self) == /\ pc[self] = "ShipGoalReachedEast"
                             /\ shipStatus' = "goal_reached"
                             /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                             /\ UNCHANGED << lockOrientation, doorsOpen, 
                                             valvesOpen, waterLevel, 
                                             shipLocation, lockCommand, 
                                             requests, permissions, perm, req, 
                                             oldLocation >>

ShipMoveEast(self) == /\ pc[self] = "ShipMoveEast"
                      /\ IF perm[self].granted
                            THEN /\ Assert(doorsOpen[IF InLock THEN "east" ELSE "west"], 
                                           "Failure of assertion at line 191, column 13.")
                                 /\ shipLocation' = shipLocation + 1
                            ELSE /\ TRUE
                                 /\ UNCHANGED shipLocation
                      /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                      /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                      waterLevel, shipStatus, lockCommand, 
                                      requests, permissions, perm, req, 
                                      oldLocation >>

ShipRequestWest(self) == /\ pc[self] = "ShipRequestWest"
                         /\ requests' = Append(requests, ([ship |-> self, lock |-> 1, side |-> "west"]))
                         /\ pc' = [pc EXCEPT ![self] = "ShipWaitForWest"]
                         /\ UNCHANGED << lockOrientation, doorsOpen, 
                                         valvesOpen, waterLevel, shipLocation, 
                                         shipStatus, lockCommand, permissions, 
                                         perm, req, oldLocation >>

ShipWaitForWest(self) == /\ pc[self] = "ShipWaitForWest"
                         /\ permissions /= <<>>
                         /\ perm' = [perm EXCEPT ![self] = Head(permissions)]
                         /\ permissions' = Tail(permissions)
                         /\ Assert(perm'[self].lock = GetLock(shipLocation+1), 
                                   "Failure of assertion at line 178, column 13.")
                         /\ pc' = [pc EXCEPT ![self] = "ShipMoveEast"]
                         /\ UNCHANGED << lockOrientation, doorsOpen, 
                                         valvesOpen, waterLevel, shipLocation, 
                                         shipStatus, lockCommand, requests, 
                                         req, oldLocation >>

ShipRequestEastInLock(self) == /\ pc[self] = "ShipRequestEastInLock"
                               /\ requests' = Append(requests, ([ship |-> self, lock |-> 1, side |-> "east"]))
                               /\ pc' = [pc EXCEPT ![self] = "ShipWaitForEastInLock"]
                               /\ UNCHANGED << lockOrientation, doorsOpen, 
                                               valvesOpen, waterLevel, 
                                               shipLocation, shipStatus, 
                                               lockCommand, permissions, perm, 
                                               req, oldLocation >>

ShipWaitForEastInLock(self) == /\ pc[self] = "ShipWaitForEastInLock"
                               /\ permissions /= <<>>
                               /\ perm' = [perm EXCEPT ![self] = Head(permissions)]
                               /\ permissions' = Tail(permissions)
                               /\ Assert(perm'[self].lock = GetLock(shipLocation), 
                                         "Failure of assertion at line 186, column 13.")
                               /\ pc' = [pc EXCEPT ![self] = "ShipMoveEast"]
                               /\ UNCHANGED << lockOrientation, doorsOpen, 
                                               valvesOpen, waterLevel, 
                                               shipLocation, shipStatus, 
                                               lockCommand, requests, req, 
                                               oldLocation >>

ShipTurnAround(self) == /\ pc[self] = "ShipTurnAround"
                        /\ shipStatus' = (IF shipLocation = WestEnd THEN "go_to_east" ELSE "go_to_west")
                        /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                        /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                        waterLevel, shipLocation, lockCommand, 
                                        requests, permissions, perm, req, 
                                        oldLocation >>

ShipGoalReachedWest(self) == /\ pc[self] = "ShipGoalReachedWest"
                             /\ shipStatus' = "goal_reached"
                             /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                             /\ UNCHANGED << lockOrientation, doorsOpen, 
                                             valvesOpen, waterLevel, 
                                             shipLocation, lockCommand, 
                                             requests, permissions, perm, req, 
                                             oldLocation >>

ShipMoveWest(self) == /\ pc[self] = "ShipMoveWest"
                      /\ IF perm[self].granted
                            THEN /\ Assert(doorsOpen[IF InLock THEN "west" ELSE "east"], 
                                           "Failure of assertion at line 220, column 13.")
                                 /\ shipLocation' = shipLocation - 1
                            ELSE /\ TRUE
                                 /\ UNCHANGED shipLocation
                      /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                      /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                      waterLevel, shipStatus, lockCommand, 
                                      requests, permissions, perm, req, 
                                      oldLocation >>

ShipRequestEast(self) == /\ pc[self] = "ShipRequestEast"
                         /\ requests' = Append(requests, ([ship |-> self, lock |-> 1, side |-> "east"]))
                         /\ pc' = [pc EXCEPT ![self] = "ShipWaitForEast"]
                         /\ UNCHANGED << lockOrientation, doorsOpen, 
                                         valvesOpen, waterLevel, shipLocation, 
                                         shipStatus, lockCommand, permissions, 
                                         perm, req, oldLocation >>

ShipWaitForEast(self) == /\ pc[self] = "ShipWaitForEast"
                         /\ permissions /= <<>>
                         /\ perm' = [perm EXCEPT ![self] = Head(permissions)]
                         /\ permissions' = Tail(permissions)
                         /\ Assert(perm'[self].lock = GetLock(shipLocation-1), 
                                   "Failure of assertion at line 207, column 13.")
                         /\ pc' = [pc EXCEPT ![self] = "ShipMoveWest"]
                         /\ UNCHANGED << lockOrientation, doorsOpen, 
                                         valvesOpen, waterLevel, shipLocation, 
                                         shipStatus, lockCommand, requests, 
                                         req, oldLocation >>

ShipRequestWestInLock(self) == /\ pc[self] = "ShipRequestWestInLock"
                               /\ requests' = Append(requests, ([ship |-> self, lock |-> 1, side |-> "west"]))
                               /\ pc' = [pc EXCEPT ![self] = "ShipWaitForWestInLock"]
                               /\ UNCHANGED << lockOrientation, doorsOpen, 
                                               valvesOpen, waterLevel, 
                                               shipLocation, shipStatus, 
                                               lockCommand, permissions, perm, 
                                               req, oldLocation >>

ShipWaitForWestInLock(self) == /\ pc[self] = "ShipWaitForWestInLock"
                               /\ permissions /= <<>>
                               /\ perm' = [perm EXCEPT ![self] = Head(permissions)]
                               /\ permissions' = Tail(permissions)
                               /\ Assert(perm'[self].lock = GetLock(shipLocation), 
                                         "Failure of assertion at line 215, column 13.")
                               /\ pc' = [pc EXCEPT ![self] = "ShipMoveWest"]
                               /\ UNCHANGED << lockOrientation, doorsOpen, 
                                               valvesOpen, waterLevel, 
                                               shipLocation, shipStatus, 
                                               lockCommand, requests, req, 
                                               oldLocation >>

shipProcess(self) == ShipNextIteration(self) \/ ShipGoalReachedEast(self)
                        \/ ShipMoveEast(self) \/ ShipRequestWest(self)
                        \/ ShipWaitForWest(self)
                        \/ ShipRequestEastInLock(self)
                        \/ ShipWaitForEastInLock(self)
                        \/ ShipTurnAround(self)
                        \/ ShipGoalReachedWest(self) \/ ShipMoveWest(self)
                        \/ ShipRequestEast(self) \/ ShipWaitForEast(self)
                        \/ ShipRequestWestInLock(self)
                        \/ ShipWaitForWestInLock(self)

ControlStart == /\ pc[0] = "ControlStart"
                /\ lockCommand.command = "finished"
                /\ oldLocation' = shipLocation
                /\ requests /= <<>>
                /\ req' = Head(requests)
                /\ requests' = Tail(requests)
                /\ pc' = [pc EXCEPT ![0] = "OpenValve"]
                /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                waterLevel, shipLocation, shipStatus, 
                                lockCommand, permissions, perm >>

OpenValve == /\ pc[0] = "OpenValve"
             /\ lockCommand' = [command |-> "change_valve", open |-> TRUE, side |-> getValveSide(lockOrientation, req.side)]
             /\ pc' = [pc EXCEPT ![0] = "CloseValve"]
             /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                             waterLevel, shipLocation, shipStatus, requests, 
                             permissions, perm, req, oldLocation >>

CloseValve == /\ pc[0] = "CloseValve"
              /\ lockCommand.command = "finished"
              /\ lockCommand' = [command |-> "change_valve", open |-> TRUE, side |-> getValveSide(lockOrientation, req.side)]
              /\ pc' = [pc EXCEPT ![0] = "OpenDoor"]
              /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                              waterLevel, shipLocation, shipStatus, requests, 
                              permissions, perm, req, oldLocation >>

OpenDoor == /\ pc[0] = "OpenDoor"
            /\ lockCommand.command = "finished"
            /\ lockCommand' = [command |-> "change_door", open |-> TRUE, side |-> req.side]
            /\ pc' = [pc EXCEPT ![0] = "GivePermission"]
            /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, waterLevel, 
                            shipLocation, shipStatus, requests, permissions, 
                            perm, req, oldLocation >>

GivePermission == /\ pc[0] = "GivePermission"
                  /\ lockCommand.command = "finished"
                  /\ permissions' = Append(permissions, ([lock |-> 1, granted |-> TRUE]))
                  /\ pc' = [pc EXCEPT ![0] = "WaitForShipToPassAndCloseDoor"]
                  /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                  waterLevel, shipLocation, shipStatus, 
                                  lockCommand, requests, perm, req, 
                                  oldLocation >>

WaitForShipToPassAndCloseDoor == /\ pc[0] = "WaitForShipToPassAndCloseDoor"
                                 /\ shipLocation # oldLocation
                                 /\ lockCommand' = [command |-> "change_door", open |-> FALSE, side |-> req.side]
                                 /\ pc' = [pc EXCEPT ![0] = "WaitCloseDoor"]
                                 /\ UNCHANGED << lockOrientation, doorsOpen, 
                                                 valvesOpen, waterLevel, 
                                                 shipLocation, shipStatus, 
                                                 requests, permissions, perm, 
                                                 req, oldLocation >>

WaitCloseDoor == /\ pc[0] = "WaitCloseDoor"
                 /\ lockCommand.command = "finished"
                 /\ pc' = [pc EXCEPT ![0] = "ControlStart"]
                 /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                 waterLevel, shipLocation, shipStatus, 
                                 lockCommand, requests, permissions, perm, req, 
                                 oldLocation >>

controlProcess == ControlStart \/ OpenValve \/ CloseValve \/ OpenDoor
                     \/ GivePermission \/ WaitForShipToPassAndCloseDoor
                     \/ WaitCloseDoor

Next == controlProcess
           \/ (\E self \in Locks: lockProcess(self))
           \/ (\E self \in Ships: shipProcess(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Locks : WF_vars(lockProcess(self))
        /\ \A self \in Ships : WF_vars(shipProcess(self))
        /\ WF_vars(controlProcess)

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Mon Oct 06 16:32:44 CEST 2025 by 20241856
\* Last modified Wed Oct 01 17:36:23 CEST 2025 by 20241856
\* Last modified Wed Sep 24 11:08:53 CEST 2025 by mvolk
\* Created Thu Aug 28 11:30:23 CEST 2025 by mvolk
