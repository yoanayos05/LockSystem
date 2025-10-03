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
DoorsMutex == FALSE
\* When the lower/higher pair of doors is open, the higher/lower valve is closed.
DoorsOpenValvesClosed == FALSE
\* The lower/higher pair of doors is only open when the water level in the lock is low/high
DoorsOpenWaterlevelRight  == FALSE
\* Always if the ship requests to enter the lock, the ship will eventually be inside the lock.
RequestLockFulfilled == FALSE
\* Water level is infinitely many times high/low
WaterlevelChange == FALSE
\* Infinitely many times the ship does requests
RequestsShips == FALSE
\* Infinitely many times the ship reaches its end location
ShipsReachGoals == FALSE

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
process lockProcess \in Locks
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
process shipProcess \in Ships
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
process controlProcess = 0
begin
  ControlStart:
    \* Implement behaviour
    skip;
    
end process;


end algorithm; *)


\* BEGIN TRANSLATION (chksum(pcal) = "b476ad83" /\ chksum(tla) = "ab6f364")
VARIABLES lockOrientation, doorsOpen, valvesOpen, waterLevel, shipLocation, 
          shipStatus, lockCommand, requests, permissions, pc

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






DoorsMutex == FALSE

DoorsOpenValvesClosed == FALSE

DoorsOpenWaterlevelRight  == FALSE

RequestLockFulfilled == FALSE

WaterlevelChange == FALSE

RequestsShips == FALSE

ShipsReachGoals == FALSE





ShipCanEnterLock == FALSE

RequestsMade == FALSE

RequestsNotFull == FALSE

LocationsVisited == FALSE

VARIABLE perm

vars == << lockOrientation, doorsOpen, valvesOpen, waterLevel, shipLocation, 
           shipStatus, lockCommand, requests, permissions, pc, perm >>

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
                                                            "Failure of assertion at line 153, column 9.")
                                                  /\ UNCHANGED valvesOpen
                                       /\ UNCHANGED doorsOpen
                            /\ IF valvesOpen'["low"]
                                  THEN /\ waterLevel' = "low"
                                  ELSE /\ IF (lockOrientation = "west_low" /\ doorsOpen'["west"])
                                              \/ (lockOrientation = "east_low" /\ doorsOpen'["east"])
                                             THEN /\ waterLevel' = "low"
                                             ELSE /\ IF valvesOpen'["high"]
                                                        THEN /\ waterLevel' = "high"
                                                        ELSE /\ IF (lockOrientation = "west_low" /\ doorsOpen'["east"])
                                                                    \/ (lockOrientation = "east_low" /\ doorsOpen'["west"])
                                                                   THEN /\ waterLevel' = "high"
                                                                   ELSE /\ TRUE
                                                                        /\ UNCHANGED waterLevel
                            /\ pc' = [pc EXCEPT ![self] = "LockCommandFinished"]
                            /\ UNCHANGED << lockOrientation, shipLocation, 
                                            shipStatus, lockCommand, requests, 
                                            permissions, perm >>

LockCommandFinished(self) == /\ pc[self] = "LockCommandFinished"
                             /\ lockCommand' = [lockCommand EXCEPT !.command = "finished"]
                             /\ pc' = [pc EXCEPT ![self] = "LockWaitForCommand"]
                             /\ UNCHANGED << lockOrientation, doorsOpen, 
                                             valvesOpen, waterLevel, 
                                             shipLocation, shipStatus, 
                                             requests, permissions, perm >>

lockProcess(self) == LockWaitForCommand(self) \/ LockCommandFinished(self)

ShipNextIteration(self) == /\ pc[self] = "ShipNextIteration"
                           /\ IF shipStatus = "go_to_east"
                                 THEN /\ IF shipLocation = EastEnd
                                            THEN /\ shipStatus' = "goal_reached"
                                                 /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                                                 /\ UNCHANGED requests
                                            ELSE /\ IF ~InLock
                                                       THEN /\ requests' = Append(requests, ([ship |-> self, lock |-> 1, side |-> "west"]))
                                                            /\ pc' = [pc EXCEPT ![self] = "ShipWaitForWest"]
                                                       ELSE /\ requests' = Append(requests, ([ship |-> self, lock |-> 1, side |-> "east"]))
                                                            /\ pc' = [pc EXCEPT ![self] = "ShipWaitForEastInLock"]
                                                 /\ UNCHANGED shipStatus
                                 ELSE /\ IF shipStatus = "go_to_west"
                                            THEN /\ IF shipLocation = WestEnd
                                                       THEN /\ shipStatus' = "goal_reached"
                                                            /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                                                            /\ UNCHANGED requests
                                                       ELSE /\ IF ~InLock
                                                                  THEN /\ requests' = Append(requests, ([ship |-> self, lock |-> 1, side |-> "east"]))
                                                                       /\ pc' = [pc EXCEPT ![self] = "ShipWaitForEast"]
                                                                  ELSE /\ requests' = Append(requests, ([ship |-> self, lock |-> 1, side |-> "west"]))
                                                                       /\ pc' = [pc EXCEPT ![self] = "ShipWaitForWestInLock"]
                                                            /\ UNCHANGED shipStatus
                                            ELSE /\ Assert(shipStatus = "goal_reached", 
                                                           "Failure of assertion at line 230, column 9.")
                                                 /\ shipStatus' = (IF shipLocation = WestEnd THEN "go_to_east" ELSE "go_to_west")
                                                 /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                                                 /\ UNCHANGED requests
                           /\ UNCHANGED << lockOrientation, doorsOpen, 
                                           valvesOpen, waterLevel, 
                                           shipLocation, lockCommand, 
                                           permissions, perm >>

ShipMoveEast(self) == /\ pc[self] = "ShipMoveEast"
                      /\ IF perm[self].granted
                            THEN /\ Assert(doorsOpen[IF InLock THEN "east" ELSE "west"], 
                                           "Failure of assertion at line 196, column 13.")
                                 /\ shipLocation' = shipLocation + 1
                            ELSE /\ TRUE
                                 /\ UNCHANGED shipLocation
                      /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                      /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                      waterLevel, shipStatus, lockCommand, 
                                      requests, permissions, perm >>

ShipWaitForWest(self) == /\ pc[self] = "ShipWaitForWest"
                         /\ permissions /= <<>>
                         /\ perm' = [perm EXCEPT ![self] = Head(permissions)]
                         /\ permissions' = Tail(permissions)
                         /\ Assert(perm'[self].lock = GetLock(shipLocation+1), 
                                   "Failure of assertion at line 183, column 13.")
                         /\ pc' = [pc EXCEPT ![self] = "ShipMoveEast"]
                         /\ UNCHANGED << lockOrientation, doorsOpen, 
                                         valvesOpen, waterLevel, shipLocation, 
                                         shipStatus, lockCommand, requests >>

ShipWaitForEastInLock(self) == /\ pc[self] = "ShipWaitForEastInLock"
                               /\ permissions /= <<>>
                               /\ perm' = [perm EXCEPT ![self] = Head(permissions)]
                               /\ permissions' = Tail(permissions)
                               /\ Assert(perm'[self].lock = GetLock(shipLocation), 
                                         "Failure of assertion at line 191, column 13.")
                               /\ pc' = [pc EXCEPT ![self] = "ShipMoveEast"]
                               /\ UNCHANGED << lockOrientation, doorsOpen, 
                                               valvesOpen, waterLevel, 
                                               shipLocation, shipStatus, 
                                               lockCommand, requests >>

ShipMoveWest(self) == /\ pc[self] = "ShipMoveWest"
                      /\ IF perm[self].granted
                            THEN /\ Assert(doorsOpen[IF InLock THEN "west" ELSE "east"], 
                                           "Failure of assertion at line 225, column 13.")
                                 /\ shipLocation' = shipLocation - 1
                            ELSE /\ TRUE
                                 /\ UNCHANGED shipLocation
                      /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                      /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                      waterLevel, shipStatus, lockCommand, 
                                      requests, permissions, perm >>

ShipWaitForEast(self) == /\ pc[self] = "ShipWaitForEast"
                         /\ permissions /= <<>>
                         /\ perm' = [perm EXCEPT ![self] = Head(permissions)]
                         /\ permissions' = Tail(permissions)
                         /\ Assert(perm'[self].lock = GetLock(shipLocation-1), 
                                   "Failure of assertion at line 212, column 13.")
                         /\ pc' = [pc EXCEPT ![self] = "ShipMoveWest"]
                         /\ UNCHANGED << lockOrientation, doorsOpen, 
                                         valvesOpen, waterLevel, shipLocation, 
                                         shipStatus, lockCommand, requests >>

ShipWaitForWestInLock(self) == /\ pc[self] = "ShipWaitForWestInLock"
                               /\ permissions /= <<>>
                               /\ perm' = [perm EXCEPT ![self] = Head(permissions)]
                               /\ permissions' = Tail(permissions)
                               /\ Assert(perm'[self].lock = GetLock(shipLocation), 
                                         "Failure of assertion at line 220, column 13.")
                               /\ pc' = [pc EXCEPT ![self] = "ShipMoveWest"]
                               /\ UNCHANGED << lockOrientation, doorsOpen, 
                                               valvesOpen, waterLevel, 
                                               shipLocation, shipStatus, 
                                               lockCommand, requests >>

shipProcess(self) == ShipNextIteration(self) \/ ShipMoveEast(self)
                        \/ ShipWaitForWest(self)
                        \/ ShipWaitForEastInLock(self)
                        \/ ShipMoveWest(self) \/ ShipWaitForEast(self)
                        \/ ShipWaitForWestInLock(self)

ControlStart == /\ pc[0] = "ControlStart"
                /\ TRUE
                /\ pc' = [pc EXCEPT ![0] = "Done"]
                /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                waterLevel, shipLocation, shipStatus, 
                                lockCommand, requests, permissions, perm >>

controlProcess == ControlStart

Next == controlProcess
           \/ (\E self \in Locks: lockProcess(self))
           \/ (\E self \in Ships: shipProcess(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Wed Sep 24 11:08:53 CEST 2025 by mvolk
\* Created Thu Aug 28 11:30:23 CEST 2025 by mvolk
