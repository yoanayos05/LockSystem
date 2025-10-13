--------------------------- MODULE lock_multiple ---------------------------

EXTENDS lock_data


(* --algorithm lock_system

\*****************************
\* Define global variables
\*****************************
variables
  \* Variables for locks
  lockOrientations = [l \in Locks |-> IF l%2=0 THEN "west_low" ELSE "east_low"],
  doorsOpen = [l \in Locks |-> [ls \in LockSide |-> FALSE]],
  valvesOpen = [l \in Locks |-> [vs \in ValveSide |-> FALSE]],
  waterLevel = [l \in Locks |-> "low"],
  
  \* Variables for single ship
  shipLocations = [s \in Ships |-> IF s%2=0 THEN 0 ELSE EastEnd],
  shipStates = [s \in Ships |-> IF s%2=0 THEN "go_to_east" ELSE "go_to_west"],
  
  \* Command for lock
  \* for command "change_door" the side should be "west" or "east"
  \* for command "change_valve" the side should be "high" or "low"
  lockCommand = [l \in Locks |-> [command |-> "finished", open |-> FALSE, side |-> "west"]],
  \* Central requests of all ships
  requests = << >>,
  \* Permissions per ship
  permissions = [s \in Ships |-> << >>],
  moved = [s \in Ships |-> FALSE];


define

\*****************************
\* Helper functions
\*****************************
\* Check if given ship is within a lock
InLock(ship) == IsLock(shipLocations[ship])
NumberAtLocation(loc) == Cardinality({s \in Ships: shipLocations[s] = loc})
NumberAtLocationCorrect(loc) == IF IsLock(loc) THEN NumberAtLocation(loc) <= MaxShipsLock ELSE NumberAtLocation(loc) <= MaxShipsLocation



\*****************************
\* Type checks
\*****************************
\* Check that variables use the correct type
TypeOK == /\ \A l \in Locks: /\ lockOrientations[l] \in LockOrientation
                             /\ \A ls \in LockSide : doorsOpen[l][ls] \in BOOLEAN
                             /\ \A vs \in ValveSide : valvesOpen[l][vs] \in BOOLEAN
                             /\ waterLevel[l] \in WaterLevel
                             /\ lockCommand[l].command \in LockCommand
                             /\ lockCommand[l].open \in BOOLEAN
                             /\ lockCommand[l].side \in LockSide \union ValveSide
          /\ \A s \in Ships: /\ shipLocations[s] \in Locations
                             /\ shipStates[s] \in ShipStatus
                             /\ \A i \in 1..Len(permissions[s]):
                                  /\ permissions[s][i].lock \in Locks
                                  /\ permissions[s][i].granted \in BOOLEAN
                             /\ moved[s] \in BOOLEAN
          /\ \A i \in 1..Len(requests):
               /\ requests[i].ship \in Ships
               /\ requests[i].lock \in Locks
               /\ requests[i].side \in LockSide

\* Check that message queues are not overflowing
MessagesOK == /\ Len(requests) <= NumShips
              /\ \A s \in Ships: Len(permissions[s]) <= 1


\*****************************
\* Requirements on lock
\*****************************
\* The eastern pair of doors and the western pair of doors are never simultaneously open
DoorsMutex == FALSE
\* When the lower/higher pair of doors is open, the higher/lower valve is closed.
DoorsOpenValvesClosed == FALSE
\* The lower/higher pair of doors is only open when the water level in the lock is low/high
DoorsOpenWaterlevelRight  == FALSE
\* Always if a ship requests to enter a lock, the ship will eventually be inside the lock.
RequestLockFulfilled == FALSE
\* Water level is infinitely many times high/low
WaterlevelChange == FALSE
\* Infinitely many times each ship does requests
RequestsShips == FALSE
\* Infinitely many times each ship reaches its end location
ShipsReachGoals == FALSE
\* The maximal ship capacity per location is not exceeded
MaxShipsPerLocation == FALSE



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
      await lockCommand[self].command /= "finished";
      if lockCommand[self].command = "change_door" then
        \* Change status of door
        doorsOpen[self][lockCommand[self].side] := lockCommand[self].open;
      elsif lockCommand[self].command = "change_valve" then
        \* Change status of valve
        valvesOpen[self][lockCommand[self].side] := lockCommand[self].open;
      else
        \* should not happen
        assert FALSE;
      end if;
  LockUpdateWaterLevel:
      updateWaterLevel(lockOrientations[self], doorsOpen[self], valvesOpen[self], waterLevel[self]);
  LockCommandFinished:
      lockCommand[self].command := "finished";    
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
      if shipStates[self] = "go_to_east" then
        if shipLocations[self] = EastEnd then
  ShipGoalReachedEast:
          shipStates[self] := "goal_reached";
        else
          if ~InLock(self) then
  ShipRequestWest:
            \* Request west doors of next lock
            write(requests, [ship |-> self, lock |-> GetLock(shipLocations[self]+1), side |-> "west"]);
  ShipWaitForWest:
            \* Wait for permission
            read(permissions[self], perm);
            assert perm.lock = GetLock(shipLocations[self]+1);
          else
  ShipRequestEastInLock:
            \* Request east doors of current lock
            write(requests, [ship |-> self, lock |-> GetLock(shipLocations[self]), side |-> "east"]);
  ShipWaitForEastInLock:
            \* Wait for permission
            read(permissions[self], perm);
            assert perm.lock = GetLock(shipLocations[self]);
          end if;
  ShipMoveEast:
          if perm.granted then
            \* Move ship
            assert doorsOpen[perm.lock][IF InLock(self) THEN "east" ELSE "west"];
            shipLocations[self] := shipLocations[self] + 1;
            \* Signal finished movement
            moved[self] := TRUE;
          end if;
        end if;
      elsif shipStates[self] = "go_to_west" then
        if shipLocations[self] = WestEnd then
  ShipGoalReachedWest:
          shipStates[self] := "goal_reached";
        else
          if ~InLock(self) then
  ShipRequestEast:
            \* Request east doors of next lock
            write(requests, [ship |-> self, lock |-> GetLock(shipLocations[self]-1), side |-> "east"]);
  ShipWaitForEast:
            \* Wait for permission
            read(permissions[self], perm);
            assert perm.lock = GetLock(shipLocations[self]-1);
          else
  ShipRequestWestInLock:
            \* Request west doors of current lock
            write(requests, [ship |-> self, lock |-> GetLock(shipLocations[self]), side |-> "west"]);
  ShipWaitForWestInLock:
            \* Wait for permission
            read(permissions[self], perm);
            assert perm.lock = GetLock(shipLocations[self]);
          end if;
  ShipMoveWest:
          if perm.granted then
            \* Move ship
            assert doorsOpen[perm.lock][IF InLock(self) THEN "west" ELSE "east"];
            shipLocations[self] := shipLocations[self] - 1;
            \* Signal finished movement
            moved[self] := TRUE;
          end if;
        end if;
      else
        assert shipStates[self] = "goal_reached";
  ShipTurnAround:
        \* Turn around
        shipStates[self] := IF shipLocations[self] = WestEnd THEN "go_to_east" ELSE "go_to_west";
      end if;
    end while;
end process;


\*****************************
\* Process for the controller
\*****************************
fair process controlProcess = 0


variables
req = [ship |-> 2, lock |-> 1, side |-> "west"];
activeShipNumber = 0

begin
  ControlStart:
    \* Implement behaviour
    while TRUE do
        await lockCommand[req.lock].command = "finished";
        read(requests, req);
        moved[req.ship] := FALSE;
        \* Note for report: moved takes the role of oldLocation, so its use was already demonstrated in single lock
    CheckEntranceIntoCanal:
    \* Here I'm denying the entrance of a ship into the system if it would pass the limit
    \* The limit is the max number of ships per location (maybe make it maxPerLocation + maxPerLock - 1)
        if shipLocations[req.ship] = 0 \/ shipLocations[req.ship] = EastEnd then
            if activeShipNumber \geq MaxShipsLocation then
                write(permissions[req.ship],[lock |-> req.lock, granted |-> FALSE]);
                goto WaitCloseDoor;
            else activeShipNumber := activeShipNumber + 1;
            end if;
        end if;
    CheckMechanicalValidityOfMove:
    \*Here I'm thinking of denying the process if an opposite door/valve is opened. I want it at the start cause if I were to do it separately for valves and doors it may lead to a deadlock
        if doorsOpen[req.lock][getOtherSide(req.side)] \/
            valvesOpen[req.lock][getOtherSide(getValveSide(lockOrientations[req.lock], req.side))]
        then
            write(permissions[req.ship],[lock |-> req.lock, granted |-> FALSE]);
            goto WaitCloseDoor;
        end if;
    CheckTargetLimit:
    \*Check if a ship would enter a room that passes the limit
        if ~NumberAtLocationCorrect(IF shipStates[req.ship] = "go_to_west" THEN shipLocations[req.ship] - 1 ELSE shipLocations[req.ship] + 1) then 
            write(permissions[req.ship],[lock |-> req.lock, granted |-> FALSE]);
            goto WaitCloseDoor;
        end if;
    OpenValve:
        lockCommand[req.lock] := [command |-> "change_valve", open |-> TRUE, side |-> getValveSide(lockOrientations[req.lock], req.side)];
        
    CloseValve:
        await lockCommand[req.lock].command = "finished";
        lockCommand[req.lock] := [command |-> "change_valve", open |-> FALSE, side |-> getValveSide(lockOrientations[req.lock], req.side)];
        
    OpenDoor:
        await lockCommand[req.lock].command = "finished";
        lockCommand[req.lock] := [command |-> "change_door", open |-> TRUE, side |-> req.side];
        
    GivePermission:
        await lockCommand[req.lock].command = "finished";
        assert doorsOpen[req.lock][req.side];        
        write(permissions[req.ship], [lock |-> req.lock, granted |-> TRUE]);
        
    WaitForShipToPassAndCloseDoor:
        await moved[req.ship];
        moved[req.ship] := FALSE;
        lockCommand[req.lock] := [command |-> "change_door", open |-> FALSE, side |-> req.side];
        
    UpdateActiveShipCount:
        if shipStates[req.ship] = "goal_reached" then 
            activeShipNumber := activeShipNumber - 1;
        end if;
        
    WaitCloseDoor:
        await lockCommand[req.lock].command = "finished";
     
     end while;
    
end process;


end algorithm; *)


\* BEGIN TRANSLATION (chksum(pcal) = "d36680f0" /\ chksum(tla) = "81f51b9b")
VARIABLES pc, lockOrientations, doorsOpen, valvesOpen, waterLevel, 
          shipLocations, shipStates, lockCommand, requests, permissions, 
          moved

(* define statement *)
InLock(ship) == IsLock(shipLocations[ship])
NumberAtLocation(loc) == Cardinality({s \in Ships: shipLocations[s] = loc})
NumberAtLocationCorrect(loc) == IF IsLock(loc) THEN NumberAtLocation(loc) <= MaxShipsLock ELSE NumberAtLocation(loc) <= MaxShipsLocation







TypeOK == /\ \A l \in Locks: /\ lockOrientations[l] \in LockOrientation
                             /\ \A ls \in LockSide : doorsOpen[l][ls] \in BOOLEAN
                             /\ \A vs \in ValveSide : valvesOpen[l][vs] \in BOOLEAN
                             /\ waterLevel[l] \in WaterLevel
                             /\ lockCommand[l].command \in LockCommand
                             /\ lockCommand[l].open \in BOOLEAN
                             /\ lockCommand[l].side \in LockSide \union ValveSide
          /\ \A s \in Ships: /\ shipLocations[s] \in Locations
                             /\ shipStates[s] \in ShipStatus
                             /\ \A i \in 1..Len(permissions[s]):
                                  /\ permissions[s][i].lock \in Locks
                                  /\ permissions[s][i].granted \in BOOLEAN
                             /\ moved[s] \in BOOLEAN
          /\ \A i \in 1..Len(requests):
               /\ requests[i].ship \in Ships
               /\ requests[i].lock \in Locks
               /\ requests[i].side \in LockSide


MessagesOK == /\ Len(requests) <= NumShips
              /\ \A s \in Ships: Len(permissions[s]) <= 1






DoorsMutex == FALSE

DoorsOpenValvesClosed == FALSE

DoorsOpenWaterlevelRight  == FALSE

RequestLockFulfilled == FALSE

WaterlevelChange == FALSE

RequestsShips == FALSE

ShipsReachGoals == FALSE

MaxShipsPerLocation == FALSE

VARIABLES perm, req, activeShipNumber

vars == << pc, lockOrientations, doorsOpen, valvesOpen, waterLevel, 
           shipLocations, shipStates, lockCommand, requests, permissions, 
           moved, perm, req, activeShipNumber >>

ProcSet == (Locks) \cup (Ships) \cup {0}

Init == (* Global variables *)
        /\ lockOrientations = [l \in Locks |-> IF l%2=0 THEN "west_low" ELSE "east_low"]
        /\ doorsOpen = [l \in Locks |-> [ls \in LockSide |-> FALSE]]
        /\ valvesOpen = [l \in Locks |-> [vs \in ValveSide |-> FALSE]]
        /\ waterLevel = [l \in Locks |-> "low"]
        /\ shipLocations = [s \in Ships |-> IF s%2=0 THEN 0 ELSE EastEnd]
        /\ shipStates = [s \in Ships |-> IF s%2=0 THEN "go_to_east" ELSE "go_to_west"]
        /\ lockCommand = [l \in Locks |-> [command |-> "finished", open |-> FALSE, side |-> "west"]]
        /\ requests = << >>
        /\ permissions = [s \in Ships |-> << >>]
        /\ moved = [s \in Ships |-> FALSE]
        (* Process shipProcess *)
        /\ perm = [self \in Ships |-> [lock |-> 1, granted |-> FALSE]]
        (* Process controlProcess *)
        /\ req = [ship |-> 2, lock |-> 1, side |-> "west"]
        /\ activeShipNumber = 0
        /\ pc = [self \in ProcSet |-> CASE self \in Locks -> "LockWaitForCommand"
                                        [] self \in Ships -> "ShipNextIteration"
                                        [] self = 0 -> "ControlStart"]

LockWaitForCommand(self) == /\ pc[self] = "LockWaitForCommand"
                            /\ lockCommand[self].command /= "finished"
                            /\ IF lockCommand[self].command = "change_door"
                                  THEN /\ doorsOpen' = [doorsOpen EXCEPT ![self][lockCommand[self].side] = lockCommand[self].open]
                                       /\ UNCHANGED valvesOpen
                                  ELSE /\ IF lockCommand[self].command = "change_valve"
                                             THEN /\ valvesOpen' = [valvesOpen EXCEPT ![self][lockCommand[self].side] = lockCommand[self].open]
                                             ELSE /\ Assert(FALSE, 
                                                            "Failure of assertion at line 151, column 9.")
                                                  /\ UNCHANGED valvesOpen
                                       /\ UNCHANGED doorsOpen
                            /\ pc' = [pc EXCEPT ![self] = "LockUpdateWaterLevel"]
                            /\ UNCHANGED << lockOrientations, waterLevel, 
                                            shipLocations, shipStates, 
                                            lockCommand, requests, permissions, 
                                            moved, perm, req, activeShipNumber >>

LockUpdateWaterLevel(self) == /\ pc[self] = "LockUpdateWaterLevel"
                              /\ IF (valvesOpen[self])["low"]
                                    THEN /\ waterLevel' = [waterLevel EXCEPT ![self] = "low"]
                                    ELSE /\ IF ((lockOrientations[self]) = "west_low" /\ (doorsOpen[self])["west"])
                                                \/ ((lockOrientations[self]) = "east_low" /\ (doorsOpen[self])["east"])
                                               THEN /\ waterLevel' = [waterLevel EXCEPT ![self] = "low"]
                                               ELSE /\ IF (valvesOpen[self])["high"]
                                                          THEN /\ waterLevel' = [waterLevel EXCEPT ![self] = "high"]
                                                          ELSE /\ IF ((lockOrientations[self]) = "west_low" /\ (doorsOpen[self])["east"])
                                                                      \/ ((lockOrientations[self]) = "east_low" /\ (doorsOpen[self])["west"])
                                                                     THEN /\ waterLevel' = [waterLevel EXCEPT ![self] = "high"]
                                                                     ELSE /\ TRUE
                                                                          /\ UNCHANGED waterLevel
                              /\ pc' = [pc EXCEPT ![self] = "LockCommandFinished"]
                              /\ UNCHANGED << lockOrientations, doorsOpen, 
                                              valvesOpen, shipLocations, 
                                              shipStates, lockCommand, 
                                              requests, permissions, moved, 
                                              perm, req, activeShipNumber >>

LockCommandFinished(self) == /\ pc[self] = "LockCommandFinished"
                             /\ lockCommand' = [lockCommand EXCEPT ![self].command = "finished"]
                             /\ pc' = [pc EXCEPT ![self] = "LockWaitForCommand"]
                             /\ UNCHANGED << lockOrientations, doorsOpen, 
                                             valvesOpen, waterLevel, 
                                             shipLocations, shipStates, 
                                             requests, permissions, moved, 
                                             perm, req, activeShipNumber >>

lockProcess(self) == LockWaitForCommand(self) \/ LockUpdateWaterLevel(self)
                        \/ LockCommandFinished(self)

ShipNextIteration(self) == /\ pc[self] = "ShipNextIteration"
                           /\ IF shipStates[self] = "go_to_east"
                                 THEN /\ IF shipLocations[self] = EastEnd
                                            THEN /\ pc' = [pc EXCEPT ![self] = "ShipGoalReachedEast"]
                                            ELSE /\ IF ~InLock(self)
                                                       THEN /\ pc' = [pc EXCEPT ![self] = "ShipRequestWest"]
                                                       ELSE /\ pc' = [pc EXCEPT ![self] = "ShipRequestEastInLock"]
                                 ELSE /\ IF shipStates[self] = "go_to_west"
                                            THEN /\ IF shipLocations[self] = WestEnd
                                                       THEN /\ pc' = [pc EXCEPT ![self] = "ShipGoalReachedWest"]
                                                       ELSE /\ IF ~InLock(self)
                                                                  THEN /\ pc' = [pc EXCEPT ![self] = "ShipRequestEast"]
                                                                  ELSE /\ pc' = [pc EXCEPT ![self] = "ShipRequestWestInLock"]
                                            ELSE /\ Assert(shipStates[self] = "goal_reached", 
                                                           "Failure of assertion at line 233, column 9.")
                                                 /\ pc' = [pc EXCEPT ![self] = "ShipTurnAround"]
                           /\ UNCHANGED << lockOrientations, doorsOpen, 
                                           valvesOpen, waterLevel, 
                                           shipLocations, shipStates, 
                                           lockCommand, requests, permissions, 
                                           moved, perm, req, activeShipNumber >>

ShipGoalReachedEast(self) == /\ pc[self] = "ShipGoalReachedEast"
                             /\ shipStates' = [shipStates EXCEPT ![self] = "goal_reached"]
                             /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                             /\ UNCHANGED << lockOrientations, doorsOpen, 
                                             valvesOpen, waterLevel, 
                                             shipLocations, lockCommand, 
                                             requests, permissions, moved, 
                                             perm, req, activeShipNumber >>

ShipMoveEast(self) == /\ pc[self] = "ShipMoveEast"
                      /\ IF perm[self].granted
                            THEN /\ Assert(doorsOpen[perm[self].lock][IF InLock(self) THEN "east" ELSE "west"], 
                                           "Failure of assertion at line 195, column 13.")
                                 /\ shipLocations' = [shipLocations EXCEPT ![self] = shipLocations[self] + 1]
                                 /\ moved' = [moved EXCEPT ![self] = TRUE]
                            ELSE /\ TRUE
                                 /\ UNCHANGED << shipLocations, moved >>
                      /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                      /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                      waterLevel, shipStates, lockCommand, 
                                      requests, permissions, perm, req, 
                                      activeShipNumber >>

ShipRequestWest(self) == /\ pc[self] = "ShipRequestWest"
                         /\ requests' = Append(requests, ([ship |-> self, lock |-> GetLock(shipLocations[self]+1), side |-> "west"]))
                         /\ pc' = [pc EXCEPT ![self] = "ShipWaitForWest"]
                         /\ UNCHANGED << lockOrientations, doorsOpen, 
                                         valvesOpen, waterLevel, shipLocations, 
                                         shipStates, lockCommand, permissions, 
                                         moved, perm, req, activeShipNumber >>

ShipWaitForWest(self) == /\ pc[self] = "ShipWaitForWest"
                         /\ (permissions[self]) /= <<>>
                         /\ perm' = [perm EXCEPT ![self] = Head((permissions[self]))]
                         /\ permissions' = [permissions EXCEPT ![self] = Tail((permissions[self]))]
                         /\ Assert(perm'[self].lock = GetLock(shipLocations[self]+1), 
                                   "Failure of assertion at line 182, column 13.")
                         /\ pc' = [pc EXCEPT ![self] = "ShipMoveEast"]
                         /\ UNCHANGED << lockOrientations, doorsOpen, 
                                         valvesOpen, waterLevel, shipLocations, 
                                         shipStates, lockCommand, requests, 
                                         moved, req, activeShipNumber >>

ShipRequestEastInLock(self) == /\ pc[self] = "ShipRequestEastInLock"
                               /\ requests' = Append(requests, ([ship |-> self, lock |-> GetLock(shipLocations[self]), side |-> "east"]))
                               /\ pc' = [pc EXCEPT ![self] = "ShipWaitForEastInLock"]
                               /\ UNCHANGED << lockOrientations, doorsOpen, 
                                               valvesOpen, waterLevel, 
                                               shipLocations, shipStates, 
                                               lockCommand, permissions, moved, 
                                               perm, req, activeShipNumber >>

ShipWaitForEastInLock(self) == /\ pc[self] = "ShipWaitForEastInLock"
                               /\ (permissions[self]) /= <<>>
                               /\ perm' = [perm EXCEPT ![self] = Head((permissions[self]))]
                               /\ permissions' = [permissions EXCEPT ![self] = Tail((permissions[self]))]
                               /\ Assert(perm'[self].lock = GetLock(shipLocations[self]), 
                                         "Failure of assertion at line 190, column 13.")
                               /\ pc' = [pc EXCEPT ![self] = "ShipMoveEast"]
                               /\ UNCHANGED << lockOrientations, doorsOpen, 
                                               valvesOpen, waterLevel, 
                                               shipLocations, shipStates, 
                                               lockCommand, requests, moved, 
                                               req, activeShipNumber >>

ShipTurnAround(self) == /\ pc[self] = "ShipTurnAround"
                        /\ shipStates' = [shipStates EXCEPT ![self] = IF shipLocations[self] = WestEnd THEN "go_to_east" ELSE "go_to_west"]
                        /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                        /\ UNCHANGED << lockOrientations, doorsOpen, 
                                        valvesOpen, waterLevel, shipLocations, 
                                        lockCommand, requests, permissions, 
                                        moved, perm, req, activeShipNumber >>

ShipGoalReachedWest(self) == /\ pc[self] = "ShipGoalReachedWest"
                             /\ shipStates' = [shipStates EXCEPT ![self] = "goal_reached"]
                             /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                             /\ UNCHANGED << lockOrientations, doorsOpen, 
                                             valvesOpen, waterLevel, 
                                             shipLocations, lockCommand, 
                                             requests, permissions, moved, 
                                             perm, req, activeShipNumber >>

ShipMoveWest(self) == /\ pc[self] = "ShipMoveWest"
                      /\ IF perm[self].granted
                            THEN /\ Assert(doorsOpen[perm[self].lock][IF InLock(self) THEN "west" ELSE "east"], 
                                           "Failure of assertion at line 226, column 13.")
                                 /\ shipLocations' = [shipLocations EXCEPT ![self] = shipLocations[self] - 1]
                                 /\ moved' = [moved EXCEPT ![self] = TRUE]
                            ELSE /\ TRUE
                                 /\ UNCHANGED << shipLocations, moved >>
                      /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                      /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                      waterLevel, shipStates, lockCommand, 
                                      requests, permissions, perm, req, 
                                      activeShipNumber >>

ShipRequestEast(self) == /\ pc[self] = "ShipRequestEast"
                         /\ requests' = Append(requests, ([ship |-> self, lock |-> GetLock(shipLocations[self]-1), side |-> "east"]))
                         /\ pc' = [pc EXCEPT ![self] = "ShipWaitForEast"]
                         /\ UNCHANGED << lockOrientations, doorsOpen, 
                                         valvesOpen, waterLevel, shipLocations, 
                                         shipStates, lockCommand, permissions, 
                                         moved, perm, req, activeShipNumber >>

ShipWaitForEast(self) == /\ pc[self] = "ShipWaitForEast"
                         /\ (permissions[self]) /= <<>>
                         /\ perm' = [perm EXCEPT ![self] = Head((permissions[self]))]
                         /\ permissions' = [permissions EXCEPT ![self] = Tail((permissions[self]))]
                         /\ Assert(perm'[self].lock = GetLock(shipLocations[self]-1), 
                                   "Failure of assertion at line 213, column 13.")
                         /\ pc' = [pc EXCEPT ![self] = "ShipMoveWest"]
                         /\ UNCHANGED << lockOrientations, doorsOpen, 
                                         valvesOpen, waterLevel, shipLocations, 
                                         shipStates, lockCommand, requests, 
                                         moved, req, activeShipNumber >>

ShipRequestWestInLock(self) == /\ pc[self] = "ShipRequestWestInLock"
                               /\ requests' = Append(requests, ([ship |-> self, lock |-> GetLock(shipLocations[self]), side |-> "west"]))
                               /\ pc' = [pc EXCEPT ![self] = "ShipWaitForWestInLock"]
                               /\ UNCHANGED << lockOrientations, doorsOpen, 
                                               valvesOpen, waterLevel, 
                                               shipLocations, shipStates, 
                                               lockCommand, permissions, moved, 
                                               perm, req, activeShipNumber >>

ShipWaitForWestInLock(self) == /\ pc[self] = "ShipWaitForWestInLock"
                               /\ (permissions[self]) /= <<>>
                               /\ perm' = [perm EXCEPT ![self] = Head((permissions[self]))]
                               /\ permissions' = [permissions EXCEPT ![self] = Tail((permissions[self]))]
                               /\ Assert(perm'[self].lock = GetLock(shipLocations[self]), 
                                         "Failure of assertion at line 221, column 13.")
                               /\ pc' = [pc EXCEPT ![self] = "ShipMoveWest"]
                               /\ UNCHANGED << lockOrientations, doorsOpen, 
                                               valvesOpen, waterLevel, 
                                               shipLocations, shipStates, 
                                               lockCommand, requests, moved, 
                                               req, activeShipNumber >>

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
                /\ lockCommand[req.lock].command = "finished"
                /\ requests /= <<>>
                /\ req' = Head(requests)
                /\ requests' = Tail(requests)
                /\ moved' = [moved EXCEPT ![req'.ship] = FALSE]
                /\ pc' = [pc EXCEPT ![0] = "CheckEntranceIntoCanal"]
                /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                waterLevel, shipLocations, shipStates, 
                                lockCommand, permissions, perm, 
                                activeShipNumber >>

CheckEntranceIntoCanal == /\ pc[0] = "CheckEntranceIntoCanal"
                          /\ IF shipLocations[req.ship] = 0 \/ shipLocations[req.ship] = EastEnd
                                THEN /\ IF activeShipNumber \geq MaxShipsLocation
                                           THEN /\ permissions' = [permissions EXCEPT ![req.ship] = Append((permissions[req.ship]), ([lock |-> req.lock, granted |-> FALSE]))]
                                                /\ pc' = [pc EXCEPT ![0] = "WaitCloseDoor"]
                                                /\ UNCHANGED activeShipNumber
                                           ELSE /\ activeShipNumber' = activeShipNumber + 1
                                                /\ pc' = [pc EXCEPT ![0] = "CheckMechanicalValidityOfMove"]
                                                /\ UNCHANGED permissions
                                ELSE /\ pc' = [pc EXCEPT ![0] = "CheckMechanicalValidityOfMove"]
                                     /\ UNCHANGED << permissions, 
                                                     activeShipNumber >>
                          /\ UNCHANGED << lockOrientations, doorsOpen, 
                                          valvesOpen, waterLevel, 
                                          shipLocations, shipStates, 
                                          lockCommand, requests, moved, perm, 
                                          req >>

CheckMechanicalValidityOfMove == /\ pc[0] = "CheckMechanicalValidityOfMove"
                                 /\ IF doorsOpen[req.lock][getOtherSide(req.side)] \/
                                        valvesOpen[req.lock][getOtherSide(getValveSide(lockOrientations[req.lock], req.side))]
                                       THEN /\ permissions' = [permissions EXCEPT ![req.ship] = Append((permissions[req.ship]), ([lock |-> req.lock, granted |-> FALSE]))]
                                            /\ pc' = [pc EXCEPT ![0] = "WaitCloseDoor"]
                                       ELSE /\ pc' = [pc EXCEPT ![0] = "CheckTargetLimit"]
                                            /\ UNCHANGED permissions
                                 /\ UNCHANGED << lockOrientations, doorsOpen, 
                                                 valvesOpen, waterLevel, 
                                                 shipLocations, shipStates, 
                                                 lockCommand, requests, moved, 
                                                 perm, req, activeShipNumber >>

CheckTargetLimit == /\ pc[0] = "CheckTargetLimit"
                    /\ IF ~NumberAtLocationCorrect(IF shipStates[req.ship] = "go_to_west" THEN shipLocations[req.ship] - 1 ELSE shipLocations[req.ship] + 1)
                          THEN /\ permissions' = [permissions EXCEPT ![req.ship] = Append((permissions[req.ship]), ([lock |-> req.lock, granted |-> FALSE]))]
                               /\ pc' = [pc EXCEPT ![0] = "WaitCloseDoor"]
                          ELSE /\ pc' = [pc EXCEPT ![0] = "OpenValve"]
                               /\ UNCHANGED permissions
                    /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                    waterLevel, shipLocations, shipStates, 
                                    lockCommand, requests, moved, perm, req, 
                                    activeShipNumber >>

OpenValve == /\ pc[0] = "OpenValve"
             /\ lockCommand' = [lockCommand EXCEPT ![req.lock] = [command |-> "change_valve", open |-> TRUE, side |-> getValveSide(lockOrientations[req.lock], req.side)]]
             /\ pc' = [pc EXCEPT ![0] = "CloseValve"]
             /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                             waterLevel, shipLocations, shipStates, requests, 
                             permissions, moved, perm, req, activeShipNumber >>

CloseValve == /\ pc[0] = "CloseValve"
              /\ lockCommand[req.lock].command = "finished"
              /\ lockCommand' = [lockCommand EXCEPT ![req.lock] = [command |-> "change_valve", open |-> FALSE, side |-> getValveSide(lockOrientations[req.lock], req.side)]]
              /\ pc' = [pc EXCEPT ![0] = "OpenDoor"]
              /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                              waterLevel, shipLocations, shipStates, requests, 
                              permissions, moved, perm, req, activeShipNumber >>

OpenDoor == /\ pc[0] = "OpenDoor"
            /\ lockCommand[req.lock].command = "finished"
            /\ lockCommand' = [lockCommand EXCEPT ![req.lock] = [command |-> "change_door", open |-> TRUE, side |-> req.side]]
            /\ pc' = [pc EXCEPT ![0] = "GivePermission"]
            /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                            waterLevel, shipLocations, shipStates, requests, 
                            permissions, moved, perm, req, activeShipNumber >>

GivePermission == /\ pc[0] = "GivePermission"
                  /\ lockCommand[req.lock].command = "finished"
                  /\ Assert(doorsOpen[req.lock][req.side], 
                            "Failure of assertion at line 297, column 9.")
                  /\ permissions' = [permissions EXCEPT ![req.ship] = Append((permissions[req.ship]), ([lock |-> req.lock, granted |-> TRUE]))]
                  /\ pc' = [pc EXCEPT ![0] = "WaitForShipToPassAndCloseDoor"]
                  /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                  waterLevel, shipLocations, shipStates, 
                                  lockCommand, requests, moved, perm, req, 
                                  activeShipNumber >>

WaitForShipToPassAndCloseDoor == /\ pc[0] = "WaitForShipToPassAndCloseDoor"
                                 /\ moved[req.ship]
                                 /\ moved' = [moved EXCEPT ![req.ship] = FALSE]
                                 /\ lockCommand' = [lockCommand EXCEPT ![req.lock] = [command |-> "change_door", open |-> FALSE, side |-> req.side]]
                                 /\ pc' = [pc EXCEPT ![0] = "UpdateActiveShipCount"]
                                 /\ UNCHANGED << lockOrientations, doorsOpen, 
                                                 valvesOpen, waterLevel, 
                                                 shipLocations, shipStates, 
                                                 requests, permissions, perm, 
                                                 req, activeShipNumber >>

UpdateActiveShipCount == /\ pc[0] = "UpdateActiveShipCount"
                         /\ IF shipStates[req.ship] = "goal_reached"
                               THEN /\ activeShipNumber' = activeShipNumber - 1
                               ELSE /\ TRUE
                                    /\ UNCHANGED activeShipNumber
                         /\ pc' = [pc EXCEPT ![0] = "WaitCloseDoor"]
                         /\ UNCHANGED << lockOrientations, doorsOpen, 
                                         valvesOpen, waterLevel, shipLocations, 
                                         shipStates, lockCommand, requests, 
                                         permissions, moved, perm, req >>

WaitCloseDoor == /\ pc[0] = "WaitCloseDoor"
                 /\ lockCommand[req.lock].command = "finished"
                 /\ pc' = [pc EXCEPT ![0] = "ControlStart"]
                 /\ UNCHANGED << lockOrientations, doorsOpen, valvesOpen, 
                                 waterLevel, shipLocations, shipStates, 
                                 lockCommand, requests, permissions, moved, 
                                 perm, req, activeShipNumber >>

controlProcess == ControlStart \/ CheckEntranceIntoCanal
                     \/ CheckMechanicalValidityOfMove \/ CheckTargetLimit
                     \/ OpenValve \/ CloseValve \/ OpenDoor
                     \/ GivePermission \/ WaitForShipToPassAndCloseDoor
                     \/ UpdateActiveShipCount \/ WaitCloseDoor

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
\* Last modified Mon Oct 13 15:44:03 CEST 2025 by 20241856
\* Last modified Fri Oct 03 10:34:10 CEST 2025 by 20241856
\* Last modified Wed Sep 24 12:00:55 CEST 2025 by mvolk
\* Created Thu Aug 28 11:30:07 CEST 2025 by mvolk
