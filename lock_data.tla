----------------------------- MODULE lock_data -----------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

\*****************************
\* Define constants
\*****************************
CONSTANTS
  NumLocks,
  NumShips,
  MaxShipsLocation,
  MaxShipsLock
ASSUME NumLocks \in Nat /\ NumLocks >= 1
  /\ NumShips \in Nat /\ NumShips >= 1
  /\ MaxShipsLocation \in Nat /\ MaxShipsLocation >= 1
  /\ MaxShipsLock \in Nat /\ MaxShipsLock >= 1 /\ MaxShipsLock <= MaxShipsLocation


\*****************************
\* Define data structures
\*****************************

\* Locks
Locks == 1..NumLocks
\* Ships have higher ids than locks
\* This is needed to avoid overlap with the lock process ids
Ships == (NumLocks+1)..(NumLocks+NumShips)
\* Even locations are outside lock
\* Odd locations are inside lock: location i corresponds to lock (i+1)/2
Locations == 0..NumLocks*2

\* Data types
LockOrientation == {"west_low", "east_low"}
LockSide == {"west", "east"}
ValveSide == {"low", "high"}
WaterLevel == {"low", "high"}
LockCommand == {"change_door", "change_valve", "finished"}

ShipStatus == {"go_to_west", "go_to_east", "goal_reached"}


\*****************************
\* Helper functions
\*****************************

\* Get the low/high side from a lock with a given orientation
LowSide(lock_orientation) == IF lock_orientation = "west_low" THEN "west" ELSE "east"
HighSide(lock_orientation) == IF lock_orientation = "west_low" THEN "east" ELSE "west"

\* Helper Function For Getting Valve Side

\* Original getValveSide(lockOrientation, side) == IF lockOrientation = "west_low" /\ side = "west" THEN "low" ELSE "high"
\* It does not account for a ship starting at the east end, but the program usually starts in the west hence why it works
getValveSide(lockOrientation, side) == IF (lockOrientation = "west_low" /\ side = "west") \/ (lockOrientation = "east_low" /\ side = "east") THEN "low" ELSE "high"                                             
getOtherSide(side) == IF side = "west" THEN "east" ELSE IF side = "east" THEN "west" ELSE IF side = "low" THEN "high" ELSE "low"
\* End points for ship locations
WestEnd == 0
EastEnd == NumLocks*2
\* Get lock corresponding to given location
\* Assumes that location is an odd value
GetLock(location) == (location + 1) \div 2
\* Check if a given location is within a lock.
\* Returns true if the location is an odd value
IsLock(location) == location % 2 = 1

=============================================================================
\* Modification History
\* Last modified Mon Oct 13 14:48:45 CEST 2025 by 20241856
\* Last modified Mon Oct 06 16:32:36 CEST 2025 by 20241856
\* Last modified Wed Sep 24 10:40:42 CEST 2025 by mvolk
\* Created Thu Aug 28 11:30:37 CEST 2025 by mvolk
