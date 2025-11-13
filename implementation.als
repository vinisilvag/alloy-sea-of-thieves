-- ===============================================
--  DCC831 Formal Methods
--  2025.2
--
--  Course Project -> Modeling the universe of
--                    Sea of Thieves in Alloy
--
--  Name:  Vinicius Silva Gomes - 2021421869
--
-- ===============================================

--------------
-- Signatures
--------------

-- abstract sig Location {}

-- sig Ocean extends Location {}
-- abstract sig Island extends Location {}
-- abstract sig Outpost extends Location {}

-- sig list_islands_subset extends Island {}
-- sig list_outposts_subset extends Outpost {}

-- abstract sig Ship {
--   location: one Location
-- }
-- sig Sloop, Brigantine, Galleon extends Ship {}

abstract sig PirateStatus {}
one sig Dead, Alive, Otherworld extends PirateStatus {}

sig Pirate {
  var status: lone PirateStatus
}

sig Tripulation {
  var pirates: set Pirate
}

sig Server {
  var tripulations: set Tripulation
}

one sig SoTGame {
  servers: set Server
}

-- Track operators during execution
abstract sig Operator {}
one sig TLon, TLout extends Operator {}
one sig Track {
  var op: lone Operator
}

---------
-- Facts
---------

fact {
  always no s : Server | s not in SoTGame.servers

  always all t : Tripulation | #t.pirates >= 1 and #t.pirates <= 4

  always all p : Pirate | one pirates.p
}

--------------------
-- Frame conditions
--------------------

pred noStatusChange [Ps: set Pirate] {
  all p : Ps | p.status' = p.status
}

pred noPiratesChange [Ts: set Tripulation] {
  all t : Ts | t.pirates' = t.pirates
}

pred noTripulationsChange [Ss: set Server] {
  all s : Ss | s.tripulations' = s.tripulations
}

-------------
-- Operators
-------------

pred tripulationLogon [s: Server, t: Tripulation] {
  -- pre-conditions
  t not in Server.tripulations
  all p : t.pirates | no p.status

  -- post-conditions
  s.tripulations' = s.tripulations + t
  all p : t.pirates | p.status' = Alive
	
  -- frame-conditions
  -- noTripulationsChange[Server - s]
  -- noPiratesChange[Tripulation]
  -- noStatusChange[Pirate - t.pirates]

  Track.op' = TLon
}

pred tripulationLogout [s: Server, t: Tripulation] {
  -- pre-conditions
  t in Server.tripulations
  -- post-conditions
  s.tripulations' = s.tripulations - t
  all p : t.pirates | no p.status'
  -- frame-conditions
  -- noTripulationsChange[Server - s]
  -- noStatusChange[Pirate - t.pirates]

  Track.op' = TLout
}

-- Stutter
pred stutter [] {
  noStatusChange[Pirate]
  noTripulationsChange[Server]
}

-----------------
-- Initial state
-----------------

pred init [] {
  some SoTGame.servers
  no Server.tripulations
  -- no Ship.location
  no Pirate.status

  no Track.op
}

-----------------------
-- Transition relation
-----------------------

pred trans []  {
  (some s : Server | some t : Tripulation | tripulationLogon[s, t])
  -- or stutter
}

--------------------
-- System predicate
--------------------

pred System {
  init
  always trans
}

--------------
-- Executions
--------------

run execution { System } for 5

--------------
-- Properties
--------------

pred p1 {}

pred p2 {}

pred p3 {}

pred p4 {}

--------------
-- Assertions
--------------

assert a1 { System => p1 }
assert a2 { System => p2 }
assert a3 { System => p3 }
assert a4 { System => p4 }

check a1 for 8
check a2 for 8
check a3 for 8
check a4 for 8
