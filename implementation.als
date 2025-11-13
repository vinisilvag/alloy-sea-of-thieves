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
one sig JT, LT, TLon, TLout extends Operator {}
one sig Track {
  var op: lone Operator
}

---------
-- Facts
---------

fact {
  always no s : Server | s not in SoTGame.servers
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

pred joinTripulation [p: Pirate, t: Tripulation] {
	-- pre-conditions
	p not in Tripulation.pirates
	no p.status
	#t.pirates <= 3

	-- post-conditions
	t.pirates' = t.pirates + p

	-- frame-conditions
	noStatusChange[Pirate]
	-- noPiratesChange[Tripulation - t]
	noTripulationsChange[Server]

	Track.op' = JT
}

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
	no tripulations
	no pirates
	no status

	-- no location

  no Track.op
}

-----------------------
-- Transition relation
-----------------------

pred transition []  {
	(some p : Pirate | some t : Tripulation | joinTripulation[p, t])
  -- (some s : Server | some t : Tripulation | tripulationLogon[s, t])
  -- or stutter
}

--------------------
-- System predicate
--------------------

pred System {
  init
  always transition
}

--------------
-- Executions
--------------

run execution { System } for 5

--------------
-- Properties
--------------

pred p1 {}

--------------
-- Assertions
--------------

assert a1 { System => p1 }

check a1 for 8
