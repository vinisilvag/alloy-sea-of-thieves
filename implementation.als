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

abstract sig Location {}

one sig Ocean extends Location {}
abstract sig Island extends Location {}
abstract sig Outpost extends Location {}

-- one sig list_islands_subset extends Island {}
-- one sig list_outposts_subset extends Outpost {}

abstract sig Ship {
	var shipLocation: lone Location
}
one sig Sloop, Brigantine, Galleon extends Ship {}

abstract sig PirateStatus {}
one sig Dead, Alive, Otherworld extends PirateStatus {}

sig Pirate {
	var status: lone PirateStatus
}

sig Tripulation {
	var pirates: set Pirate,
	var ship: lone Ship
}

sig Server {
	var tripulations: set Tripulation
}

one sig SoTGame {
	servers: set Server
}

-- Track operators during execution
abstract sig Operator {}
one sig NOP, JT, LT, TLogon, TLogout extends Operator {}
one sig Track {
	var op: lone Operator
}

---------
-- Facts
---------

fact {
	always no s : Server | s not in SoTGame.servers

	-- Fato sobre o tamanho dos navios?
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

pred noShipChange [Ts: set Tripulation] {
	all t : Ts | t.ship' = t.ship
}

pred noShipLocationChange [Ss: set Ship] {
	all s : Ss | s.shipLocation' = s.shipLocation
}

pred noTripulationsChange [Ss: set Server] {
	all s : Ss | s.tripulations' = s.tripulations
}

-----------------------
-- Auxiliar predicates
-----------------------

-- Ver como fazer sobre os tamanhos de navio
pred tripulationShip [t: Tripulation] {}

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
	noPiratesChange[Tripulation - t]
	noShipChange[Tripulation]
	noShipLocationChange[Ship]
	noTripulationsChange[Server]

	Track.op' = JT
}

pred leaveTripulation [p: Pirate, t: Tripulation] {
	-- pre-conditions
	p in t.pirates
	#t.pirates - 1 > 0

	-- post-conditions
	t.pirates' = t.pirates - p
	no p.status

	-- frame-conditions
	noStatusChange[Pirate - p]
	noPiratesChange[Tripulation - t]
	noShipChange[Tripulation]
	noShipLocationChange[Ship]
	noTripulationsChange[Server]

	Track.op' = LT
}

pred tripulationLogon [sv: Server, t: Tripulation, sp: Ship] {
	-- pre-conditions
	t not in Server.tripulations
	no t.ship
	some t.pirates
	all p : t.pirates | no p.status

	-- post-conditions
	sv.tripulations' = sv.tripulations + t
	all p : t.pirates | p.status' = Alive
	t.ship' = sp
	-- t.ship.shipLocation' = l
	
	-- frame-conditions
	noStatusChange[Pirate - t.pirates]
	noPiratesChange[Tripulation]
	noShipChange[Tripulation - t]
	noShipLocationChange[Ship]
	noTripulationsChange[Server - sv]

	Track.op' = TLogon
}

pred tripulationLogout [s: Server, t: Tripulation] {
	-- pre-conditions
	t in Server.tripulations
	
	-- post-conditions
	no t.pirates
	no t.ship
	no t.ship.shipLocation
	s.tripulations' = s.tripulations - t
	all p : t.pirates | no p.status'
	
	-- frame-conditions
	noStatusChange[Pirate - t.pirates]
	noPiratesChange[Tripulation]
	noShipChange[Tripulation - t]
	noShipLocationChange[Ship]
	noTripulationsChange[Server - s]

	Track.op' = TLogout
}

-- Stutter
pred stutter [] {
	noStatusChange[Pirate]
	noPiratesChange[Tripulation]
	noShipChange[Tripulation]
	noShipLocationChange[Ship]
	noTripulationsChange[Server]
	
	Track.op' = NOP
}

-----------------
-- Initial state
-----------------

pred init [] {
	some SoTGame.servers
	no tripulations
	no pirates
	no status
	no ship
	no shipLocation

	no Track.op
}

-----------------------
-- Transition relation
-----------------------

pred transition []  {
	(some p : Pirate | some t : Tripulation | joinTripulation[p, t])
	or (some p : Pirate | some t : Tripulation | leaveTripulation[p, t])
	or (some sv : Server | some t : Tripulation | some sp : Ship | tripulationLogon[sv, t, sp])
	or (some s : Server | some t : Tripulation | tripulationLogout[s, t])
	or stutter
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

run execution { System && some sv : Server | some t : Tripulation | some sp : Ship | eventually tripulationLogon[sv, t, sp] } for 5

--------------
-- Properties
--------------

pred p1 {}

--------------
-- Assertions
--------------

assert a1 { System => p1 }

check a1 for 8
