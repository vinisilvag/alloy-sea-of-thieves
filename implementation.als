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

sig Enemie {}

sig Treasure {}

abstract sig Location {}

one sig Ocean extends Location {}
abstract sig Island extends Location {
	var treasures: set Treasure,
	var enemies: set Enemie
}
abstract sig Outpost extends Location {}

-- one sig list_islands_subset extends Island {}
-- one sig list_outposts_subset extends Outpost {}

abstract sig Ship {}
one sig Sloop, Brigantine, Galleon extends Ship {}

abstract sig PirateStatus {}
one sig Dead, Alive, Otherworld extends PirateStatus {}

sig Pirate {
	var status: lone PirateStatus
}

sig Tripulation {
	var pirates: set Pirate,
	var ship: lone Ship,
	var location: lone Location,
	var collectedTreasures: set Treasure
}

sig Server {
	var tripulations: set Tripulation
}

one sig SoTGame {
	servers: set Server
}

-- Track operators during execution
abstract sig Operator {}
one sig NOP, JT, LT, TLogon, TLogout, ARR, DEP extends Operator {}
one sig Track {
	var op: lone Operator
}

---------
-- Facts
---------

fact {
	-- All servers are attached to SoTGame instance
	always no s : Server | s not in SoTGame.servers

	-- Fato sobre o tamanho dos navios?
	
	-- Islands do not share enemies
	always all e : Enemie | one enemies.e

	-- Islands do not share treasures
	always all t : Treasure | one treasures.t
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

pred noLocationChange [Ts: set Tripulation] {
	all t : Ts | t.location' = t.location
}

pred noTripulationsChange [Ss: set Server] {
	all s : Ss | s.tripulations' = s.tripulations
}

pred noTreasuresChange [Is: set Island] {
	all i : Is | i.treasures' = i.treasures
}

pred noEnemiesChange [Is: set Island] {
	all i : Is | i.enemies' = i.enemies
}

pred noCollectedTreasuresChange [Ts: set Tripulation] {
	all t : Ts | t.collectedTreasures' = t.collectedTreasures
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
	noLocationChange[Tripulation]
	noTripulationsChange[Server]
	noTreasuresChange[Island]
	noEnemiesChange[Island]
	noCollectedTreasuresChange[Tripulation]

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
	noLocationChange[Tripulation]
	noTripulationsChange[Server]
	noTreasuresChange[Island]
	noEnemiesChange[Island]
	noCollectedTreasuresChange[Tripulation]

	Track.op' = LT
}

pred tripulationLogon [sv: Server, t: Tripulation, sp: Ship, l : Location] {
	-- pre-conditions
	t not in Server.tripulations
	no t.ship
	some t.pirates
	all p : t.pirates | no p.status

	-- post-conditions
	sv.tripulations' = sv.tripulations + t
	all p : t.pirates | p.status' = Alive
	t.ship' = sp
	t.location' = l
	
	-- frame-conditions
	noStatusChange[Pirate - t.pirates]
	noPiratesChange[Tripulation]
	noShipChange[Tripulation - t]
	noLocationChange[Tripulation - t]
	noTripulationsChange[Server - sv]
	noTreasuresChange[Island]
	noEnemiesChange[Island]
	noCollectedTreasuresChange[Tripulation]

	Track.op' = TLogon
}

pred tripulationLogout [s: Server, t: Tripulation] {
	-- pre-conditions
	t in Server.tripulations
	
	-- post-conditions
	no t.pirates'
	no t.ship'
	-- no t.ship.shipLocation
	s.tripulations' = s.tripulations - t
	all p : t.pirates | no p.status'
	
	-- frame-conditions
	noStatusChange[Pirate - t.pirates]
	noPiratesChange[Tripulation - t]
	noShipChange[Tripulation - t]
	noLocationChange[Tripulation]
	noTripulationsChange[Server - s]
	noTreasuresChange[Island]
	noEnemiesChange[Island]
	noCollectedTreasuresChange[Tripulation]

	Track.op' = TLogout
}

pred arrive [t: Tripulation, l: Location] {
	-- pre-conditions
	t.location = Ocean
	l != Ocean
	-- Ensure that the tripulation is logged in
	t in Server.tripulations

	-- post-conditions
	t.location' = l

	-- frame-conditions
	noStatusChange[Pirate]
	noPiratesChange[Tripulation]
	noShipChange[Tripulation]
	noLocationChange[Tripulation - t]
	noTripulationsChange[Server]
	noTreasuresChange[Island]
	noEnemiesChange[Island]
	noCollectedTreasuresChange[Tripulation]
	
	Track.op' = ARR
}

pred depart [t: Tripulation] {
	-- pre-conditions
	some t.location
	t.location != Ocean

	-- post-conditions
	t.location' = Ocean

	-- frame-conditions
	noStatusChange[Pirate]
	noPiratesChange[Tripulation]
	noShipChange[Tripulation]
	noLocationChange[Tripulation - t]
	noTripulationsChange[Server]
	noTreasuresChange[Island]
	noEnemiesChange[Island]
	noCollectedTreasuresChange[Tripulation]

	Track.op' = DEP
}

pred collectTreasure [tp: Tripulation, ts: Treasure] {
	-- pre-conditions
	tp.location in Island
	ts in tp.location.treasures
	-- inimigos mortos?

	-- post-conditions
	tp.collectedTreasures' = tp.collectedTreasures + ts

	-- frame-conditions
	noStatusChange[Pirate]
	noPiratesChange[Tripulation]
	noShipChange[Tripulation]
	noLocationChange[Tripulation - tp]
	noTripulationsChange[Server]
	noTreasuresChange[Island]
	noEnemiesChange[Island]
	noCollectedTreasuresChange[Tripulation - tp]
}

pred sellTreasure [tp: Tripulation, ts: Treasure] {
	-- pre-conditions
	tp.location in Outpost

	-- post-conditions
	no tp.collectedTreasures'

	-- frame-conditions
	noStatusChange[Pirate]
	noPiratesChange[Tripulation]
	noShipChange[Tripulation]
	noLocationChange[Tripulation - tp]
	noTripulationsChange[Server]
	noTreasuresChange[Island]
	noEnemiesChange[Island]
	noCollectedTreasuresChange[Tripulation - tp]
}

-- pred killEnemy [] {}

-- How to model tripulation fights?

-- Stutter
pred stutter [] {
	noStatusChange[Pirate]
	noPiratesChange[Tripulation]
	noShipChange[Tripulation]
	noLocationChange[Tripulation]
	noTripulationsChange[Server]
	
	Track.op' = NOP
}

-----------------
-- Initial state
-----------------

pred init [] {
	some SoTGame.servers
	no tripulations

	no status

	no pirates
	no ship
	no location
	no collectedTreasures

	some treasures
	some enemies

	no Track.op
}

-----------------------
-- Transition relation
-----------------------

pred transition []  {
	   (some p : Pirate | some t : Tripulation | joinTripulation[p, t])
	or (some p : Pirate | some t : Tripulation | leaveTripulation[p, t])
	
	or (some sv : Server | some t : Tripulation | some sp : Ship | some l : Location | tripulationLogon[sv, t, sp, l])
	or (some sv : Server | some t : Tripulation | tripulationLogout[sv, t])

	-- Fix bug on these (logon ja estando no server dedpois do arrive)
	or (some t : Tripulation | some l : Location | arrive[t, l])
	or (some t : Tripulation | depart[t])

	-- Test this properly
	or (some tp : Tripulation | some ts : Treasure | collectTreasure[tp, ts])
	or (some tp : Tripulation | some ts : Treasure | sellTreasure[tp, ts])
	
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

run exec { System && some sv : Server | some t : Tripulation | some sp : Ship | some l : Location | eventually tripulationLogon[sv, t, sp, l] } for 5
run exec2 { System && some p : Pirate | some t : Tripulation | eventually leaveTripulation[p, t] } for 5
run exec3 { System && some sv : Server | some t : Tripulation | eventually tripulationLogout[sv, t] }
run exec4 { System && some t : Tripulation | some l : Location | eventually arrive[t, l] }
run exec5 { System && some t : Tripulation | depart[t] }

--------------
-- Properties
--------------

pred p1 {}

--------------
-- Assertions
--------------

assert a1 { System => p1 }

check a1 for 8
