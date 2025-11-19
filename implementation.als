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

open util/integer

--------------
-- Signatures
--------------

sig Enemie {}

sig Treasure {}

abstract sig Location {}

one sig Ocean extends Location {}
sig Island extends Location {
	var treasures: set Treasure,
	var enemies: set Enemie
}
sig Outpost extends Location {}

-- one sig list_islands_subset extends Island {}
-- one sig list_outposts_subset extends Outpost {}

abstract sig Ship {
	var shipHp: lone Int
}
sig Sloop, Brigantine, Galleon extends Ship {}

abstract sig PirateStatus {}
one sig Dead, Alive, Otherworld extends PirateStatus {}

sig Pirate {
	var hp: lone Int,
	var status: lone PirateStatus
}

sig Tripulation {
	var pirates: set Pirate,
	var ship: lone Ship,
	var location: lone Location,
	var collectedTreasures: set Treasure,
	var money: lone Int,
	var resources: lone Int
}

sig Server {
	var tripulations: set Tripulation
}

one sig SoTGame {
	servers: set Server
}

-- Track operators during execution
abstract sig Operator {}
one sig NOP, JT, LT, TLogon, TLogout, ARR, DEP, CT, ST extends Operator {}
one sig Track {
	var op: lone Operator
}

---------
-- Facts
---------

fact {
	-- All servers are attached to SoTGame instance
	always no s : Server | s not in SoTGame.servers
	
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

pred noHpChanges [Ps: set Pirate] {
	all p : Ps | p.hp' = p.hp
}

pred noMoneyChanges [Ts: set Tripulation] {
	all t : Ts | t.money' = t.money
}

pred noResourcesChanges [Ts: set Tripulation] {
	all t : Ts | t.resources' = t.resources
}

pred noShipHpChange [Ss: set Ship] {
	all s : Ss | s.shipHp' = s.shipHp
}

-----------------------
-- Auxiliar predicates
-----------------------

pred shipRestrictions [t: Tripulation, sp: Ship] {
	let sz = #t.pirates |
		sp in (
			sz = 1 implies Sloop + Brigantine + Galleon
			else sz = 2 implies Brigantine + Galleon
			else Galleon)
}

-------------
-- Operators
-------------

pred joinTripulation [p: Pirate, t: Tripulation] {
	-- pre-conditions
	p not in Tripulation.pirates
	no p.status
	#t.pirates <= 3
	t not in Server.tripulations

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
	noHpChanges[Pirate]
	noMoneyChanges[Tripulation]
	noResourcesChanges[Tripulation]
	noShipHpChange[Ship]

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
	noHpChanges[Pirate]
	noMoneyChanges[Tripulation]
	noResourcesChanges[Tripulation]
	noShipHpChange[Ship]

	Track.op' = LT
}

pred tripulationLogon [sv: Server, t: Tripulation, sp: Ship, l : Location] {
	-- pre-conditions
	t not in Server.tripulations
	no t.ship
	no ship.sp
	some t.pirates
	all p : t.pirates | no p.status
	shipRestrictions[t, sp]
	l in Outpost

	-- post-conditions
	sv.tripulations' = sv.tripulations + t
	all p : t.pirates | p.status' = Alive
	all p : t.pirates | p.hp' = 3
	t.ship' = sp
	t.location' = l
	t.money' = 0
	t.resources' = 5
	t.ship'.shipHp' = 5
	
	-- frame-conditions
	noStatusChange[Pirate - t.pirates]
	noPiratesChange[Tripulation]
	noShipChange[Tripulation - t]
	noLocationChange[Tripulation - t]
	noTripulationsChange[Server - sv]
	noTreasuresChange[Island]
	noEnemiesChange[Island]
	noCollectedTreasuresChange[Tripulation]
	noHpChanges[Pirate - t.pirates]
	noMoneyChanges[Tripulation - t]
	noResourcesChanges[Tripulation - t]
	noShipHpChange[Ship - sp]

	Track.op' = TLogon
}

pred tripulationLogout [s: Server, t: Tripulation] {
	-- pre-conditions
	t in s.tripulations
	
	-- post-conditions
	no t.pirates'
	no t.ship'
	no t.location'
	no money'
	no resources'
	s.tripulations' = s.tripulations - t
	all p : t.pirates | no p.status'
	all p : t.pirates | no p.hp'
	
	-- frame-conditions
	noStatusChange[Pirate - t.pirates]
	noPiratesChange[Tripulation - t]
	noShipChange[Tripulation - t]
	noLocationChange[Tripulation - t]
	noTripulationsChange[Server - s]
	noTreasuresChange[Island]
	noEnemiesChange[Island]
	noCollectedTreasuresChange[Tripulation]
	noHpChanges[Pirate]
	noMoneyChanges[Tripulation]
	noResourcesChanges[Tripulation]
	noShipHpChange[Ship]

	Track.op' = TLogout
}

pred arrive [t: Tripulation, l: Location] {
	-- pre-conditions
	t.location = Ocean
	l != Ocean

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
	noHpChanges[Pirate]
	noMoneyChanges[Tripulation]
	noResourcesChanges[Tripulation]
	noShipHpChange[Ship]
	
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
	noHpChanges[Pirate]
	noMoneyChanges[Tripulation]
	noResourcesChanges[Tripulation]
	noShipHpChange[Ship]

	Track.op' = DEP
}

pred collectTreasure [tp: Tripulation, ts: Treasure] {
	-- pre-conditions
	tp.location in Island
	ts in tp.location.treasures
	no tp.location.enemies

	-- post-conditions
	tp.collectedTreasures' = tp.collectedTreasures + ts
	tp.location.treasures' = tp.location.treasures - ts

	-- frame-conditions
	noStatusChange[Pirate]
	noPiratesChange[Tripulation]
	noShipChange[Tripulation]
	noLocationChange[Tripulation]
	noTripulationsChange[Server]
	noTreasuresChange[Island - tp.location]
	noEnemiesChange[Island]
	noCollectedTreasuresChange[Tripulation - tp]
	noHpChanges[Pirate]
	noMoneyChanges[Tripulation]
	noResourcesChanges[Tripulation]
	noShipHpChange[Ship]

	Track.op' = CT
}

pred sellTreasure [tp: Tripulation, ts: Treasure] {
	-- pre-conditions
	tp.location in Outpost
	ts in tp.collectedTreasures

	-- post-conditions
	tp.collectedTreasures' = tp.collectedTreasures - ts
	tp.money' = tp.money + 1

	-- frame-conditions
	noStatusChange[Pirate]
	noPiratesChange[Tripulation]
	noShipChange[Tripulation]
	noLocationChange[Tripulation]
	noTripulationsChange[Server]
	noTreasuresChange[Island]
	noEnemiesChange[Island]
	noCollectedTreasuresChange[Tripulation - tp]
	noHpChanges[Pirate]
	noMoneyChanges[Tripulation - tp]
	noResourcesChanges[Tripulation]
	noShipHpChange[Ship]

	Track.op' = ST
}

pred buyResources [] {}

pred useResources [] {}

pred sinkShip [] {}

-- pred killEnemy [] {}

-- How to model tripulation fights?

-- Stutter
pred stutter [] {
	noStatusChange[Pirate]
	noPiratesChange[Tripulation]
	noShipChange[Tripulation]
	noLocationChange[Tripulation]
	noTripulationsChange[Server]
	noTreasuresChange[Island]
	noEnemiesChange[Island]
	noCollectedTreasuresChange[Tripulation]
	noHpChanges[Pirate]
	noMoneyChanges[Tripulation]
	noResourcesChanges[Tripulation]
	noShipHpChange[Ship]
	
	Track.op' = NOP
}

-----------------
-- Initial state
-----------------

pred init [] {
	some SoTGame.servers
	no tripulations

	no hp
	no status

	no pirates
	no ship
	no location
	no collectedTreasures
	no money
	no resources

	no shipHp

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

	or (some t : Tripulation | some l : Location | arrive[t, l])
	or (some t : Tripulation | depart[t])

	-- Check bug on collectTreasure and sellTreasure
	-- or (some tp : Tripulation | some ts : Treasure | collectTreasure[tp, ts])
	-- or (some tp : Tripulation | some ts : Treasure | sellTreasure[tp, ts])
	
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
run exec3 { System && some sv : Server | some t : Tripulation | eventually tripulationLogout[sv, t] } for 5

run exec4 { System && some t : Tripulation | some l : Location | eventually arrive[t, l] } for 5
run exec5 { System && some t : Tripulation | eventually depart[t] } for 5

run exec6 { System && some tp : Tripulation | some ts : Treasure | eventually collectTreasure[tp, ts] } for 5
-- run exec7 { System && some tp : Tripulation | some ts : Treasure | eventually sellTreasure[tp, ts] } for 5

--------------
-- Properties
--------------

-- Todos os servers estao vinculados a instancia do Game
pred p1 {
	always no s : Server | s not in SoTGame.servers
}

-- Nenhuma tripulacao vazia logada no server
pred p2 {
	always no t : Tripulation | #t.pirates = 0 and t in Server.tripulations
}

-- Nenhuma tripulacao compartilha piratas
pred p3 {
	always no disj t1, t2 : Tripulation | some (t1.pirates & t2.pirates)
}

-- Nenhuma tripulacao compartilha o mesmo barco
pred p4 {
	always no disj t1, t2 : Tripulation | some t1.ship and some t2.ship and t1.ship = t2.ship
}

-- Nenhuma tripulacao com navios invalidos
pred p5 {
	always no t : Tripulation |
		(#t.pirates > 1 and t.ship = Sloop) or (#t.pirates > 2 and t.ship = Brigantine)
}

-- Tripulacao sempre spawna num outpost

-- Impossivel fazer um depart para uma ilha

-- Impossivel fazer um arrive para o mar

-- Nenhum tesouro eh compartilhado em ilhas diferentes
pred p8 {
	always no disj i1, i2 : Island | some (i1.treasures & i2.treasures) 
}

-- Nenhum tesouro eh compartilhado por tripulacoes diferentes
pred p9 {
	always no disj t1, t2 : Tripulation | some (t1.collectedTreasures & t2.collectedTreasures) 
}

-- Nenhum tesouro eh compartilhado por uma ilha e uma tripulacao ao mesmo tempo
pred p10 {
	always no t : Tripulation, i : Island | some (t.collectedTreasures & i.treasures) 
}

--------------
-- Assertions
--------------

assert a1 { System => p1 }
assert a2 { System => p2 }
assert a3 { System => p3 }
assert a4 { System => p4 }
assert a5 { System => p5 }
assert a8 { System => p8 }
assert a9 { System => p9 }
assert a10 { System => p10 }

check a1 for 5
check a2 for 5
check a3 for 5
check a4 for 5
check a5 for 5
check a8 for 5
check a9 for 5
check a10 for 5
