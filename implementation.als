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

sig Enemy {}
-- one sig Kraken, Megalodon extends Enemy {}

sig Treasure {}

abstract sig Location {}

one sig Ocean extends Location {}
sig Island extends Location {
	var treasures: set Treasure,
	var enemies: set Enemy
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
one sig NOP, JT, LT, TLogon, TLogout, ARR, DEP, CT, ST, KE, ABE, EKP, FTD, R, FK, FM, BR, RS, SC, SS extends Operator {}
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
	always no disj e1, e2 : Enemy | some (enemies.e1 & enemies.e2)

	-- Islands do not share treasures
	always no disj t1, t2 : Treasure | some (treasures.t1 & treasures.t2)
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
	no p.status'

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

pred tripulationLogon [sv: Server, t: Tripulation, sp: Ship, l : Outpost] {
	-- pre-conditions
	t not in Server.tripulations
	no t.ship
	no ship.sp
	some t.pirates
	all p : t.pirates | no p.status
	shipRestrictions[t, sp]

	-- post-conditions
	sv.tripulations' = sv.tripulations + t
	all p : t.pirates | p.status' = Alive
	all p : t.pirates | p.hp' = 3
	t.ship' = sp
	t.location' = l
	t.money' = 0
	t.resources' = 3
	t.ship'.shipHp' = 3
	
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

pred killEnemy [i: Island, p: Pirate, e: Enemy] {
	-- pre-conditions
	p.status = Alive
	e in i.enemies
	(pirates.p).location = i
	
	-- post-conditions
	i.enemies' = i.enemies - e
	
	-- frame-conditions
	noStatusChange[Pirate]
	noPiratesChange[Tripulation]
	noShipChange[Tripulation]
	noLocationChange[Tripulation]
	noTripulationsChange[Server]
	noTreasuresChange[Island]
	noEnemiesChange[Island - i]
	noCollectedTreasuresChange[Tripulation]
	noHpChanges[Pirate]
	noMoneyChanges[Tripulation]
	noResourcesChanges[Tripulation]
	noShipHpChange[Ship]

	Track.op' = KE
}

pred attackedByEnemy [p: Pirate, e: Enemy] {
	-- pre-conditions
	p.status = Alive
	p.hp > 1
	((pirates.p).location = (enemies.e))
	
	-- post-conditions
	p.hp' = minus[p.hp, 1]
	
	-- frame-conditions
	noStatusChange[Pirate]
	noPiratesChange[Tripulation]
	noShipChange[Tripulation]
	noLocationChange[Tripulation]
	noTripulationsChange[Server]
	noTreasuresChange[Island]
	noEnemiesChange[Island]
	noCollectedTreasuresChange[Tripulation]
	noHpChanges[Pirate - p]
	noMoneyChanges[Tripulation]
	noResourcesChanges[Tripulation]
	noShipHpChange[Ship]

	Track.op' = ABE
}

pred enemyKillPirate [p: Pirate, e: Enemy] {
	-- pre-conditions
	p.status = Alive
	p.hp = 1
	((pirates.p).location = (enemies.e))
	
	-- post-conditions
	p.hp' = 0
	p.status' = Dead
	
	-- frame-conditions
	noStatusChange[Pirate - p]
	noPiratesChange[Tripulation]
	noShipChange[Tripulation]
	noLocationChange[Tripulation]
	noTripulationsChange[Server]
	noTreasuresChange[Island]
	noEnemiesChange[Island]
	noCollectedTreasuresChange[Tripulation]
	noHpChanges[Pirate - p]
	noMoneyChanges[Tripulation]
	noResourcesChanges[Tripulation]
	noShipHpChange[Ship]

	Track.op' = EKP
}

pred ferryOfTheDamned [p: Pirate] {
	-- pre-conditions
	p.status = Dead
	
	-- post-conditions
	p.status' = Otherworld
	
	-- frame-conditions
	noStatusChange[Pirate - p]
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

	Track.op' = FTD
}

pred respawn [p: Pirate] {
	-- pre-conditions
	p.status = Otherworld
	
	-- post-conditions
	p.status' = Alive
	p.hp' = 3
	
	-- frame-conditions
	noStatusChange[Pirate - p]
	noPiratesChange[Tripulation]
	noShipChange[Tripulation]
	noLocationChange[Tripulation]
	noTripulationsChange[Server]
	noTreasuresChange[Island]
	noEnemiesChange[Island]
	noCollectedTreasuresChange[Tripulation]
	noHpChanges[Pirate - p]
	noMoneyChanges[Tripulation]
	noResourcesChanges[Tripulation]
	noShipHpChange[Ship]

	Track.op' = R
}

pred collectTreasure [i: Island, tp: Tripulation, ts: Treasure] {
	-- pre-conditions
	tp.location = i
	ts in i.treasures
	no i.enemies
	some p : tp.pirates | p.status = Alive
	
	-- post-conditions
	tp.collectedTreasures' = tp.collectedTreasures + ts
	i.treasures' = i.treasures - ts
	
	-- frame-conditions
	noStatusChange[Pirate]
	noPiratesChange[Tripulation]
	noShipChange[Tripulation]
	noLocationChange[Tripulation]
	noTripulationsChange[Server]
	noTreasuresChange[Island - i]
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
	tp.money' = plus[tp.money, 1]
	
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

-- pred fightKraken [] {}

-- pred fightMegalodon [] {}

pred buyResources [tp: Tripulation] {
	-- pre-conditions
	tp.location in Outpost
	tp.money >= 1
	tp.resources < 3
	
	-- post-conditions
	tp.money' = minus[tp.money, 1]
	tp.resources' = plus[tp.resources, 1]

	-- frame-conditions
	noStatusChange[Pirate]
	noPiratesChange[Tripulation]
	noShipChange[Tripulation]
	noLocationChange[Tripulation]
	noTripulationsChange[Server]
	noTreasuresChange[Island]
	noEnemiesChange[Island]
	noCollectedTreasuresChange[Tripulation]
	noHpChanges[Pirate]
	noMoneyChanges[Tripulation - tp]
	noResourcesChanges[Tripulation - tp]
	noShipHpChange[Ship]

	Track.op' = BR
}

pred shipCollision [tp: Tripulation] {
	-- pre-conditions
	tp.location = Ocean
	tp.ship.shipHp > 1
	
	-- post-conditions
	tp.ship.shipHp' = minus[tp.ship.shipHp, 1]

	-- frame-conditions
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
	noShipHpChange[Ship - tp.ship]
	
	Track.op' = SC
}

pred repairShip [tp: Tripulation] {
	-- pre-conditions
	tp.ship.shipHp < 3
	tp.resources >= 1
	
	-- post-conditions
	tp.ship.shipHp' = plus[tp.ship.shipHp, 1]
	tp.resources' = minus[tp.resources, 1]

	-- frame-conditions
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
	noResourcesChanges[Tripulation - tp]
	noShipHpChange[Ship - tp.ship]
	
	Track.op' = RS
}

pred sinkShip [tp: Tripulation] {
	-- pre-conditions
	tp.location = Ocean
	tp.ship.shipHp = 1
	
	-- post-conditions
	

	-- frame-conditions
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
	
	Track.op' = SS
}

-- Model tripulation fights

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
	
	or (some sv : Server | some t : Tripulation | some sp : Ship | some l : Outpost | tripulationLogon[sv, t, sp, l])
	or (some sv : Server | some t : Tripulation | tripulationLogout[sv, t])

	or (some t : Tripulation | some l : Location | arrive[t, l])
	or (some t : Tripulation | depart[t])

	or (some i : Island | some tp : Tripulation | some ts : Treasure | collectTreasure[i, tp, ts])
	or (some tp : Tripulation | some ts : Treasure | sellTreasure[tp, ts])
	
	or (some i : Island | some p : Pirate | some e : Enemy | killEnemy[i, p, e])
	or (some p : Pirate | some e : Enemy | attackedByEnemy [p, e])
	or (some p : Pirate | some e : Enemy | enemyKillPirate [p, e])
	or (some p : Pirate | ferryOfTheDamned [p])
	or (some p : Pirate | respawn [p])

	or (some tp : Tripulation | buyResources [tp])
	or (some tp : Tripulation | shipCollision[tp])
	or (some tp : Tripulation | repairShip[tp])

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

run exec { System && some sv : Server | some t : Tripulation | some sp : Ship | some l : Outpost | eventually tripulationLogon[sv, t, sp, l] } for 5
run exec2 { System && some p : Pirate | some t : Tripulation | eventually leaveTripulation[p, t] } for 5
run exec3 { System && some sv : Server | some t : Tripulation | eventually tripulationLogout[sv, t] } for 5

run exec4 { System && some t : Tripulation | some l : Location | eventually arrive[t, l] } for 5
run exec5 { System && some t : Tripulation | eventually depart[t] } for 5

run exec6 { System && some i : Island | some tp : Tripulation | some ts : Treasure | eventually collectTreasure[i, tp, ts] } for 5
run exec7 { System && some tp : Tripulation | some ts : Treasure | eventually sellTreasure[tp, ts] } for 5

run exec8 { System && some i : Island | some p : Pirate | some e : Enemy | eventually killEnemy[i, p, e] } for 5
run exec9 { System && some p : Pirate | some e : Enemy | eventually attackedByEnemy[p, e] } for 5
run exec10 { System && some p : Pirate | some e : Enemy | eventually enemyKillPirate[p, e] } for 5
run exec11 { System && some p : Pirate | eventually respawn[p] } for 5

run exec12 { System && some tp : Tripulation | eventually shipCollision[tp] } for 5
run exec13 { System && some tp : Tripulation | eventually buyResources[tp] } for 15 steps
run exec14 { System && some tp : Tripulation | eventually repairShip[tp] } for 15 steps

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
