from collections import defaultdict, deque
import random
from typing import Optional, Tuple, Union, cast
from risk_helper.game import Game
from risk_shared.models.card_model import CardModel
from risk_shared.queries.query_attack import QueryAttack
from risk_shared.queries.query_claim_territory import QueryClaimTerritory
from risk_shared.queries.query_defend import QueryDefend
from risk_shared.queries.query_distribute_troops import QueryDistributeTroops
from risk_shared.queries.query_fortify import QueryFortify
from risk_shared.queries.query_place_initial_troop import QueryPlaceInitialTroop
from risk_shared.queries.query_redeem_cards import QueryRedeemCards
from risk_shared.queries.query_troops_after_attack import QueryTroopsAfterAttack
from risk_shared.queries.query_type import QueryType
from risk_shared.records.moves.move_attack import MoveAttack
from risk_shared.records.moves.move_attack_pass import MoveAttackPass
from risk_shared.records.moves.move_claim_territory import MoveClaimTerritory
from risk_shared.records.moves.move_defend import MoveDefend
from risk_shared.records.moves.move_distribute_troops import MoveDistributeTroops
from risk_shared.records.moves.move_fortify import MoveFortify
from risk_shared.records.moves.move_fortify_pass import MoveFortifyPass
from risk_shared.records.moves.move_place_initial_troop import MovePlaceInitialTroop
from risk_shared.records.moves.move_redeem_cards import MoveRedeemCards
from risk_shared.records.moves.move_troops_after_attack import MoveTroopsAfterAttack
from risk_shared.records.record_attack import RecordAttack
from risk_shared.records.types.move_type import MoveType


twodice = [[0]*6 for i in range(6)]
threedice = [[0]*6 for i in range(6)]

# get number of ways to have two dice with particular values,
# as well as three dice where the highest 2 have particular values
for i in range(6):
    for j in range(6):
        twodice[min(i,j)][max(i,j)] += 1
        for k in range(6):
            ordered = sorted([i,j,k])
            threedice[ordered[1]][ordered[2]] += 1

total2dice = sum(sum(arr) for arr in twodice)
total3dice = sum(sum(arr) for arr in threedice)

flawless3v2 = 0 # probability of attacker rolling 3 dice against 2 and losing no pieces
flawless2v2 = 0 # probability of attacker rolling 2 dice against 2 and losing no pieces
for h in range(5):
    for i in range(h,5):
        # prob of defender rolling rolling h and i
        # we divide by attacker sample space now to avoid doing it repeatedly later
        temp3v2 = float(twodice[h][i])/(total2dice*total3dice)
        temp2v2 = float(twodice[h][i])/(total2dice*total2dice)
        for j in range(h+1,6):
            for k in range(i+1,6):
                # going through all ways attacker can defeat two armies
                # without losing anybody in the process.
                flawless3v2 += temp3v2*threedice[j][k]
                flawless2v2 += temp2v2*twodice[j][k]

flawed3v2 = 0 # probability of attacker rolling 3v2 and each losing 1 piece
flawed2v2 = 0 # probability of attacker rolling 2v2 and each losing 1 piece
for h in range(5):
    for i in range(h,6):
        # prob of defender rolling h and i
        # once again we factor out division of attacker sample space
        temp3v2 = float(twodice[h][i])/(total2dice*total3dice)
        temp2v2 = float(twodice[h][i])/(total2dice*total2dice)
        for j in range(h+1,6):
            for k in range(j,i+1):
                # attacker defeats low die but loses to high die
                flawed3v2 += temp3v2*threedice[j][k]
                flawed2v2 += temp2v2*twodice[j][k]
        if i==5: continue # attacker cannot beat high die
        for j in range(h+1):
            for k in range(i+1,6):
                # attacker defeats high die but loses to low die
                flawed3v2 += temp3v2*threedice[j][k]
                flawed2v2 += temp2v2*twodice[j][k]

fatal3v2 = 1-flawless3v2-flawed3v2 # attacker loses two when rolling 3
fatal2v2 = 1-flawless2v2-flawed2v2 # attacker loses two when rolling 2

flawless1v2 = 0 # probability of attacker rolling 1 die and winning against 2 dice
for i in range(5):
    for j in range(i,5):
        # prob of defender rolling i and j
        # factor out division by six (attacker sample space)
        temp1v2 = float(twodice[i][j])/(total2dice*6)
        for k in range(j+1,6):
            flawless1v2 += temp1v2

fatal1v2 = 1-flawless1v2 # probability of attacker rolling 1v2 and losing

flawless3v1 = 0 # probability of attacker rolling 3v1 and winning
flawless2v1 = 0 # probability of attacker rolling 2v1 and winning
for i in range(5):
    temp3v1 = 1.0/(6*total3dice)
    temp2v1 = 1.0/(6*total2dice)
    for j in range(6):
        for k in range(max(j,i+1),6):
            flawless3v1 += temp3v1*threedice[j][k]
            flawless2v1 += temp2v1*twodice[j][k]

fatal3v1 = 1-flawless3v1 # probability of attacker rolling 3v1 and losing
fatal2v1 = 1-flawless2v1 # probabiliyy of attacker rolling 2v1 and losing


flawless1v1 = 0 # prob of attacker rolling 1v1 and winning
for i in range(5):
    for j in range(i+1,6):
        flawless1v1 += 1.0/36

fatal1v1 = 1-flawless1v1

# probs[x][y][z] means probability of attacker using x dice vs y dice with outcome z
# (z=0 is a win, z=1 is a tie, z=2 is a loss)
probs = [0, [0, [flawless1v1,0.0,fatal1v1], [flawless1v2,0.0,fatal1v2]],
            [0, [flawless2v1,0.0,fatal2v1], [flawless2v2,flawed2v2,fatal2v2]],
            [0, [flawless3v1,0.0,fatal3v1], [flawless3v2,flawed3v2,fatal3v2]]]
bmem = {}
omem = {}
tmem = {}

# Finds probability that army of size attackers will
# defeat army of size defenders with at least minleft troops left.
# Less general than outcomeprob.
def battleprob(attackers, defenders, minleft=1):
    if attackers < minleft: return 0.0
    if defenders == 0: return 1.0

    h = (attackers, defenders, minleft)
    if h in bmem: return bmem[h]

    val = 0.0
    if attackers >= 3 and defenders >= 2:
        val = probs[3][2][0]*battleprob(attackers, defenders-2, minleft) + \
              probs[3][2][1]*battleprob(attackers-1, defenders-1, minleft) + \
              probs[3][2][2]*battleprob(attackers-2, defenders, minleft)
    elif attackers >= 3 and defenders == 1:
        val = probs[3][1][0] + \
              probs[3][1][2]*battleprob(attackers-1, defenders, minleft)
    elif attackers == 2 and defenders >= 2:
        val = probs[2][2][0]*battleprob(attackers, defenders-2, minleft) + \
              probs[2][2][1]*battleprob(attackers-1, defenders-1, minleft) + \
              probs[2][2][2]*battleprob(attackers-2, defenders, minleft)
    elif attackers == 2 and defenders == 1:
        val = probs[2][1][0] + \
              probs[2][1][2]*battleprob(attackers-1, defenders, minleft)
    elif attackers == 1 and defenders >= 2:
        val = probs[1][2][0]*battleprob(attackers, defenders-1, minleft)
    elif attackers == 1 and defenders == 1:
        val = probs[1][1][0]

    bmem[h] = val
    return val

# Finds probability that an army of size attackers
# battling an army of size defenders will result in
# arem attackers and drem attackers remaining on either side.
def outcomeprob(attackers, defenders, arem=1, drem=0):
    if attackers < arem or defenders < drem: return 0.0
    if defenders == drem:
        if drem == 0 and attackers != arem: return 0.0
        if attackers == arem: return 1.0

    h = (attackers, defenders, arem, drem)
    if h in omem: return omem[h]

    val = 0.0
    if attackers >= 3 and defenders >= 2:
        val = probs[3][2][0]*outcomeprob(attackers, defenders-2, arem, drem) + \
              probs[3][2][1]*outcomeprob(attackers-1, defenders-1, arem, drem) + \
              probs[3][2][2]*outcomeprob(attackers-2, defenders, arem, drem)
    elif attackers >= 3 and defenders == 1:
        val = probs[3][1][0]*outcomeprob(attackers, defenders-1, arem, drem) + \
              probs[3][1][2]*outcomeprob(attackers-1, defenders, arem, drem)
    elif attackers == 2 and defenders >= 2:
        val = probs[2][2][0]*outcomeprob(attackers, defenders-2, arem, drem) + \
              probs[2][2][1]*outcomeprob(attackers-1, defenders-1, arem, drem) + \
              probs[2][2][2]*outcomeprob(attackers-2, defenders, arem, drem)
    elif attackers == 2 and defenders == 1:
        val = probs[2][1][0]*outcomeprob(attackers, defenders-1, arem, drem) + \
              probs[2][1][2]*outcomeprob(attackers-1, defenders, arem, drem)
    elif attackers == 1 and defenders >= 2:
        val = probs[1][2][0]*outcomeprob(attackers, defenders-1, arem, drem)
    elif attackers == 1 and defenders == 1:
        val = probs[1][1][0]*outcomeprob(attackers, defenders-1, arem, drem)

    omem[h] = val
    return val

# Finds probability of successful tour given:
# a starting army of size attackers,
# an array of armies darmies representing the defending armies in the order they will be attacked,
# which defending army is being attacked (default 0 for the start),
# the number of troops we want to leave behind at each country (default 1 for each country),
# number of guys we want to leave behind in each country
def tourprob(attackers, darmies, tindex=0, fortify=([1]*100)):
    if tindex == len(darmies): return 1.0
    if tindex == 0: # reset memoize table
        global tmem
        tmem = {}

    h = (attackers, tindex)
    if h in tmem: return tmem[h]

    army = attackers-fortify[tindex]
    minremaining = sum(fortify[i] for i in range(tindex+1,len(darmies)+1))

    val = 0.0
    for i in range(minremaining, army+1):
        val += outcomeprob(army, darmies[tindex], i)*tourprob(i, darmies, tindex+1, fortify)

    tmem[h] = val
    return val

# We will store our enemy in the bot state.
class BotState():
    def __init__(self):
        self.enemy: Optional[int] = None


def main():
    
    # Get the game object, which will connect you to the engine and
    # track the state of the game.
    game = Game()
    bot_state = BotState()
   
    # Respond to the engine's queries with your moves.
    while True:

        # Get the engine's query (this will block until you receive a query).
        query = game.get_next_query()

        # Based on the type of query, respond with the correct move.
        def choose_move(query: QueryType) -> MoveType:
            match query:
                case QueryClaimTerritory() as q:
                    return handle_claim_territory(game, bot_state, q)

                case QueryPlaceInitialTroop() as q:
                    return handle_place_initial_troop(game, bot_state, q)

                case QueryRedeemCards() as q:
                    return handle_redeem_cards(game, bot_state, q)

                case QueryDistributeTroops() as q:
                    return handle_distribute_troops(game, bot_state, q)

                case QueryAttack() as q:
                    return handle_attack(game, bot_state, q)

                case QueryTroopsAfterAttack() as q:
                    return handle_troops_after_attack(game, bot_state, q)

                case QueryDefend() as q:
                    return handle_defend(game, bot_state, q)

                case QueryFortify() as q:
                    return handle_fortify(game, bot_state, q)
        
        # Send the move to the engine.
        game.send_move(choose_move(query))
                

def handle_claim_territory(game: Game, bot_state: BotState, query: QueryClaimTerritory) -> MoveClaimTerritory:
    """At the start of the game, you can claim a single unclaimed territory every turn 
    until all the territories have been claimed by players."""

    unclaimed_territories = game.state.get_territories_owned_by(None)
    my_territories = game.state.get_territories_owned_by(game.state.me.player_id)

    # We will try to always pick new territories that are next to ones that we own,
    # or a random one if that isn't possible.
    adjacent_territories = game.state.get_all_adjacent_territories(my_territories)

    # We can only pick from territories that are unclaimed and adjacent to us.
    available = list(set(unclaimed_territories) & set(adjacent_territories))
    if len(available) != 0:

        # We will pick the one with the most connections to our territories
        # this should make our territories clustered together a little bit.
        def count_adjacent_friendly(x: int) -> int:
            return len(set(my_territories) & set(game.state.map.get_adjacent_to(x)))

        selected_territory = sorted(available, key=lambda x: count_adjacent_friendly(x), reverse=True)[0]
    
    # Or if there are no such territories, we will pick just an unclaimed one with the greatest number of adjacent unclaimed territories.
    else:
        selected_territory = sorted(unclaimed_territories, key=lambda x: len([territory for territory in game.state.map.get_adjacent_to(x) if game.state.get_territories_owned_by(None)]), reverse=True)[0]

    return game.move_claim_territory(query, selected_territory)


def handle_place_initial_troop(game: Game, bot_state: BotState, query: QueryPlaceInitialTroop) -> MovePlaceInitialTroop:
    """After all the territories have been claimed, you can place a single troop on one
    of your territories each turn until each player runs out of troops."""
    
    # We will place troops along the territories on our border.
    border_territories = game.state.get_all_border_territories(
        game.state.get_territories_owned_by(game.state.me.player_id)
    )

    # We will place a troop in the border territory with the least troops currently
    # on it. This should give us close to an equal distribution.
    border_territory_models = [game.state.territories[x] for x in border_territories]
    min_troops_territory = min(border_territory_models, key=lambda x: x.troops)

    return game.move_place_initial_troop(query, min_troops_territory.territory_id)


def handle_redeem_cards(game: Game, bot_state: BotState, query: QueryRedeemCards) -> MoveRedeemCards:
    """After the claiming and placing initial troops phases are over, you can redeem any
    cards you have at the start of each turn, or after killing another player."""

    # We will always redeem the minimum number of card sets we can until the 12th card set has been redeemed.
    # This is just an arbitrary choice to try and save our cards for the late game.

    # We always have to redeem enough cards to reduce our card count below five.
    card_sets: list[Tuple[CardModel, CardModel, CardModel]] = []
    cards_remaining = game.state.me.cards.copy()

    while len(cards_remaining) >= 5:
        card_set = game.state.get_card_set(cards_remaining)
        # According to the pigeonhole principle, we should always be able to make a set
        # of cards if we have at least 5 cards.
        assert card_set != None
        card_sets.append(card_set)
        cards_remaining = [card for card in cards_remaining if card not in card_set]

    # Remember we can't redeem any more than the required number of card sets if 
    # we have just eliminated a player.
    if game.state.card_sets_redeemed > 12 and query.cause == "turn_started":
        card_set = game.state.get_card_set(cards_remaining)
        while card_set != None:
            card_sets.append(card_set)
            cards_remaining = [card for card in cards_remaining if card not in card_set]
            card_set = game.state.get_card_set(cards_remaining)

    return game.move_redeem_cards(query, [(x[0].card_id, x[1].card_id, x[2].card_id) for x in card_sets])


def handle_distribute_troops(game: Game, bot_state: BotState, query: QueryDistributeTroops) -> MoveDistributeTroops:
    """After you redeem cards (you may have chosen to not redeem any), you need to distribute
    all the troops you have available across your territories. This can happen at the start of
    your turn or after killing another player.
    """

    # We will distribute troops across our border territories.
    total_troops = game.state.me.troops_remaining
    distributions = defaultdict(lambda: 0)
    border_territories = game.state.get_all_border_territories(
        game.state.get_territories_owned_by(game.state.me.player_id)
    )

    # We need to remember we have to place our matching territory bonus
    # if we have one.
    if len(game.state.me.must_place_territory_bonus) != 0:
        assert total_troops >= 2
        distributions[game.state.me.must_place_territory_bonus[0]] += 2
        total_troops -= 2


    # We will equally distribute across border territories in the early game,
    # but start doomstacking in the late game.
    if len(game.state.recording) < 4000:
        troops_per_territory = total_troops // len(border_territories)
        leftover_troops = total_troops % len(border_territories)
        for territory in border_territories:
            distributions[territory] += troops_per_territory
    
        # The leftover troops will be put some territory (we don't care)
        distributions[border_territories[0]] += leftover_troops
    
    else:
        my_territories = game.state.get_territories_owned_by(game.state.me.player_id)
        weakest_players = sorted(game.state.players.values(), key=lambda x: sum(
            [game.state.territories[y].troops for y in game.state.get_territories_owned_by(x.player_id)]
        ))

        for player in weakest_players:
            bordering_enemy_territories = set(game.state.get_all_adjacent_territories(my_territories)) & set(game.state.get_territories_owned_by(player.player_id))
            if len(bordering_enemy_territories) > 0:
                selected_territory = list(set(game.state.map.get_adjacent_to(list(bordering_enemy_territories)[0])) & set(my_territories))[0]
                distributions[selected_territory] += total_troops
                break


    return game.move_distribute_troops(query, distributions)


def handle_attack(game: Game, bot_state: BotState, query: QueryAttack) -> Union[MoveAttack, MoveAttackPass]:
    """After the troop phase of your turn, you may attack any number of times until you decide to
    stop attacking (by passing). After a successful attack, you may move troops into the conquered
    territory. If you eliminated a player you will get a move to redeem cards and then distribute troops."""
    
    # We will attack someone.
    my_territories = game.state.get_territories_owned_by(game.state.me.player_id)
    bordering_territories = game.state.get_all_adjacent_territories(my_territories)

    def attack_weakest(territories: list[int]) -> Optional[MoveAttack]:
        # We will attack the weakest territory from the list.
        territories = sorted(territories, key=lambda x: game.state.territories[x].troops)
        for candidate_target in territories:
            candidate_attackers = sorted(list(set(game.state.map.get_adjacent_to(candidate_target)) & set(my_territories)), key=lambda x: game.state.territories[x].troops, reverse=True)
            for candidate_attacker in candidate_attackers:
                my_troops = game.state.territories[candidate_attacker].troops
                target_troops = game.state.territories[candidate_target].troops
                # For smaller armies, calculate out our odds or winning
                if my_troops <= 100 and target_troops <= 100 and my_troops > 1:
                    if tourprob(my_troops, [target_troops]) > 0.5:
                        return game.move_attack(query, candidate_attacker, candidate_target, min(3, game.state.territories[candidate_attacker].troops - 1))
                
                # Otherwise Unless there's a difference of over 15, we're more likely to win, so hit it
                elif my_troops - target_troops > 15:
                    return game.move_attack(query, candidate_attacker, candidate_target, min(3, game.state.territories[candidate_attacker].troops - 1))

    if len(game.state.recording) < 4000:
        # We will pick the player with the weakest territory bordering us, and make them our enemy.
        weakest_territory = min(bordering_territories, key=lambda x: game.state.territories[x].troops)
        bot_state.enemy = game.state.territories[weakest_territory].occupier
        
        # Get all territories owned by opponents
        all_territories = [y.territory_id for y in game.state.territories.values()]
        enemy_territories = set(all_territories).difference(my_territories)

        # We will attack their weakest territory that gives us a favourable battle if possible.
        enemy_territories = list(set(bordering_territories) & enemy_territories)
        move = attack_weakest(enemy_territories)
        if move != None:
            return move

    # In the late game, we will attack anyone adjacent to our strongest territories (hopefully our doomstack).
    else:
        strongest_territories = sorted(my_territories, key=lambda x: game.state.territories[x].troops, reverse=True)
        for territory in strongest_territories:
            move = attack_weakest(list(set(game.state.map.get_adjacent_to(territory)) - set(my_territories)))
            if move != None:
                return move

    return game.move_attack_pass(query)


def handle_troops_after_attack(game: Game, bot_state: BotState, query: QueryTroopsAfterAttack) -> MoveTroopsAfterAttack:
    """After conquering a territory in an attack, you must move troops to the new territory."""
    
    # First we need to get the record that describes the attack, and then the move that specifies
    # which territory was the attacking territory.
    record_attack = cast(RecordAttack, game.state.recording[query.record_attack_id])
    move_attack = cast(MoveAttack, game.state.recording[record_attack.move_attack_id])
    conquered_territory = move_attack.defending_territory
    attacking_territory = game.state.territories[move_attack.attacking_territory]

    # Only move the max number of troops if the attacking territory was a border
    is_border = len(set(game.state.map.get_adjacent_to(conquered_territory)) - set(game.state.territories)) != 0 
    if is_border: 
        return game.move_troops_after_attack(query, game.state.territories[move_attack.attacking_territory].troops - 1)

    else: 
        return game.move_troops_after_attack(query, move_attack.attacking_troops)


def handle_defend(game: Game, bot_state: BotState, query: QueryDefend) -> MoveDefend:
    """If you are being attacked by another player, you must choose how many troops to defend with."""

    # We will always defend with the most troops that we can.

    # First we need to get the record that describes the attack we are defending against.
    move_attack = cast(MoveAttack, game.state.recording[query.move_attack_id])
    defending_territory = move_attack.defending_territory
    
    # We can only defend with up to 2 troops, and no more than we have stationed on the defending
    # territory.
    defending_troops = min(game.state.territories[defending_territory].troops, 2)
    return game.move_defend(query, defending_troops)


def handle_fortify(game: Game, bot_state: BotState, query: QueryFortify) -> Union[MoveFortify, MoveFortifyPass]:
    """At the end of your turn, after you have finished attacking, you may move a number of troops between
    any two of your territories (they must be adjacent)."""
    # We will always fortify towards the most powerful player (player with most troops on the map) to defend against them.
    my_territories = game.state.get_territories_owned_by(game.state.me.player_id)
    total_troops_per_player = {}
    for player in game.state.players.values():
        total_troops_per_player[player.player_id] = sum([game.state.territories[x].troops for x in game.state.get_territories_owned_by(player.player_id)])

    most_powerful_player = max(total_troops_per_player.items(), key=lambda x: x[1])[0]

    # If we are the most powerful, we will pass.
    if most_powerful_player == game.state.me.player_id:
        return game.move_fortify_pass(query)
    
    # Otherwise we will find the shortest path between our territory with the most troops
    # and any of the most powerful player's territories and fortify along that path.
    candidate_territories = game.state.get_all_border_territories(my_territories)
    most_troops_territory = max(candidate_territories, key=lambda x: game.state.territories[x].troops)
    weakest_borders = sorted(candidate_territories, key= lambda x: game.state.territories[x].troops)

    # Fortify towards the weakest border 
    shortest_path = find_shortest_path_from_vertex_to_set(game, most_troops_territory, set(weakest_borders))
    # We will move our troops along this path (we can only move one step, and we have to leave one troop behind).
    # We have to check that we can move any troops though, if we can't then we will pass our turn.
    if len(shortest_path) > 0 and game.state.territories[most_troops_territory].troops > 1:
        return game.move_fortify(query, shortest_path[0], shortest_path[1], game.state.territories[most_troops_territory].troops - 1)
    else:
        return game.move_fortify_pass(query)


def find_shortest_path_from_vertex_to_set(game: Game, source: int, target_set: set[int]) -> list[int]:
    """Used in move_fortify()."""

    # We perform a BFS search from our source vertex, stopping at the first member of the target_set we find.
    queue = deque()
    queue.appendleft(source)

    current = queue.pop()
    parent = {}
    seen = {current: True}

    while len(queue) != 0:
        if current in target_set:
            break

        for neighbour in game.state.map.get_adjacent_to(current):
            if neighbour not in seen:
                seen[neighbour] = True
                parent[neighbour] = current
                queue.appendleft(neighbour)

        current = queue.pop()

    path = []
    while current in parent:
        path.append(current)
        current = parent[current]

    return path[::-1]

if __name__ == "__main__":
    main()