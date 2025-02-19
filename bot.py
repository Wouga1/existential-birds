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

memorised_win_rates = {}
# Calculate probability (between 0 and 1) of attacker winning a fight
# attackers: number of attackers
# defenders: number of defenders
def calculate_win_rate(attackers, defenders):
    # Don't calculate if a value is over 300
    if attackers > 300 or defenders > 300:
        return 0.75 if attackers > defenders else 0.25

    # Return memorised values
    key = f"{attackers},{defenders}"
    if key in memorised_win_rates:
        return memorised_win_rates[key]

    win_rate = 0
    
    # Find win rates for a battle
    battle_attackers = min(3, attackers - 1)
    battle_defenders = min(2, defenders)
    outcomes = calculate_outcome_chances(battle_attackers, battle_defenders)

    # For each outcome, add win rate given that outcome * chance of that outcome
    for outcome in outcomes:
        attacker_loss, defender_loss = outcome.split(",")
        new_attackers = attackers - int(attacker_loss)
        new_defenders = defenders - int(defender_loss)

        if new_defenders <= 0:
            win_rate += outcomes[outcome]
        elif new_attackers > 1:
            win_rate += outcomes[outcome] * calculate_win_rate(new_attackers, new_defenders)
    
    # Add to memorised values and return
    memorised_win_rates[key] = win_rate
    return win_rate

memorised_outcomes = {}
# Calculate the outcomes and probability of outcomes given a single fight
# Attackers should be between 1 and 3, defenders should be between 1 and 2
def calculate_outcome_chances(attackers, defenders):
    # Return memorised value if it exists
    key = f"{attackers},{defenders}"
    if key in memorised_outcomes:
        return memorised_outcomes[key]

    outcomes = {} # keys are "{attacker_loss},{defender_loss}"

    # Iterate over all possible dice rolls
    sample_space_size = 6**(attackers + defenders)
    for i in range(sample_space_size):
        n = i
        # Get dice rolls
        dice_rolls = []
        for _ in range(5):
            dice_rolls.append((i % 6) + 1)
            i //= 6

        # Split dice between attacker and defender, then sort them
        attacker_dice = dice_rolls[:attackers]
        attacker_dice.sort(reverse=True)
        defender_dice = dice_rolls[attackers:]
        defender_dice.sort(reverse=True)

        # Find how many attacker die and how many defenders die
        attacker_loss = 0
        defender_loss = 0
        j = 0
        while j < len(attacker_dice) and j < len(defender_dice):
            if attacker_dice[j] > defender_dice[j]:
                defender_loss += 1
            else:
                attacker_loss += 1
            j += 1

        # Add 1 to whichever outcome occured
        outcome = f"{attacker_loss},{defender_loss}"
        if outcome in outcomes:
            outcomes[outcome] += 1
        else:
            outcomes[outcome] = 1

    # Divide by sample space size
    for outcome in outcomes:
        outcomes[outcome] /= sample_space_size

    # Add to memorised values and return
    memorised_outcomes[key] = outcomes
    return outcomes

# We will store our enemy in the bot state.
class BotState():
    def __init__(self):
        self.remaining_claims = -1

# Dictionary of what territories are in each continent
continents = {
        "AF": (32, 33, 34, 35, 36, 37),
        "SA": (28, 29, 30, 31),
        "AU": (38, 39, 40, 41),
        "NA": (0, 1, 2, 3, 4, 5, 6, 7, 8),
        "EU": (9, 10, 11, 12, 13, 14, 15),
        "AS": (16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27)
    }

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

    # If first time, determine how many territories we can claim total
    if bot_state.remaining_claims == -1:
        bot_state.remaining_claims = 9 if game.state.me.player_id in game.state.turn_order[:2] else 8

    unclaimed_territories = game.state.get_territories_owned_by(None)
    my_territories = game.state.get_territories_owned_by(game.state.me.player_id)
    me = game.state.me.player_id

    
    uncontested_continents = [] # Continents we have a territory in that no other players have territories in (but we do not fully control)
    empty_continents = [] # Continents that nobody has
    influenced_continents = [] # Continents that we have a territory in (and have at least one free territory)
    for continent in continents.keys():
        total_territories = len(continents[continent])
        our_territories = len([territory for territory in continents[continent] if game.state.territories[territory].occupier == me])
        free_territories = len([territory for territory in continents[continent] if game.state.territories[territory].occupier == None])
        if total_territories - free_territories == 0:
            # Nobody has a territory here
            empty_continents.append(continent)
            continue
        if total_territories - our_territories == 0:
            # We already have this continent
            continue
        if total_territories - our_territories - free_territories == 0:
            # Nobody else has contested this continent
            uncontested_continents.append(continent)
        if our_territories > 1 and free_territories > 1:
            # We have at least 1 territory
            influenced_continents.append(continent)

    # We will look for any continents that only we have territories in
    if len(uncontested_continents) > 0:
        # Sort by (number of territories in continent - number of territories we own in continent)
        # This finds the continent we need the least tiles to claim
        uncontested_continents.sort(key = lambda x: len(continents[x]) - len([territory for territory in continents[x] if game.state.territories[territory].occupier == me]))
        chosen_continent = uncontested_continents[0]

        # Find all unclaimed territories in that continent
        unclaimed_in_continent = [territory for territory in continents[chosen_continent] if territory in unclaimed_territories]

        # Sort by how many adjacent territories we own
        # This lets us find the territory we have the most adjacent territories to
        unclaimed_in_continent.sort(key = lambda x: len([territory for territory in game.state.get_all_adjacent_territories([x]) if game.state.territories[territory].occupier == me]), reverse=True)
        to_claim = unclaimed_in_continent[0]

        return game.move_claim_territory(query, to_claim)

    # We will look for any continents that nobody has territories in
    if len(empty_continents) > 0:
        # Grab a territory in that empty continent
        chosen_continent = empty_continents[0]

        # Find all unclaimed territories in that continent
        unclaimed_in_continent = [territory for territory in continents[chosen_continent]]

        # Sort by how many adjacent territories we own
        # This lets us find the territory we have the most adjacent territories to
        unclaimed_in_continent.sort(key = lambda x: len([territory for territory in game.state.get_all_adjacent_territories([x]) if game.state.territories[territory].occupier == me]), reverse=True)
        to_claim = unclaimed_in_continent[0]

        return game.move_claim_territory(query, to_claim)

    # We will expand our easiest to claim continent
    if len(influenced_continents) > 0:
        # Sort by least enemy territories
        # This finds the continent with the least enemies
        enemies = [player for player in game.state.players.keys() if player != me]
        influenced_continents.sort(key = lambda x: len([territory for territory in continents[x] if game.state.territories[territory].occupier in enemies]))
        chosen_continent = influenced_continents[0]

        # Find all unclaimed territories in that continent
        unclaimed_in_continent = [territory for territory in continents[chosen_continent] if territory in unclaimed_territories]

        # Sort by how many adjacent territories we own
        # This lets us find the territory we have the most adjacent territories to
        unclaimed_in_continent.sort(key = lambda x: len([territory for territory in game.state.get_all_adjacent_territories([x]) if game.state.territories[territory].occupier == me]), reverse=True)
        to_claim = unclaimed_in_continent[0]

        return game.move_claim_territory(query, to_claim)
    
    # If there are no such territories, we will pick just an unclaimed one with the greatest number of adjacent unclaimed territories.
    selected_territory = sorted(unclaimed_territories, key=lambda x: len([territory for territory in game.state.map.get_adjacent_to(x) if territory in game.state.get_territories_owned_by(None)]), reverse=True)[0]

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

    # Redeem card whenever we can
    if query.cause == "turn_started":
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
    continents = game.state.map._continents
    uncontested_continents = [continent for continent in continents.keys() 
    if len([territory for territory in continents[continent] if game.state.territories[territory].occupier == game.state.me.player_id or game.state.territories[territory].occupier == None]) != 0]

    all_enemies = dict([(player, game.state.get_territories_owned_by(player)) for player in game.state.players.keys() if player != game.state.me.player_id])

    def attack_weakest(territories: list[int]) -> Optional[MoveAttack]:
            # We will attack the weakest territory from the list.
            territories = sorted(territories, key=lambda x: game.state.territories[x].troops)
            for candidate_target in territories:
                candidate_attackers = sorted(list(set(game.state.map.get_adjacent_to(candidate_target)) & set(my_territories)), key=lambda x: game.state.territories[x].troops, reverse=True)
                for candidate_attacker in candidate_attackers:
                    my_troops = game.state.territories[candidate_attacker].troops
                    target_troops = game.state.territories[candidate_target].troops
                    # For smaller armies, calculate out our odds or winning
                    if calculate_win_rate(my_troops, target_troops) > 0.5:
                            return game.move_attack(query, candidate_attacker, candidate_target, min(3, game.state.territories[candidate_attacker].troops - 1))

    def can_eliminate(territories: list[int]) -> Optional[bool]:
        targetable_territories = []
        # Check if our border territories can target is in their territory list
        # Recursive function that checks connectivity of locations
        def recursive_target(territory):
            if territory in targetable_territories:
                return 

            targetable_territories.append(territory)
            for connected in game.state.map.get_adjacent_to(territory):
                # Recursively, get all the adjacent territories to get all connected territories
                recursive_target(connected)

        for bordering_territory in bordering_territories:
            adjacents = game.state.map.get_adjacent_to(bordering_territory)
            # These are the starting points for attack based on borders.
            targetable_territories += [targetable for targetable in adjacents if targetable in territories]
            targetable_territories = list(set(targetable_territories))
            for targetables in targetable_territories:
                recursive_target(targetables)

        if len(targetable_territories) == len(territories) and len(targetable_territories) != 0: 
            # If they can be eliminated, we compare our attacking force vs their defense
            attacking = sum([game.state.territories[bordering_territory].troops 
            # Only count territories that can attack as part of our attacking force
            for bordering_territory in bordering_territories if game.state.territories[bordering_territory].troops > 1])
            defending = sum([game.state.territories[defenders].troops 
            for defenders in targetable_territories])
            # Then, calculate our win rate and send it if it's good.
            win_rate = calculate_win_rate(attacking, defending)
            if win_rate > 0.5:
                attack_weakest(targetable_territories)

    for enemy_territories in all_enemies.values():
        can_eliminate(enemy_territories)

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
    is_border = len(set(game.state.map.get_adjacent_to(conquered_territory)) - set(game.state.get_territories_owned_by(game.state.me.player_id)))
    if is_border: 
        return game.move_troops_after_attack(query, attacking_territory.troops - 1)

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
    # if most_powerful_player == game.state.me.player_id:
    #     return game.move_fortify_pass(query)
    
    # Otherwise we will find the shortest path between our territory with the most troops
    # and any of the most powerful player's territories and fortify along that path.

    #our territories
    our_territories =  game.state.get_territories_owned_by(player.player_id)

    #all terroritiories bordering my spot
    candidate_territories = game.state.get_all_border_territories(my_territories)

    my_border_territories = [mine for mine in candidate_territories if mine in our_territories]
    most_troops_territory = max(candidate_territories, key=lambda x: game.state.territories[x].troops)
    weakest_borders = []
    for my_spot in my_border_territories:
        bordering_territories = game.state.get_all_adjacent_territories([my_spot])
        enemy_territories = [enemy for enemy in bordering_territories if enemy not in our_territories]
        my_troops = game.state.territories[my_spot].troops
        enemy_troops = 0
        for i in range(len(enemy_territories)):
            enemy_troops+= game.state.territories[enemy_territories[i]].troops
        #enemy fail rate calc
        if calculate_win_rate(enemy_troops, my_troops) > 0.3:
            weakest_borders.append(my_spot)
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