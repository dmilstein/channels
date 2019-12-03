"""
Library to parse TLA+ states, as output by TLC when it finds violations of
invariants or properties.
"""

from pyparsing import *

def parse_tla_state(state_str):
    """
    Given a string describing a single TLA state, return a dictionary
    mapping variable names to the values those variables have in the
    given state (making the natural conversions of ints, strings, dicts,
    lists, and sets as expected)
    """
    expr = Forward()
    
    identifier = Word(alphas) # xxx placeholder for now
    # Hah! Just int values to start with
    integer = Word(nums).setParseAction(lambda toks: int(toks[0]))
    string = QuotedString('"')
    sequence = nestedExpr("<<", ">>", delimitedList(expr))

    functionMember = Group(identifier + Suppress("|->") + expr)
    functionMemberLst = delimitedList(functionMember)
    
    #function = nestedExpr("[", "]", Optional(Dict(functionMemberLst), {}))
    function = nestedExpr("[", "]", Dict(functionMemberLst), {})

    # need sets, too

    # and then, handle multiple expressions separated by /\'s
    
    expr << (integer | string | sequence | function)
    # Switch to delimited list with "/\" as delimiter?
    state = Dict(Group(Suppress("/\\") +
                           identifier +
                           Suppress("=") +
                           expr))
    return state.parseString(state_str).asDict()
