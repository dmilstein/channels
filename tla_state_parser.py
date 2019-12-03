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

    # Identifiers are: a string of letters, digits, and the underscore
    # character (_) that contains at least one letter, as per:
    # https://www.microsoft.com/en-us/research/uploads/prod/2018/05/book-02-08-08.pdf
    identifier = Word(alphas + nums + "_")

    integer = Word("-" + nums, nums).setParseAction(lambda toks: int(toks[0]))
    
    string = QuotedString('"')

    sequence = nestedExpr("<<", ">>", delimitedList(expr))

    # In fact, sets can only contain things which can be checked for
    # equality, which is not all expressions, but whatever.
    tla_set = nestedExpr("{", "}", delimitedList(expr)).setParseAction(
        lambda toks: set(toks[0]))

    functionMember = Group(identifier + Suppress("|->") + expr)
    functionMemberLst = delimitedList(functionMember)

    # xxx figure out how to match empty functions
    #function = nestedExpr("[", "]", Optional(Dict(functionMemberLst), {}))
    function = nestedExpr("[", "]", Dict(functionMemberLst))

    modelValue = identifier # hmm, not sure how else to do this
    
    expr << (integer | string | sequence | tla_set | function | modelValue)

    # This feels a bit hacky -- rather than expressing the /\'s as
    # delimiters (which they basically are), I'm leaning on the fact
    # that each line starts with one. But it works.
    equality_assertion = Group(Suppress("/\\") + identifier + Suppress("=") + expr)
    state = Dict(OneOrMore(equality_assertion))
    return state.parseString(state_str).asDict()
