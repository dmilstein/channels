"""
Library to parse TLA+ states, as output by TLC when it finds violations of
invariants or properties.
"""

from immutables import Map

from pyparsing import *

def parse_tla_state(state_str):
    """Given a string describing a single TLA state, return a dictionary
    mapping variable names to the values those variables have in the
    given state.

    Constructs *immutable* python versions of the various TLA datatypes --
    because TLA+ allows sets of all of its datatypes, which is only possible if
    we use immutable python types.

    Thus:
      - ints -> ints
      - strings -> strings
      - sequences -> tuples (*not* lists)
      - functions -> immutables.Map's
      - sets -> frozensets
      - model values -> strings (not sure what else to parse them as)

    """
    expr = Forward()

    # Identifiers are: a string of letters, digits, and the underscore
    # character (_) that contains at least one letter, as per:
    # https://www.microsoft.com/en-us/research/uploads/prod/2018/05/book-02-08-08.pdf
    identifier = Word(alphas + nums + "_")

    integer = Word("-" + nums, nums).setParseAction(lambda toks: int(toks[0]))

    string = QuotedString('"')

    sequence = nestedExpr("<<", ">>",
                          delimitedList(expr)).setParseAction(
                              lambda toks: tuple(toks[0]))

    # In fact, sets can only contain things which can be checked for
    # equality, which is not all expressions, but we're ignoring that
    tla_set = nestedExpr("{", "}",
                         delimitedList(expr)).setParseAction(
                             lambda toks: frozenset(toks[0]))

    # Functions are complex, because they have 3 forms, all of which can show
    # up in state traces:
    #
    # [ key1 |-> value1, key2 |-> value2, ...]
    #
    # key :> value
    #
    # func1 @@ func2
    function_member = Group(identifier + Suppress("|->") + expr)
    function_member_list = delimitedList(function_member)

    full_function = nestedExpr("[", "]", Dict(function_member_list))
    full_function.setParseAction(lambda toks: Map(toks[0]))

    single_elt_function = identifier + Suppress(":>") + expr
    single_elt_function.setParseAction(lambda toks: Map([(toks[0], toks[1])]))

    function = full_function | single_elt_function

    function_prepend = function + Suppress("@@") + function
    function_prepend.setParseAction(lambda toks: Map(toks[1], **toks[0]))

    parens = Suppress("(") + expr + Suppress(")")

    model_value = identifier # hmm, not sure how else to do this

    expr << (integer |
             string |
             sequence |
             tla_set |
             function_prepend |
             function |
             model_value |
             parens)

    # This feels a bit hacky -- rather than expressing the /\'s as
    # delimiters (which they basically are), I'm leaning on the fact
    # that each line starts with one. But it works.
    equality_assertion = Group(Suppress("/\\") + identifier + Suppress("=") + expr)
    state = Dict(OneOrMore(equality_assertion))
    return state.parseString(state_str).asDict()
