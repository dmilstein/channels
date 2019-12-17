from frozendict import frozendict

from tla_state_parser import parse_tla_state

tla_sample = r"""
/\ MsgsPerClient = 2
/\ Channels = [ ClientInboxes |->
      [ client1 |-> <<>>,
        client2 |->
            << [ sender |-> "client1",
                 receiver |-> "client2",
                 msgLabel |-> "Msg: -1",
                 sendAt |-> 2,
                 senderState |-> 0,
                 payload |-> -1,
                 recvAt |-> Null,
                 receiverState |-> Null ] >> ],
  LogicalTime |-> 5,
  MsgSteps |->
      { [ sender |-> "client1",
          receiver |-> "client2",
          msgLabel |-> "Msg: 1",
          sendAt |-> 1,
          senderState |-> 1,
          payload |-> 1,
          recvAt |-> 3,
          receiverState |-> 1 ],
        [ sender |-> "client2",
          receiver |-> "client1",
          msgLabel |-> "Msg: -1",
          sendAt |-> 4,
          senderState |-> 0,
          payload |-> -1,
          recvAt |-> 5,
          receiverState |-> -1 ] },
  NextMsgId |-> 0 ]
/\ Val = [client1 |-> -1, client2 |-> 0]
/\ MsgsSent = [client1 |-> 2, client2 |-> 1]
"""

pts = parse_tla_state

def test_parse_numbers():
    assert pts(r'/\ x = 2') == { 'x': 2 }
    assert pts(r'/\ x = -2') == { 'x': -2 }

def test_parse_strings():
    assert pts(r'/\ x = "abc"') == { 'x': "abc" }

def test_parse_sequences():
    assert pts(r'/\ x = <<1,2>>') == { 'x': (1,2) }
    assert pts(r'/\ x = <<1,"a">>') == { 'x': (1,"a") }
    assert pts(r'/\ x = <<1,<<2>>>>') == { 'x': (1,(2,)) }
    assert pts(r'/\ x = <<>>') == { 'x': () }

def test_parse_functions():
    a_parsed_func = pts(r'/\ x = [y |-> 0]')['x']
    s = set([a_parsed_func])
    assert a_parsed_func in s
    assert pts(r'/\ x = [y |-> 0]') == {'x': frozendict({ 'y': 0 })}
    assert pts(r'/\ x = [y |-> "abc"]') == {'x': frozendict({ 'y': "abc" })}
    assert pts(r'/\ x = [y |-> "ab c"]') == { 'x': frozendict({ 'y': "ab c" })}
    assert pts(r'/\ x = [y |-> 0, z |-> 1]') == { 'x': frozendict({ 'y': 0, 'z': 1 })}
    assert pts(r'/\ x = []') == { 'x': frozendict({})}

def test_parse_sets():
    assert pts(r'/\ x = {}') == { 'x': frozenset()}
    assert pts(r'/\ x = {1}') == { 'x': frozenset([1])}
    assert pts(r'/\ x = {1, 2}') == { 'x': frozenset([1, 2])}
    assert pts(r'/\ x = {1, {2}}') == { 'x': frozenset([1, frozenset([2])])}
    assert pts(r'/\ x = { [y |-> 1] }') == { 'x': frozenset([frozendict({'y': 1})])}

def test_parse_identifier_names():
    assert pts(r'/\ x1 = 1') == { 'x1': 1 }
    assert pts(r'/\ x_1 = 1') == { 'x_1': 1 }

def test_parse_multiline():
    assert pts('/\\ x = <<1,\n2>>') == { 'x': (1,2) }

def test_parse_multiple_variables():
    two_vars = r'''
/\ x = 2
/\ y = 3
'''
    assert pts(two_vars) == { 'x': 2, 'y': 3 }

    four_vars = r'''
/\ x = 2
/\ y = 3
/\ z = [ a |-> "b" ]
/\ w = [ a |-> <<1, 2>> ]
'''

    assert pts(four_vars) == { 'x': 2,
                               'y': 3,
                               'z': {'a': 'b'},
                               'w': {'a': (1, 2)}}

def test_embedded_dict():
    tla = r'''
/\ x = [MsgSteps |->
      { [ sender |-> "client1",
          receiver |-> "client2"] },
  NextMsgId |-> 0 ]
'''
    assert pts(tla) == {
        'x': frozendict({'MsgSteps': set([frozendict({'sender': "client1",
                                                      'receiver': "client2"})]),
                         'NextMsgId': 0})}
