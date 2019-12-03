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

def test_parse_simple_state():
    assert parse_tla_state(r'/\ x = 2') == { 'x': 2 }
    assert parse_tla_state(r'/\ x = "abc"') == { 'x': "abc" }
    assert parse_tla_state(r'/\ x = <<1,2>>') == { 'x': [1,2] }
    assert parse_tla_state(r'/\ x = <<1,"a">>') == { 'x': [1,"a"] }
    assert parse_tla_state(r'/\ x = <<1,<<2>>>>') == { 'x': [1,[2]] }
    assert parse_tla_state(r'/\ x = <<>>') == { 'x': [] }
    assert parse_tla_state(r'/\ x = [y |-> 0]') == { 'x': { 'y': 0 }}
    assert parse_tla_state(r'/\ x = [y |-> 0, z |-> 1]') == { 'x': { 'y': 0, 'z': 1 }}
    #assert parse_tla_state(r'/\ x = []') == { 'x': {}}
