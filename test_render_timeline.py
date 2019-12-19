from render_timeline import parse_states, extract_msg_steps, extract_clients

tlc_output = r'''
State 5: <client line 65, col 20 to line 69, col 40 of module two_client_reliable_channel>
/\ C = [ ClientInboxes |->
      [ client1 |->
            << [ rawMsg |->
                     [ receiver |-> "client1",
                       sender |-> "client2",
                       msgLabel |-> "1",
                       senderState |-> 1,
                       receiverState |-> "",
                       sendAt |-> 2,
                       payload |-> 1,
                       recvAt |-> -1 ] ],
               [ rawMsg |->
                     [ receiver |-> "client1",
                       sender |-> "client2",
                       msgLabel |-> "1",
                       senderState |-> 2,
                       receiverState |-> "",
                       sendAt |-> 3,
                       payload |-> 1,
                       recvAt |-> -1 ] ] >>,
        client2 |-> <<>> ],
  LogicalTime |-> 4,
  MsgSteps |->
      { [ receiver |-> "client2",
          sender |-> "client1",
          msgLabel |-> "1",
          senderState |-> 1,
          receiverState |-> 3,
          sendAt |-> 1,
          payload |-> "",
          recvAt |-> 4 ] },
  NextMsgId |-> 3 ]
/\ GlobalCount = [client1 |-> 1, client2 |-> 3]
/\ MsgsSent = [client1 |-> 1, client2 |-> 2]

State 6: <client line 65, col 20 to line 69, col 40 of module two_client_reliable_channel>
/\ C = [ ClientInboxes |->
      [ client1 |->
            << [ rawMsg |->
                     [ receiver |-> "client1",
                       sender |-> "client2",
                       msgLabel |-> "1",
                       senderState |-> 2,
                       receiverState |-> "",
                       sendAt |-> 3,
                       payload |-> 1,
                       recvAt |-> -1 ] ] >>,
        client2 |-> <<>> ],
  LogicalTime |-> 5,
  MsgSteps |->
      { [ receiver |-> "client1",
          sender |-> "client2",
          msgLabel |-> "1",
          senderState |-> 1,
          receiverState |-> 2,
          sendAt |-> 2,
          payload |-> "",
          recvAt |-> 5 ],
        [ receiver |-> "client2",
          sender |-> "client1",
          msgLabel |-> "1",
          senderState |-> 1,
          receiverState |-> 3,
          sendAt |-> 1,
          payload |-> "",
          recvAt |-> 4 ] },
  NextMsgId |-> 3 ]
/\ GlobalCount = [client1 |-> 2, client2 |-> 3]
/\ MsgsSent = [client1 |-> 1, client2 |-> 2]

'''

def test_parse_states():
    states = parse_states(tlc_output)
    assert len(states) == 2

    final_state = states[-1]

    steps = extract_msg_steps(final_state)
    assert len([ s.recvAt for s in steps if s.received ]) == 2
    assert len([ s.recvAt for s in steps if not s.received ]) == 1

    clients = extract_clients(final_state)
    assert clients == ['client1', 'client2']

def test_parser_can_find_channels_under_any_name():
    tlc_output_adjusted = tlc_output.replace(r'/\ C =', r'/\ OtherName =')

    steps = extract_msg_steps(parse_states(tlc_output_adjusted)[-1])
    assert len(steps) == 3
