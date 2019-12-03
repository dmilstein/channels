---- MODULE ChannelsReliable ----

\* An implementation of the Channels abstraction that models perfectly reliable
\* channels (no dropped messages, no duplicates, order always preserved)

EXTENDS Integers, Sequences, TLC

InitChannels(Clients) ==
  [ ClientInboxes |-> [ c \in Clients |-> <<>> ],
    LogicalTime |-> 0,
    MsgSteps |-> {}]

Message(sender, receiver,
        msg, msgLabel,
        sendAt, senderState) == [ sender |-> sender,
                                  receiver |-> receiver,
                                  payload |-> msg,
                                  msgLabel |-> msgLabel,
                                  sendAt |-> sendAt,
                                  recvAt |-> -1,
                                  senderState |-> senderState,
                                  receiverState |-> "" ]

Payload(msg) == msg.payload

HasMessage(C, client) == C.ClientInboxes[client] /= <<>>

Send(C, sender, receiver, msg, msgLabel, senderState) ==
  [ LogicalTime |-> C.LogicalTime + 1,
    ClientInboxes |-> (receiver :> Append(C.ClientInboxes[receiver],
                                          Message(sender,
                                                  receiver,
                                                  msg,
                                                  msgLabel,
                                                  C.LogicalTime + 1,
                                                  senderState)) @@ C.ClientInboxes)
    ] @@ C

\* Always return the first message, but return a set to fit the overall interface
NextMessages(C, client) == {Head(C.ClientInboxes[client])}

MarkMessageReceived(C, receiver, msg, receiverState) ==
  [ LogicalTime |-> C.LogicalTime + 1,
    ClientInboxes |-> (receiver :> Tail(C.ClientInboxes[receiver])
                       @@ C.ClientInboxes),
    MsgSteps |-> C.MsgSteps \union {[recvAt |-> C.LogicalTime + 1,
                                     receiverState |-> receiverState,
                                     payload |-> "" \* it's screwing up parsing
                                     ] @@ msg}
    ] @@ C

=====
