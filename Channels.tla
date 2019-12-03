---- MODULE Channels ----
\* Local instance?
EXTENDS Integers, Sequences, TLC

CONSTANT NULL

InitChannels(Clients) ==
  [ ClientInboxes |-> [ c \in Clients |-> <<>> ],
    LogicalTime |-> 0,
    MsgSteps |-> {},
    NextMsgId |-> 0]

InitChannels_U(Clients) ==
  [ ClientInboxes |-> [ c \in Clients |-> {} ],
    LogicalTime |-> 0,
    MsgSteps |-> {},
    NextMsgId |-> 0]

HasMessage(C, client) == C.ClientInboxes[client] /= <<>>
HasMessage_U(C, client) == C.ClientInboxes[client] /= {}

N(time_step) == time_step + 1

\* Convert to a CONSTANT, most likely
MaxDupes == 2

Identity(x) == x

Message(sender, receiver,
        msg, msgLabel,
        sendAt, senderState) == [ sender |-> sender,
                                  receiver |-> receiver,
                                  payload |-> msg,
                                  msgLabel |-> msgLabel,
                                  sendAt |-> sendAt,
                                  recvAt |-> NULL,
                                  senderState |-> senderState,
                                  receiverState |-> NULL ]

Wrap(msg, msgId) == [ rawMsg |-> msg, numCopies |-> NULL, msgId |-> msgId ]

\* Expand returns a set
Expand(wrapped) == IF wrapped.numCopies /= NULL
  THEN { wrapped }
  ELSE { [ rawMsg |-> wrapped.rawMsg,
           numCopies |-> i,
           msgId |-> wrapped.msgId ]
           :
           i \in 1..MaxDupes }

Payload(msg) == msg.rawMsg.payload

\* Duplicating send
Send_D(C, sender, receiver, msg, msgLabel, senderState) ==
  [ LogicalTime |-> N(C.LogicalTime),
    NextMsgId |-> C.NextMsgId + 1,
    ClientInboxes |-> (receiver :> Append(C.ClientInboxes[receiver],
                                          Wrap(Message(sender,
                                                       receiver,
                                                       msg,
                                                       msgLabel,
                                                       N(C.LogicalTime),
                                                       senderState),
                                               C.NextMsgId
                                               )) @@ C.ClientInboxes)
    ] @@ C

\* Out-of-order *and* Duplicating send
Send_U(C, sender, receiver, msg, msgLabel, senderState) ==
  [ LogicalTime |-> N(C.LogicalTime),
    NextMsgId |-> C.NextMsgId + 1,
    ClientInboxes |-> (receiver :> (C.ClientInboxes[receiver] \union
                                    {Wrap(Message(sender,
                                                  receiver,
                                                  msg,
                                                  msgLabel,
                                                  N(C.LogicalTime),
                                                  senderState),
                                           C.NextMsgId
                                           )})) @@ C.ClientInboxes
    ] @@ C

NextMessages(C, client) ==  Expand(Head(C.ClientInboxes[client]))
NextMessages_U(C, client) == UNION { Expand(msg) : msg \in C.ClientInboxes[client] }

RemoveOneCopy(C, receiver, msg) ==
  \* For now, assuming *had* to be first message, if I move to sets, change
  \* And just do { \A m \in C.ClientInboxes[receiver] : m.msg_id /= msg.msg_id }
  \* And \union message with numopies decremented
  IF
    msg.numCopies = 1 \* We just processed this, so no more
  THEN
    Tail(C.ClientInboxes[receiver])
  ELSE
    <<[ numCopies |-> msg.numCopies-1 ] @@ msg>> \o Tail(C.ClientInboxes[receiver])

MarkMessageReceived(C, receiver, msg, receiverState) ==
  [ LogicalTime |-> N(C.LogicalTime),
    ClientInboxes |-> ((receiver :> RemoveOneCopy(C, receiver, msg))
                       @@ C.ClientInboxes),
    MsgSteps |-> C.MsgSteps \union {[recvAt |-> N(C.LogicalTime),
                                     receiverState |-> receiverState,
                                     payload |-> "" \* it's screwing up parsing
                                     ] @@ msg.rawMsg}
    ] @@ C


RemoveOneCopy_U(C, receiver, msg) ==
  LET msg_to_add_back == IF msg.numCopies = 1
                         THEN {}
                         ELSE { [ numCopies |-> msg.numCopies-1 ] @@ msg}
  IN
    msg_to_add_back \union { m \in C.ClientInboxes[receiver] :
                             m.msgId /= msg.msgId }

MarkMessageReceived_U(C, receiver, msg, receiverState) ==
  [ LogicalTime |-> N(C.LogicalTime),
    ClientInboxes |-> ((receiver :> RemoveOneCopy_U(C, receiver, msg))
                       @@ C.ClientInboxes),
    MsgSteps |-> C.MsgSteps \union {[recvAt |-> N(C.LogicalTime),
                                     receiverState |-> receiverState,
                                     payload |-> "" \* it's screwing up parsing
                                     ] @@ msg.rawMsg}
    ] @@ C


\* Non-duplicating send version

Send(C, sender, receiver, msg, msgLabel, senderState) ==
  [ LogicalTime |-> N(C.LogicalTime),
    ClientInboxes |-> (receiver :> Append(C.ClientInboxes[receiver],
                                          Message(sender,
                                                  receiver,
                                                  msg,
                                                  msgLabel,
                                                  N(C.LogicalTime),
                                                  senderState)) @@ C.ClientInboxes)
    ] @@ C


NextMessage(C, client) == Head(C.ClientInboxes[client]).payload

MarkReceived(C, receiver, new_val) ==
  [ LogicalTime |-> N(C.LogicalTime),
    ClientInboxes |-> (receiver :> Tail(C.ClientInboxes[receiver]) @@ C.ClientInboxes),
    MsgSteps |-> C.MsgSteps \union {[recvAt |-> N(C.LogicalTime),
                                     receiverState |-> new_val]
                                    @@ Head(C.ClientInboxes[receiver])}
    ] @@ C

=====
