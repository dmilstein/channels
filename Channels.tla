---- MODULE Channels ----

\* Provide a data structure to model message passing with configurable
\* guarantees -- reliable delivery, duplicates, out-of-order, duplicates *and*
\* out of order ("at least once").

\* By design, all the versions of the Channels data strucures provide the same
\* interface -- so that it's straightforward to change the messaging behavior
\* for an algorithm and see how it behaves.

\* The internal state is designed such that, on a failure, the message history
\* and timing can be parsed from the TLC output (which allows a timeline
\* diagram to be written out as an SVG)

\* The key operators that work on Channels are:
\*
\*  - InitChannels_<type>
\*     type \in {"Reliable", "Duplicates", "OutOfOrder", "AtLeastOnce"}
\*
\*  - Send() - send a single message from one client to another
\*
\*  - HasMessage() - does a given client have any messages waiting for it?
\*
\*  - NextMessages() - the set of message a given client *could* see next. This
\*  is how non-determinism is expressed to users of Channels -- they must
\*  choose one of these messages, non-deterministically, see below.
\*
\*  - MarkMessageReceived() - update channels to show a specific message was
\*  received. Note that the client process should always call this, after
\*  receiving a message -- the Channel data structure will take care of
\*  ensuring that duplicate are still generated.
\*
\* The messagse received by NextMessages() are "wrapped" (which is necessary
\* for MarkMessageReceived() to function). To obtain an underlying message
\* inside a receive loop, call:
\*
\* - Payload(wrapped_msg)
\*
\* Examples of use:
\*
\* First, construct one of the versions of the data structures, and store in a
\* global variable accessible by all clients, passing in the names of the
\* client processes:
\*
\* variables
\*  Channels = InitChannels_Reliable(Clients)
\*
\* To send a message, update that global Channels variable, as so:
\*
\* Channels := Send(Channels, sender, receiver, msg, msgLabel, senderState)
\*
\* Where:
\*  sender is the name of the sending client (usually self)
\*  receiver is the name of the destination client
\*  msg is the message to send, which is opaque to the Channels data structure
\*  msgLabel is a string describing the message, for the timeline diagram
\*  senderState is a string describing the state of the sender, for the timeline.
\*
\* To receive and process messages, use the following idiom:
\*
\* await HasMessage(Channels, self);
\* with wrapped_msg \in NextMessages(Channels, self) do
\*   with msg = Payload(wrapped_msg) do
\*     \* process msg
\*   end with;
\*   Channels := MarkMessageReceived(Channels, self, wrapped_msg, receiverState)

\* _D = Duplicating
\* _U = Unordered (on top of duplicating)

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
