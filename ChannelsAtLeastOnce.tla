---- MODULE ChannelsAtLeastOnce ----

\* An implementation of the Channels abstraction that models channels where a
\* finite number of duplicates of a message can be delivered, and where
\* messages can be delivered in a different order than they were sent.

\* The specific number of potential duplicates is determined by the
\* MaxDupes constant, which calling modules can set, ala:

\* INSTANCE ChannelsAtLeastOnce WITH MaxDupes <- 2

\* The implementation strategy is: first, to wrap each messages in an envelope
\* which adds a unique message id (msgId), and also a count of how many times
\* the message should be delivered (numCopies); and second, to store messages
\* to be delivered to any one client in a set.

\* When a message is first sent, numCopies for that envelope is set to the
\* sentinel value of -1. On the first receiving of such a message in
\* NextMessages, this expands out into a set of 1 .. MaxDupes distinct versions
\* of the message, each with a positive value for numCopies. When one of those
\* copies is then passed into MarkMessageReceived, the original message with
\* the sentinel value will be removed from the set, and a specific version with
\* numCopies decremented will be added. Then, in each of those "timelines", the
\* proper number of copies will eventually be delivered.

EXTENDS Integers, Sequences, TLC

\* How many times can a single message be duplicated?
CONSTANT MaxDupes

InitChannels(Clients) ==
  [ ClientInboxes |-> [ c \in Clients |-> {} ],
    LogicalTime |-> 0,
    MsgSteps |-> {},
    NextMsgId |-> 0]

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

Wrap(msg, msgId) == [ rawMsg |-> msg,
                      numCopies |-> -1,
                      msgId |-> msgId ]

Expand(wrapped) == IF wrapped.numCopies > 0
  THEN { wrapped }
  ELSE { [ rawMsg |-> wrapped.rawMsg,
           msgId |-> wrapped.msgId,
           numCopies |-> i ]:
         i \in 1..MaxDupes }

Payload(msg) == msg.rawMsg.payload

HasMessage(C, client) == C.ClientInboxes[client] /= {}

Send(C, sender, receiver, msg, msgLabel, senderState) ==
  [ LogicalTime |-> C.LogicalTime + 1,
    NextMsgId |-> C.NextMsgId + 1,
    ClientInboxes |-> (receiver :> (C.ClientInboxes[receiver] \union
                                    { Wrap(Message(sender,
                                                   receiver,
                                                   msg,
                                                   msgLabel,
                                                   C.LogicalTime + 1,
                                                   senderState),
                                           C.NextMsgId)})
                       @@ C.ClientInboxes)
    ] @@ C

NextMessages(C, receiver) == UNION { Expand(msg) :
                                     msg \in C.ClientInboxes[receiver] }

RemoveOneCopy(msg, inbox) ==
  LET msg_to_add_back == IF msg.numCopies = 1
                         THEN {}
                         ELSE { [ numCopies |-> msg.numCopies-1 ] @@ msg}
  IN
    msg_to_add_back \union { m \in inbox: m.msgId /= msg.msgId }

MarkMessageReceived(C, receiver, msg, receiverState) ==
  [ LogicalTime |-> C.LogicalTime + 1,
    ClientInboxes |-> ((receiver :> RemoveOneCopy(msg, C.ClientInboxes[receiver]))
                       @@ C.ClientInboxes),
    MsgSteps |-> C.MsgSteps \union {[recvAt |-> C.LogicalTime + 1,
                                     receiverState |-> receiverState,
                                     payload |-> "" \* it's screwing up parsing
                                     ] @@ msg.rawMsg}
    ] @@ C
=====
