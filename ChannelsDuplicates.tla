---- MODULE ChannelsDuplicates ----

\* An implementation of the Channels abstraction that models channels where a
\* finite number of duplicates of a message can be delivered, but where order
\* is still preserved.

\* The implementation strategy is to wrap all messages in an envelope which
\* counts how many times they have been delivered. When the message is first
\* sent, numCopies for that envelope is set to -1. On the first attempt to
\* receive a message, this expands out into a set of 1 .. MaxDupes distinct
\* versions of the message, each with a positive value for numCopies. On
\* MarkMessageReceived, each of those will replace the first copy, and, in each
\* of those "timelines", the proper number of copies will then be
\* deterministically delivered.

EXTENDS Integers, Sequences, TLC

\* How many times can a single message be duplicated?
CONSTANT MaxDupes

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

\* We wrap the underlying message with a number of (remaining) copies to
\* deliver. This allows us to track how many times we've delivered a given
\* message, and how many are remaining.
Wrap(msg) == [ rawMsg |-> msg,
               numCopies |-> -1]

Expand(wrapped) == IF wrapped.numCopies > 0
  THEN { wrapped }
  ELSE { [ rawMsg |-> wrapped.rawMsg,
           numCopies |-> i ]
         :
         i \in 1..MaxDupes }

Payload(msg) == msg.rawMsg.payload

HasMessage(C, client) == C.ClientInboxes[client] /= <<>>

Send(C, sender, receiver, msg, msgLabel, senderState) ==
  [ LogicalTime |-> C.LogicalTime + 1,
    ClientInboxes |-> (receiver :> Append(C.ClientInboxes[receiver],
                                          Wrap(Message(sender,
                                                       receiver,
                                                       msg,
                                                       msgLabel,
                                                       C.LogicalTime + 1,
                                                       senderState)))
                       @@ C.ClientInboxes)
    ] @@ C

NextMessages(C, receiver) ==  Expand(Head(C.ClientInboxes[receiver]))

RemoveOneCopy(msg, inbox) ==
  \* For in-order duplicates, the received messages is always the first.
  IF
    msg.numCopies = 1 \* We just processed this, so no more
  THEN
    Tail(inbox)
  ELSE
    <<[ numCopies |-> msg.numCopies-1 ] @@ msg>> \o Tail(inbox)

MarkMessageReceived(C, receiver, msg, receiverState) ==
  [ LogicalTime |-> C.LogicalTime + 1,
    ClientInboxes |-> (receiver :> RemoveOneCopy(msg,
                                                 C.ClientInboxes[receiver])
                       @@ C.ClientInboxes),
    MsgSteps |-> C.MsgSteps \union {[recvAt |-> C.LogicalTime + 1,
                                     receiverState |-> receiverState,
                                     payload |-> "" \* it's screwing up parsing
                                     ] @@ msg.rawMsg}
    ] @@ C

=====
