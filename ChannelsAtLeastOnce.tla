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

EXTENDS Integers, Sequences, TLC, ChannelsUtils

\* How many times can a single message be duplicated?
CONSTANT MaxDupes

InitChannels(Clients) == InitChannelsWithInboxes([ c \in Clients |-> {} ])

HasMessage(C, client) == C.ClientInboxes[client] /= {}

Wrap(msg, msgId) == [ rawMsg |-> msg,
                      numCopies |-> -1,
                      msgId |-> msgId ]

AddToInbox(C, msg, receiver) == (C.ClientInboxes[receiver] \union
                                 {Wrap(msg, C.NextMsgId)})

Send(C, sender, receiver, msg, msgLabel, senderState) ==
  SendWithAdder(C, sender, receiver, msg, msgLabel, senderState, AddToInbox)


Expand(wrapped) == IF wrapped.numCopies > 0
  THEN { wrapped }
  ELSE { [ rawMsg |-> wrapped.rawMsg,
           msgId |-> wrapped.msgId,
           numCopies |-> i ]:
         i \in 1..MaxDupes }

NextMessages(C, receiver) == UNION { Expand(msg):
                                     msg \in C.ClientInboxes[receiver] }

RemoveOneCopy(msg, inbox) ==
  LET msgToAddBack == IF msg.numCopies = 1
                         THEN {}
                         ELSE { [ numCopies |-> msg.numCopies-1 ] @@ msg}
  IN
    msgToAddBack \union { m \in inbox: m.msgId /= msg.msgId }

MarkMessageReceived(C, receiver, msg, receiverState) ==
  MarkReceivedWithRemover(C, receiver, msg, receiverState, RemoveOneCopy)

=====
