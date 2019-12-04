---- MODULE ChannelsReliable ----

\* An implementation of the Channels abstraction that models perfectly reliable
\* channels (no dropped messages, no duplicates, order always preserved)

EXTENDS Integers, Sequences, TLC, ChannelsUtils

InitChannels(Clients) == InitChannelsWithInboxes([ c \in Clients |-> <<>> ])

HasMessage(C, client) == C.ClientInboxes[client] /= <<>>

\* Match interface of the other, more complex Channel implementations
Wrap(msg) == [ rawMsg |-> msg ]

AddToInbox(C, msg, receiver) == Append(C.ClientInboxes[receiver], Wrap(msg))

Send(C, sender, receiver, msg, msgLabel, senderState) ==
  SendWithAdder(C, sender, receiver, msg, msgLabel, senderState, AddToInbox)

\* Always return the first message, but return a set to fit the overall interface
NextMessages(C, client) == {Head(C.ClientInboxes[client])}

RemoveOneCopy(msg, inbox) == Tail(inbox)

MarkMessageReceived(C, receiver, msg, receiverState) ==
  MarkReceivedWithRemover(C, receiver, msg, receiverState, RemoveOneCopy)

=====
