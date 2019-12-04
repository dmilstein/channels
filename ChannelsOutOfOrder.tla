---- MODULE ChannelsOutOfOrder ----

\* An implementation of the Channels abstraction that models channels where
\* messages can be delivered out of order, but where any given message is
\* delivered exactly once.

\* The implementation strategy is to wrap the messages in an envelope with a
\* unique identifier and then simply store all messages sent to a given
\* receiver in a set (we need the identifier so the set can store messages with
\* identical contents).

EXTENDS Integers, Sequences, TLC, ChannelsUtils

InitChannels(Clients) == InitChannelsWithInboxes([ c \in Clients |-> {} ])

HasMessage(C, client) == C.ClientInboxes[client] /= {}

Wrap(msg, msgId) == [ rawMsg |-> msg,
                      msgId |-> msgId ]

AddToInbox(C, msg, reciever) == (C.ClientInboxes[reciever] \union
                                 {Wrap(msg, C.NextMsgId)})

Send(C, sender, receiver, msg, msgLabel, senderState) ==
  SendWithAdder(C, sender, receiver, msg, msgLabel, senderState, AddToInbox)

NextMessages(C, receiver) == C.ClientInboxes[receiver]

RemoveOneCopy(msg, inbox) == { m \in inbox: m.msgId /= msg.msgId }

MarkMessageReceived(C, receiver, msg, receiverState) ==
  MarkReceivedWithRemover(C, receiver, msg, receiverState, RemoveOneCopy)

=====
