---- MODULE ChannelsOutOfOrder ----

\* An implementation of the Channels abstraction that models channels where
\* messages can be delivered out of order, but where any given message is
\* delivered exactly once.

\* The implementation strategy is to wrap the messages in an envelope with a
\* unique identifier and then simply store all messages sent to a given
\* receiver in a set (we need the identifier so the set can store messages with
\* identical contents).

EXTENDS Integers, Sequences, TLC

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
                      msgId |-> msgId ]

Payload(msg) == msg.rawMsg.payload

HasMessage(C, client) == C.ClientInboxes[client] /= {}

Send(C, sender, receiver, msg, msgLabel, senderState) ==
  [ LogicalTime |-> C.LogicalTime + 1,
    NextMsgId |-> C.NextMsgId + 1,
    ClientInboxes |-> (receiver :> (C.ClientInboxes[receiver] \union
                                    {Wrap(Message(sender,
                                                  receiver,
                                                  msg,
                                                  msgLabel,
                                                  C.LogicalTime + 1,
                                                  senderState),
                                           C.NextMsgId)})
                       @@ C.ClientInboxes)
    ] @@ C

NextMessages(C, receiver) == C.ClientInboxes[receiver]

RemoveOneCopy(msg, inbox) == { m \in inbox: m.msgId /= msg.msgId }

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
