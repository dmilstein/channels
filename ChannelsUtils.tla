---- MODULE ChannelsUtils ----

\* Shared utilities for the Channels implementations -- most internal, with the
\* exception of Payload() which is part of the overall interface.

EXTENDS Integers, TLC

\* All the Channels implementations store client inboxes inside a map from
\* names to inboxes (even though the inboxes structures themselves can vary --
\* some are sets, some are sequences).

InitChannelsWithInboxes(clientInboxes) ==
  [ ClientInboxes |-> clientInboxes,
    LogicalTime |-> 0,
    MsgSteps |-> {},
    NextMsgId |-> 0 \* not used in all implementations
    ]

\* Take an underlying message from a client and wrap it in a first level of
\* information. Some of that information is needed to ensure delivery, some
\* is just stored to allow later timeline reconstruction from a trace.
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

\* All implementations wrap the Messages in some form of envelope
Payload(msg) == msg.rawMsg.payload

\* Given the shared structure, we can used shared logic to do the machinery of
\* both sending and marking received, as long we can pass in something which
\* knows how to add or remove from a single inbox, respectively.

SendWithAdder(C, sender, receiver, msg, msgLabel, senderState, addToInbox(_,_,_)) ==
  [ LogicalTime |-> C.LogicalTime + 1,
    NextMsgId |-> C.NextMsgId + 1,
    ClientInboxes |-> (receiver :> addToInbox(C,
                                              Message(sender,
                                                      receiver,
                                                      msg,
                                                      msgLabel,
                                                      C.LogicalTime + 1,
                                                      senderState),
                                              receiver)
                       @@ C.ClientInboxes)
    ] @@ C

MarkReceivedWithRemover(C, receiver, msg, receiverState, removeFromInbox(_, _)) ==
  [ LogicalTime |-> C.LogicalTime + 1,
    ClientInboxes |-> ((receiver :> removeFromInbox(msg, C.ClientInboxes[receiver]))
                       @@ C.ClientInboxes),
    MsgSteps |-> C.MsgSteps \union {[recvAt |-> C.LogicalTime + 1,
                                     receiverState |-> receiverState,
                                     payload |-> "" \* it's screwing up parsing
                                     ] @@ msg.rawMsg}
    ] @@ C
=====
