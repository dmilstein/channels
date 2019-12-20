---- MODULE ChannelsAlternate ----

\* Alternate version of Channels, to see how much work we're talking about here.

EXTENDS Integers, TLC, FiniteSets, Sequences

\* How many times can a single message be duplicated?
CONSTANT MaxDupes

\* All the Channels implementations store client inboxes inside a map from
\* names to inboxes

InitChannels(clients, flags) ==
  [ ClientInboxes |-> [ c \in clients |-> <<>> ],
    Flags |-> flags @@ [ duplicates |-> FALSE ],
    LogicalTime |-> 0,
    MsgSteps |-> {},
    NextMsgId |-> 0 \* not used in all implementations
    ]

HasMessage(C, client) == C.ClientInboxes[client] /= <<>>
NumMessages(C, client) == Len(C.ClientInboxes[client])

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

AppendToInbox(C, msgSeq, receiver) == C.ClientInboxes[receiver] \o msgSeq

\* Return a set of all sequences of <= n elements chosen from Set
AllSeqs(S, n) == UNION {[1..m -> S] : m \in 1..n}

\* Return a set of distinct Channels objects, covering all the ways the new
\* message could be added to client inboxes.
Send(C, sender, receiver, msg, msgLabel, senderState) ==
  LET wrappedMsg == Message(sender,
                            receiver,
                            msg,
                            msgLabel,
                            C.LogicalTime + 1,
                            senderState) IN
  LET numDupes == IF C.Flags.duplicates THEN MaxDupes ELSE 1 IN
  LET seqsToAdd == AllSeqs({wrappedMsg}, numDupes) IN
  {[ LogicalTime |-> C.LogicalTime + 1,
     NextMsgId |-> C.NextMsgId + 1,
     ClientInboxes |-> (receiver :> AppendToInbox(C,
                                                  msgSeq,
                                                  receiver)
                        @@ C.ClientInboxes)
    ] @@ C : msgSeq \in seqsToAdd}

NextMessage(C, receiver) == Head(C.ClientInboxes[receiver]).payload

\* Mark the current message for receiver as received
MarkMessageReceived(C, receiver, receiverState) ==
  [ LogicalTime |-> C.LogicalTime + 1,
    ClientInboxes |-> ((receiver :> Tail(C.ClientInboxes[receiver]))
                       @@ C.ClientInboxes),
    MsgSteps |-> C.MsgSteps \union {[recvAt |-> C.LogicalTime + 1,
                                     receiverState |-> receiverState,
                                     payload |-> "" \* it's screwing up parsing
                                     ] @@ Head(C.ClientInboxes[receiver])}
    ] @@ C
=====
