---- MODULE ChannelsTest ----
\* Since Channels has no temporal actions, we can test it with ASSUME

EXTENDS FiniteSets, Channels, TLC

Eq_(actual, expected) == Assert(actual = expected,
                                <<"Actual:", actual, "Expected:", expected>>)

ASSUME LET C == InitChannels({"a", "b"}) IN
  /\ Eq_(C.ClientInboxes.a, <<>>)
  /\ Eq_(C.ClientInboxes.b, <<>>)

ASSUME LET msg_set == Expand(Wrap("abc", 1)) IN
  /\ Eq_(Cardinality(msg_set), MaxDupes)
  /\ \A n \in 1..MaxDupes: \E m \in msg_set: m.numCopies = n

\* Tests for duplicate sends
OneSentMessage == LET C == InitChannels({"a", "b"})
                  IN Send_D(C, "a", "b", "a message", "a labeled message", 1)

ASSUME Eq_(Payload(Head(OneSentMessage.ClientInboxes.b)), "a message")
ASSUME Eq_(Head(OneSentMessage.ClientInboxes.b).numCopies, NULL)

MsgSet == NextMessages(OneSentMessage, "b")
ASSUME Eq_(Cardinality(MsgSet), MaxDupes)
ASSUME \A n \in 1..MaxDupes: \E m \in MsgSet: m.numCopies = n

ChannelsPostReceive == LET C == OneSentMessage
IN LET MS == NextMessages(C, "b")
IN { MarkMessageReceived(C, "b", m, 1): m \in MS }

\* ASSUME Eq_(ChannelsPostReceive, {}) \* to view for debugging

ASSUME Eq_({Head(c.ClientInboxes.b).numCopies:
           c \in { c \in ChannelsPostReceive: HasMessage(c, "b")}},
           1..MaxDupes-1)

ASSUME Eq_(Cardinality({c \in ChannelsPostReceive: ~HasMessage(c, "b")}),
           1)

\* XXX Add a test to verify that the duplicating sends preserve order
\* Add a test for next message on empty inbox, wrap on empty inbox

\* Out of order sends - verify duplication still works
OOO_Channel_Sent == LET C == InitChannels_U({"a", "b"})
  IN Send_U(C, "a", "b", "a message", "a labeled message", 1)

ASSUME Eq_(Payload(RandomElement(OOO_Channel_Sent.ClientInboxes.b)),
           "a message")

OOO_MsgSet == NextMessages_U(OOO_Channel_Sent, "b")

\* ASSUME Eq_(msg_set, {})
ASSUME Eq_(Cardinality(OOO_MsgSet), MaxDupes)
ASSUME \A n \in 1..MaxDupes: \E m \in OOO_MsgSet: m.numCopies = n

OOO_ChannelsPostReceive == { MarkMessageReceived_U(OOO_Channel_Sent, "b", m, 1):
                             m \in OOO_MsgSet }

ASSUME Eq_({RandomElement(NextMessages_U(c, "b")).numCopies:
             c \in { c \in OOO_ChannelsPostReceive: HasMessage_U(c, "b")}},
            1..MaxDupes-1)

ASSUME Eq_(Cardinality({c \in OOO_ChannelsPostReceive: ~HasMessage_U(c, "b")}),
           1)

\* Out of order -- verify out of order works
OOO_Channel_Sent_2 == LET C == InitChannels_U({"a", "b"})
  IN LET C2 == Send_U(C, "a", "b", "message 1", "a labeled message 1", 1)
  IN Send_U(C2, "a", "b", "message 2", "a labeled message 2", 1)

OOO_MsgSet_2 == NextMessages_U(OOO_Channel_Sent_2, "b")

ASSUME Eq_({Payload(msg) : msg \in OOO_MsgSet_2}, { "message 1", "message 2"})

======
