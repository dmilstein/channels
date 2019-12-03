---- MODULE ChannelsReliableTest ----

EXTENDS FiniteSets, ChannelsReliable, TLC

Eq_(actual, expected) == Assert(actual = expected,
                                <<"Actual:", actual, "Expected:", expected>>)

Clients == {"a", "b"}
ReliableChannel == InitChannels(Clients)

ASSUME Eq_(HasMessage(ReliableChannel, "a"), FALSE)
ASSUME Eq_(HasMessage(ReliableChannel, "b"), FALSE)

ReliableOneSent == Send(ReliableChannel, "a", "b", "a message", "a label", "a state")

ASSUME Eq_(HasMessage(ReliableOneSent, "a"), FALSE)
ASSUME Eq_(HasMessage(ReliableOneSent, "b"), TRUE)

MsgSet == NextMessages(ReliableOneSent, "b")

ASSUME Eq_(Cardinality(MsgSet), 1)
TheMsg == CHOOSE m \in MsgSet: TRUE
ASSUME Eq_(Payload(TheMsg), "a message")

PostReceive == MarkMessageReceived(ReliableOneSent, "b", TheMsg, "b state")
ASSUME Eq_(HasMessage(PostReceive, "a"), FALSE)
ASSUME Eq_(HasMessage(PostReceive, "b"), FALSE)

ASSUME Eq_(Cardinality(PostReceive.MsgSteps), 1)
TheStep == CHOOSE s \in PostReceive.MsgSteps: TRUE
ASSUME Eq_(TheStep.sendAt, 1)
ASSUME Eq_(TheStep.senderState, "a state")
ASSUME Eq_(TheStep.msgLabel, "a label")
ASSUME Eq_(TheStep.recvAt, 2)
ASSUME Eq_(TheStep.receiverState, "b state")

======
