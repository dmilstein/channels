---- MODULE ChannelsDupeAlternateTest ----

EXTENDS TLC, FiniteSets

INSTANCE ChannelsAlternate WITH MaxDupes <- 2

Eq_(actual, expected) == Assert(actual = expected,
                                <<"Actual:", actual, "Expected:", expected>>)

ASSUME Eq_(AllSeqs({"a"}, 2), { <<"a">>, <<"a", "a">> })

Clients == {"a", "b"}

DupeChannel == InitChannels(Clients, [ duplicates |-> TRUE ])

ASSUME Eq_(HasMessage(DupeChannel, "a"), FALSE)
ASSUME Eq_(HasMessage(DupeChannel, "b"), FALSE)

DupeFirstSendSet == Send(DupeChannel,
                         "a", "b", "a message", "a label", "a state")

ASSUME Eq_(Cardinality(DupeFirstSendSet), 2)
ASSUME Eq_({ HasMessage(C, "a") : C \in DupeFirstSendSet }, {FALSE})
ASSUME Eq_({ HasMessage(C, "b") : C \in DupeFirstSendSet }, {TRUE})
ASSUME Eq_({ NumMessages(C, "a") : C \in DupeFirstSendSet }, {0})
ASSUME Eq_({ NumMessages(C, "b") : C \in DupeFirstSendSet }, {1, 2})

SingleCopy == CHOOSE C \in DupeFirstSendSet: NumMessages(C, "b") = 1
Msg1 == NextMessage(SingleCopy, "b")

ASSUME Eq_(Msg1, "a message")
SingleCopyPostReceive == MarkMessageReceived(SingleCopy, "b", "post-send state")

ASSUME Eq_(NumMessages(SingleCopyPostReceive, "b"), 0)
ASSUME Eq_(Cardinality(SingleCopyPostReceive.MsgSteps), 1)

DoubleCopy == CHOOSE C \in DupeFirstSendSet: NumMessages(C, "b") = 2
Msg2 == NextMessage(DoubleCopy, "b")

ASSUME Eq_(Msg2, "a message")
DoubleCopyPostReceive == MarkMessageReceived(DoubleCopy, "b", "b state 1")

ASSUME Eq_(NumMessages(DoubleCopyPostReceive, "b"), 1)
ASSUME Eq_(Cardinality(DoubleCopyPostReceive.MsgSteps), 1)

PostReceiveRoundTwo == MarkMessageReceived(DoubleCopyPostReceive, "b", "b state 2")

\* Check for proper collection of msg steps
ASSUME Eq_(Cardinality(DoubleCopyPostReceive.MsgSteps), 1)

TheStep == CHOOSE s \in DoubleCopyPostReceive.MsgSteps: TRUE
ASSUME Eq_(TheStep.sendAt, 1)
ASSUME Eq_(TheStep.senderState, "a state")
ASSUME Eq_(TheStep.msgLabel, "a label")
ASSUME Eq_(TheStep.recvAt, 2)
ASSUME Eq_(TheStep.receiverState, "b state 1")

ASSUME Eq_(Cardinality(PostReceiveRoundTwo.MsgSteps), 2)

StepOne == CHOOSE s \in PostReceiveRoundTwo.MsgSteps: s.recvAt = 2
ASSUME Eq_(StepOne.sendAt, 1)
ASSUME Eq_(StepOne.senderState, "a state")
ASSUME Eq_(StepOne.msgLabel, "a label")
ASSUME Eq_(StepOne.receiverState, "b state 1")

StepTwo == CHOOSE s \in PostReceiveRoundTwo.MsgSteps: s.recvAt = 3
ASSUME Eq_(StepTwo.sendAt, 1)
ASSUME Eq_(StepTwo.senderState, "a state")
ASSUME Eq_(StepTwo.msgLabel, "a label")
ASSUME Eq_(StepTwo.receiverState, "b state 2")

======
