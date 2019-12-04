---- MODULE ChannelsAtLeastOnceTest ----

EXTENDS TLC, FiniteSets

INSTANCE ChannelsAtLeastOnce WITH MaxDupes <- 2

Eq_(actual, expected) == Assert(actual = expected,
                                <<"Actual:", actual, "Expected:", expected>>)

Clients == {"a", "b"}
AtLeastOnceChannel == InitChannels(Clients)

ASSUME Eq_(HasMessage(AtLeastOnceChannel, "a"), FALSE)
ASSUME Eq_(HasMessage(AtLeastOnceChannel, "b"), FALSE)

AtLeastOnceOneSent == Send(AtLeastOnceChannel, "a", "b",
                           "message 1", "a label 1", "a state 1")

AtLeastOnceTwoSent == Send(AtLeastOnceOneSent, "a", "b",
                           "message 2", "a label 2", "a state 2")

ASSUME Eq_(HasMessage(AtLeastOnceTwoSent, "a"), FALSE)
ASSUME Eq_(HasMessage(AtLeastOnceTwoSent, "b"), TRUE)

MsgSet == NextMessages(AtLeastOnceTwoSent, "b")

ASSUME Eq_(Cardinality(MsgSet), 4)
ASSUME Eq_(Cardinality({ m \in MsgSet: m.numCopies = 1 }), 2)
ASSUME Eq_(Cardinality({ m \in MsgSet: m.numCopies = 2 }), 2)

ASSUME Eq_(Cardinality({ m \in MsgSet: Payload(m) = "message 1" }), 2)
ASSUME Eq_(Cardinality({ m \in MsgSet: Payload(m) = "message 2" }), 2)

SecondSelector(m) == Payload(m) = "message 2" /\ m.numCopies = 2

ASSUME Eq_(Cardinality({ m \in MsgSet: SecondSelector(m)}),
           1)

SecondMsgWithDupe == CHOOSE m \in MsgSet: SecondSelector(m)

PostFirstReceive == MarkMessageReceived(AtLeastOnceTwoSent, "b",
                                        SecondMsgWithDupe, "b state 1")

ASSUME Eq_(HasMessage(PostFirstReceive, "a"), FALSE)
ASSUME Eq_(HasMessage(PostFirstReceive, "b"), TRUE)

MsgSet2 == NextMessages(PostFirstReceive, "b")

ASSUME Eq_(Cardinality(MsgSet2), 3)
ASSUME Eq_(Cardinality({ m \in MsgSet2: m.numCopies = 1 }), 2)
ASSUME Eq_(Cardinality({ m \in MsgSet2: m.numCopies = 2 }), 1)

ASSUME Eq_(Cardinality({ m \in MsgSet2: Payload(m) = "message 1" }), 2)
ASSUME Eq_(Cardinality({ m \in MsgSet2: Payload(m) = "message 2" }), 1)

SecondSelector2(m) == Payload(m) = "message 2" /\ m.numCopies = 1
ASSUME Eq_(Cardinality({ m \in MsgSet2: SecondSelector2(m)}),
           1)

SecondMsgRound2 == CHOOSE m \in MsgSet2: SecondSelector2(m)

PostSecondReceive == MarkMessageReceived(PostFirstReceive, "b",
                                         SecondMsgRound2, "b state 2")

ASSUME Eq_(HasMessage(PostSecondReceive, "a"), FALSE)
ASSUME Eq_(HasMessage(PostSecondReceive, "b"), TRUE)

MsgSet3 == NextMessages(PostSecondReceive, "b")

ASSUME Eq_(Cardinality(MsgSet3), 2)
ASSUME Eq_(Cardinality({ m \in MsgSet3: m.numCopies = 1 }), 1)
ASSUME Eq_(Cardinality({ m \in MsgSet3: m.numCopies = 2 }), 1)

ASSUME Eq_(Cardinality({ m \in MsgSet3: Payload(m) = "message 1" }), 2)
ASSUME Eq_(Cardinality({ m \in MsgSet3: Payload(m) = "message 2" }), 0)

\* Check for proper collection of msg steps
ASSUME Eq_(Cardinality(PostFirstReceive.MsgSteps), 1)

TheStep == CHOOSE s \in PostFirstReceive.MsgSteps: TRUE
ASSUME Eq_(TheStep.sendAt, 2)
ASSUME Eq_(TheStep.senderState, "a state 2")
ASSUME Eq_(TheStep.msgLabel, "a label 2")
ASSUME Eq_(TheStep.recvAt, 3)
ASSUME Eq_(TheStep.receiverState, "b state 1")

ASSUME Eq_(Cardinality(PostSecondReceive.MsgSteps), 2)

StepOne == CHOOSE s \in PostSecondReceive.MsgSteps: s.recvAt = 3
ASSUME Eq_(StepOne.sendAt, 2)
ASSUME Eq_(StepOne.senderState, "a state 2")
ASSUME Eq_(StepOne.msgLabel, "a label 2")
ASSUME Eq_(StepOne.receiverState, "b state 1")

StepTwo == CHOOSE s \in PostSecondReceive.MsgSteps: s.recvAt = 4
ASSUME Eq_(StepTwo.sendAt, 2)
ASSUME Eq_(StepTwo.senderState, "a state 2")
ASSUME Eq_(StepTwo.msgLabel, "a label 2")
ASSUME Eq_(StepTwo.receiverState, "b state 2")

======
