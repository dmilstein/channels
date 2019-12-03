---- MODULE ChannelsDuplicatesTest ----

EXTENDS TLC, FiniteSets

INSTANCE ChannelsDuplicates WITH MaxDupes <- 2

Eq_(actual, expected) == Assert(actual = expected,
                                <<"Actual:", actual, "Expected:", expected>>)

Clients == {"a", "b"}
DuplicatesChannel == InitChannels(Clients)

ASSUME Eq_(HasMessage(DuplicatesChannel, "a"), FALSE)
ASSUME Eq_(HasMessage(DuplicatesChannel, "b"), FALSE)

DuplicatesOneSent == Send(DuplicatesChannel, "a", "b", "a message", "a label", "a state")

ASSUME Eq_(HasMessage(DuplicatesOneSent, "a"), FALSE)
ASSUME Eq_(HasMessage(DuplicatesOneSent, "b"), TRUE)

MsgSet == NextMessages(DuplicatesOneSent, "b")

ASSUME Eq_(Cardinality(MsgSet), 2)
SingleMsg == CHOOSE m \in MsgSet: m.numCopies = 1
DoubleMsg == CHOOSE m \in MsgSet: m.numCopies = 2

ASSUME Eq_(Payload(SingleMsg), "a message")
ASSUME Eq_(Payload(DoubleMsg), "a message")

PostSingleReceive == MarkMessageReceived(DuplicatesOneSent, "b",
                                         SingleMsg, "b state")

ASSUME Eq_(HasMessage(PostSingleReceive, "a"), FALSE)
ASSUME Eq_(HasMessage(PostSingleReceive, "b"), FALSE)

PostDoubleReceive == MarkMessageReceived(DuplicatesOneSent, "b",
                                         DoubleMsg, "b state")

ASSUME Eq_(HasMessage(PostDoubleReceive, "a"), FALSE)
ASSUME Eq_(HasMessage(PostDoubleReceive, "b"), TRUE)

MsgSetPostDoubleReceive == NextMessages(PostDoubleReceive, "b")

ASSUME Eq_(Cardinality(MsgSetPostDoubleReceive), 1)
MsgRoundTwo == CHOOSE m \in MsgSetPostDoubleReceive: m.numCopies = 1
ASSUME Eq_(MsgRoundTwo.numCopies, 1)

ASSUME Eq_(Payload(MsgRoundTwo), "a message")

PostReceiveRoundTwo == MarkMessageReceived(PostDoubleReceive, "b",
                                           MsgRoundTwo, "b state")

ASSUME Eq_(HasMessage(PostReceiveRoundTwo, "a"), FALSE)
ASSUME Eq_(HasMessage(PostReceiveRoundTwo, "b"), FALSE)


\* Check for proper collection of msg steps
ASSUME Eq_(Cardinality(PostDoubleReceive.MsgSteps), 1)

TheStep == CHOOSE s \in PostDoubleReceive.MsgSteps: TRUE
ASSUME Eq_(TheStep.sendAt, 1)
ASSUME Eq_(TheStep.senderState, "a state")
ASSUME Eq_(TheStep.msgLabel, "a label")
ASSUME Eq_(TheStep.recvAt, 2)
ASSUME Eq_(TheStep.receiverState, "b state")

ASSUME Eq_(Cardinality(PostReceiveRoundTwo.MsgSteps), 2)

StepOne == CHOOSE s \in PostReceiveRoundTwo.MsgSteps: s.recvAt = 2
ASSUME Eq_(StepOne.sendAt, 1)
ASSUME Eq_(StepOne.senderState, "a state")
ASSUME Eq_(StepOne.msgLabel, "a label")
ASSUME Eq_(StepOne.receiverState, "b state")

StepTwo == CHOOSE s \in PostReceiveRoundTwo.MsgSteps: s.recvAt = 3
ASSUME Eq_(StepTwo.sendAt, 1)
ASSUME Eq_(StepTwo.senderState, "a state")
ASSUME Eq_(StepTwo.msgLabel, "a label")
ASSUME Eq_(StepTwo.receiverState, "b state")

======
