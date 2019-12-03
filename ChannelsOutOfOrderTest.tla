---- MODULE ChannelsOutOfOrderTest ----

EXTENDS TLC, FiniteSets

INSTANCE ChannelsOutOfOrder

Eq_(actual, expected) == Assert(actual = expected,
                                <<"Actual:", actual, "Expected:", expected>>)

Clients == {"a", "b"}
OutOfOrderChannel == InitChannels(Clients)

ASSUME Eq_(HasMessage(OutOfOrderChannel, "a"), FALSE)
ASSUME Eq_(HasMessage(OutOfOrderChannel, "b"), FALSE)

OutOfOrderOneSent == Send(OutOfOrderChannel, "a", "b",
                          "message 1", "a label", "a state")

ASSUME Eq_(HasMessage(OutOfOrderOneSent, "a"), FALSE)
ASSUME Eq_(HasMessage(OutOfOrderOneSent, "b"), TRUE)

OutOfOrderTwoSent == Send(OutOfOrderOneSent, "a", "b",
                          "message 2", "a label", "a state")

MsgSet == NextMessages(OutOfOrderTwoSent, "b")

ASSUME Eq_(Cardinality(MsgSet), 2)

ASSUME Eq_({ Payload(msg) : msg \in MsgSet },
           {"message 1", "message 2"})

MsgOne == CHOOSE m \in MsgSet: Payload(m) = "message 1"
MsgTwo == CHOOSE m \in MsgSet: Payload(m) = "message 2"

\* This forces the use of the Operators above (even though not very whitebox...)
ASSUME Eq_(MsgOne.msgId, 0)
ASSUME Eq_(MsgTwo.msgId, 1)

PostMsgOneReceive == MarkMessageReceived(OutOfOrderTwoSent, "b",
                                         MsgOne, "b state 1")

ASSUME Eq_(HasMessage(PostMsgOneReceive, "a"), FALSE)
ASSUME Eq_(HasMessage(PostMsgOneReceive, "b"), TRUE)

MsgSetRoundTwo == NextMessages(PostMsgOneReceive, "b")

ASSUME Eq_(Cardinality(MsgSetRoundTwo), 1)
MsgTwoRoundTwo == CHOOSE m \in MsgSetRoundTwo: Payload(m) = "message 2"

ASSUME Eq_(Payload(MsgTwoRoundTwo), "message 2")

PostReceiveRoundTwo == MarkMessageReceived(PostMsgOneReceive, "b",
                                           MsgTwoRoundTwo, "b state 2")

ASSUME Eq_(HasMessage(PostReceiveRoundTwo, "a"), FALSE)
ASSUME Eq_(HasMessage(PostReceiveRoundTwo, "b"), FALSE)

\* Check for proper collection of msg steps

ASSUME Eq_(Cardinality(PostReceiveRoundTwo.MsgSteps), 2)

StepOne == CHOOSE s \in PostReceiveRoundTwo.MsgSteps: s.recvAt = 3
ASSUME Eq_(StepOne.sendAt, 1)
ASSUME Eq_(StepOne.senderState, "a state")
ASSUME Eq_(StepOne.msgLabel, "a label")
ASSUME Eq_(StepOne.receiverState, "b state 1")

StepTwo == CHOOSE s \in PostReceiveRoundTwo.MsgSteps: s.recvAt = 4
ASSUME Eq_(StepTwo.sendAt, 2)
ASSUME Eq_(StepTwo.senderState, "a state")
ASSUME Eq_(StepTwo.msgLabel, "a label")
ASSUME Eq_(StepTwo.receiverState, "b state 2")

======
