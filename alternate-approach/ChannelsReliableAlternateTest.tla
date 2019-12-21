---- MODULE ChannelsReliableAlternateTest ----

EXTENDS TLC, FiniteSets

INSTANCE ChannelsAlternate WITH MaxDupes <- 2

Eq_(actual, expected) == Assert(actual = expected,
                                <<"Actual:", actual, "Expected:", expected>>)

ASSUME Eq_(AllSeqs({"a"}, 2), { <<"a">>, <<"a", "a">> })

Clients == {"a", "b"}

EmptyFunc == [ x \in {} |-> TRUE ]

ReliableChannel == InitChannels(Clients, EmptyFunc)

ASSUME Eq_(ReliableChannel, InitChannels(Clients, [ duplicates |-> FALSE ]))

FirstSendSet == Send(ReliableChannel,
                     "a", "b", "a message", "a label", "a state")

ASSUME Eq_(Cardinality(FirstSendSet), 1)
ASSUME Eq_({ HasMessage(C, "a") : C \in FirstSendSet }, {FALSE})
ASSUME Eq_({ HasMessage(C, "b") : C \in FirstSendSet }, {TRUE})
ASSUME Eq_({ NumMessages(C, "a") : C \in FirstSendSet }, {0})
ASSUME Eq_({ NumMessages(C, "b") : C \in FirstSendSet }, {1})

ReliableOneSent == CHOOSE x \in FirstSendSet: TRUE

ASSUME Eq_(NextMessage(ReliableOneSent, "b"), "a message")

PostReceive == MarkMessageReceived(ReliableOneSent, "b", "b state")
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
