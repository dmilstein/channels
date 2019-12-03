Provide a data structure to model message passing with configurable guarantees -- reliable delivery, duplicates, out-of-order, duplicates **and** out of order ("at least once").

By design, all the versions of the Channels data strucures provide the same interface -- so that it's straightforward to change the messaging behavior for an algorithm and see how it behaves, merely by adjusting the Channels module included via INSTANCE.

The internal state of the various Channels data structures are designed such that, on a failure, the message history and timing can be parsed from the TLC output (which allows a timeline diagram to be written out as an SVG).

The key operators that work on Channels are:

 - `InitChannels<type>(clients)`
    where type is one of {`Reliable`, `Duplicates`, `OutOfOrder`, `AtLeastOnce`}, and `clients` is a set of client process names

 - `Send(channels, sender, receiver, msg, msgLabel, senderState)` - send a single message from one client to another, where

   - `sender` is the name of the sending client (usually self)
   - `receiver` is the name of the destination client
   - `msg` is the message to send, which is opaque to the Channels data structure
   - `msgLabel` is a string describing the message, for the timeline diagram
   - `senderState` is a string describing the state of the sender, for the timeline diagram

 - `HasMessage(channels, receiver)` - does a given client have any messages waiting for it?

 - `NextMessages(channels, receiver)` - the set of (wrapped) message a given client **could** see next.
 This is how non-determinism is expressed to users of Channels -- they are expected to
 choose one of these messages, non-deterministically, see example below.

 - `MarkMessageReceived(channels, receiver, msg, receiverState)` - update
 channels to show a specific (wrapped) message was received, passing in a `receiverState` to annotate the timeline diagram. Note that the client process should always call this, after receiving a message. Specifically, even if you wish to see duplicates, you should still call `MarkMessageReceived` -- the Channels data structure will take care of ensuring that the proper numnber of duplicates are still generated.

The messages received by `NextMessages()` are "wrapped" (which is necessary for `MarkMessageReceived()` to function). To obtain an underlying message inside a receive loop, call:

- `Payload(msg)`

## Example of Use

First, construct one of the versions of the Channels data structures, passing in the set of client process names, and store it in a global variable accessible by all clients:

    INSTANCE ChannelsReliable

    Clients == {"client1", "client2"}

    variables
      Channels = InitChannels(Clients);

To send a message, update that global Channels variable inside the PlusCal algorithm, as so:

    Channels := Send(Channels, sender, receiver, msg,
                     "label for the message",
                     "label for state of sender at send time")

To receive and process messages, use the following idiom:

    await HasMessage(Channels, self);
    with wrapped_msg \in NextMessages(Channels, self) do
      with msg = Payload(wrapped_msg) do
        \* process msg
      end with;
      Channels := MarkMessageReceived(Channels, self, wrapped_msg, receiverState)
