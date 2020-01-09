## Introduction

The Channels data structures provide message-passing implementations with two goals - first, to make it easy for TLA spec writers to model distributed systems with various kinds of message passing guarantees; second, to make it possible to create visualizations of message-passing flows.

As an example, the below specifies a set of PlusCal processes which implement a distributed counter, which can be incremented or decremented:

```tla
fair process client \in Clients
  variables
    MsgsSent = 0,
    GlobalCount = 0;
  begin ClientLoop:
    while TRUE do
      either
        await MsgsSent < MsgsPerClient;
        with Increment \in {-1, 1} do
          if GlobalCount + Increment < 0 then
            skip;
          else
            GlobalCount := GlobalCount + Increment;
            C := Send(C, self, Other(self), Increment, Label(Increment), GlobalCount);
            MsgsSent := MsgsSent + 1;
          end if;
        end with;
      or
        await HasMessage(C, self);
        with wrappedMsg \in NextMessages(C, self) do
          GlobalCount := GlobalCount + Payload(wrappedMsg);
          C := MarkMessageReceived(C, self, wrappedMsg, GlobalCount)
        end with;
      or
        skip;
      end either;
    end while;
end process;
```

(full code available in `examples/two_client_inc_dec.pcal`)

Although each client only sends a negative increment when its version of the overall value is positive, the overall system can still reach a state with a negative counter.

To view the timeline of how that can happen, run `render_timeline.py` on a failed run: E.g., if using the scripts from [tla-bin](https://github.com/pmer/tla-bin):

    > tlc SomeSpec.tla > SomeSpec.out
    > ./render_timeline.py SomeSpec.out > SomeSpec.svg

For the above, this gives this timeline:

![Counter: Two Clients, Inc/Dec](examples/images/two_client_inc_dec.svg)

The dashed line which represents a message which has been sent but not yet received.


## Details

Channels provides a data structure to model message passing with configurable guarantees -- reliable delivery, duplicates, out-of-order, duplicates **and** out of order ("at least once").

All the versions of the Channels data strucures provide the same interface -- so that it's straightforward to change the messaging behavior for an algorithm and see how it behaves, merely by adjusting the Channels module included via EXTENDS or INSTANCE.

The various Channels data structures record the history of messages sent such that, on a failure, the message history and timing can be parsed from the TLC output. The associated python script (which includes a basic TLA parser, in python) can then render a timeline diagram as an SVG. (Note: it's possible that this recording of history will cause some form of exponential blow up on a state space which would otherwise be tractable).

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
 channels to show a specific (wrapped) message was received, passing in a `receiverState` to annotate the timeline diagram. Note that the client process should always call this, after receiving a message. Specifically, even if you wish to see duplicates, you should still call `MarkMessageReceived` -- the Channels data structure will take care of ensuring that the proper number of duplicates are still generated.

The messages received by `NextMessages()` are "wrapped" (which is necessary for `MarkMessageReceived()` to function). To obtain an underlying message inside a receive loop, call:

- `Payload(msg)`

## How To Use

First, construct one of the versions of the Channels data structures, passing in the set of client process names, and store it in a global variable accessible by all clients:

```tla
INSTANCE ChannelsReliable

Clients == {"client1", "client2"}

variables
  Channels = InitChannels(Clients);
```

To send a message, update that global Channels variable inside a specific process in the PlusCal algorithm, as so:

```tla
Channels := Send(Channels, self, receiver, msg,
                 "label for the message",
                 "label for state of sender at send time")
```

To receive and process messages, use the following idiom:

```tla
await HasMessage(Channels, self);
with wrapped_msg \in NextMessages(Channels, self) do
  with msg = Payload(wrapped_msg) do
    \* process msg
  end with;
  Channels := MarkMessageReceived(Channels, self, wrapped_msg, receiverState)
```

To construct the svg image on a failed run, capture the state trace in a file. E.g., if using the scripts from [tla-bin](https://github.com/pmer/tla-bin):

    > tlc SomeSpec.tla > SomeSpec.out
    > ./render_timeline.py SomeSpec.out > SomeSpec.svg

(If you want to see a timeline diagram for a "successful" run, it's generally straightforward to set up a failing Invariant or Property, so that you'll produce a state trace to render.)

## Timeline Diagram Examples

In the `examples/` directory is a series of specs modeling a distributed counter, using various forms of the Channels.

The general set up is: multiple peer clients, each of which is tracking a local copy of an overall, globally shared counter value. Local requests to increment the counter can arrive at any client, which will increment its own value and then attempt to communicate the increment to the other clients.

In most cases, the examples just use a pair of clients.

For the diagrams:

 - Time flows from the top to the bottom

 - The labels adjacent to the vertical timelines specify each client's local state, immediately *after* sending or receiving a message

 - The labels on the diagonal arrows specify the message payloads

 - Dashed diagonal lines, if present, represent messages sent but not received

### `two_client_reliable_channel.pcal`

This is the simplest one, where the Channel reliably delivers every message, in-order, without duplicates. Thus, each client, when it needs to update the counter, simply sends a single increment message to the others.

![Counter: Two Clients, Reliable Channel](examples/images/two_client_reliable_channel.svg)

Note: in this case, to get a state trace to render, we have to specify a property we don't expect to be true, even if the counter implementation was correct.

    FailingProperty == <>[](\A c \in Clients:
                            GlobalCount[c] = MsgsPerClient * Cardinality(Clients) + 1)

### `two_client_dupe_channel.pcal`

This is the same client strategy as above, but with the Channels implementation switched to one that will inject duplicates of a message. And, now TLC finds a run where the final values are inconsistent.

![Counter: Two Clients, Duplicating Channel](examples/images/two_client_dupe_channel.svg)

### `two_client_track_last_id.pcal` (with just duplicates)

The Duplicating channel is the simplest form of duplicates -- any duplicate messages from a given client will be delivered in sequence before any other message from that client arrives (which can happen if, e.g. the sending client waits for an acknowledgment of each message before sending the next -- if messages drop and are re-sent, you can get sequential duplicates, but you'll never see messages out-of-order).

Thus, we can make the distributed counter resilient to this very simple form of duplicate delivery of messages, by adjusting the TLA code to attach a (per-client) sequence id to every message sent, and having the receiving client discard a message if the most recent message processed had the same sequence id:

![Counter: Two Clients, Track Last ID, Just Dupes](examples/images/two_client_track_last_id_just_dupes.svg)

Note how, in the above diagram, the per-client state (adjacent to the vertical timelines), does **not** increment when a message is received with the same `id` as the previously received message.

Also, for this one, we're explicitly labeling each message, instead of just using the default rendering:

    Label(msg) == ToString(msg.msg) \o " (id: " \o ToString(msg.seq_id) \o ")"

### `two_client_track_last_id.pcal` (with at-least-once delivery)

Now, if we switch the above code to the at-least-once channel implementation, we'll see that this implementation no longer works:

![Counter: Two Clients, Track Last ID, At-Least-Once](examples/images/two_client_track_last_id_at_least_once.svg)


### `three_client_counter.pcal`

The svg rendering will work for more than two clients, though the diagrams can get a bit harder to read, naturally:

![Counter: Three Clients](examples/images/three_client_counter.svg)
