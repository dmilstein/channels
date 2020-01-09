#!/usr/bin/python
"""
Render timeline from an annotated TLC trace as an SVG file. Write to stdout.
"""

from collections.abc import Mapping
import re
import sys

from jinja2 import Environment, PackageLoader

from tlaparser import parse_tla_state

env = Environment(loader=PackageLoader('tlaparser', 'templates'))

TimelineSpacing = 200
StepSpacing = 55
LeftMargin = 50
TopMargin = 20

def x_pos(client_name, clients):
    return LeftMargin + (client_idx(client_name, clients) * TimelineSpacing)

def y_pos(sendAt):
    return TopMargin + (sendAt * StepSpacing)

def client_idx(client_name, all_clients):
    return all_clients.index(client_name)

class MsgStep(object):
    "Collect key data from a parsed MsgStep, to support rendering"

    def __init__(self, parsed_step, received):
        self.sender        = parsed_step["sender"]
        self.receiver      = parsed_step["receiver"]
        self.msg           = parsed_step["msgLabel"]
        self.senderState   = parsed_step["senderState"]
        self.receiverState = parsed_step["receiverState"]

        self.received = received

        self.sendAt = parsed_step['sendAt']
        if received:
            self.recvAt = parsed_step["recvAt"]
        else:
            self.recvAt = self.sendAt + 2

    def get_line(self, all_clients):
        "Return a MessageLine object for rendering this step"
        return MsgLine(self, all_clients)

class MsgLine(object):
    LINE_IDX = 0 # To support id-based SVG path linking

    def __init__(self, msg_step, all_clients):
        self.line_idx = MsgLine.LINE_IDX
        MsgLine.LINE_IDX += 1

        self.msg = msg_step.msg

        self.x1 = x_pos(msg_step.sender, all_clients)
        self.y1 = y_pos(msg_step.sendAt)
        self.x2 = x_pos(msg_step.receiver, all_clients)
        self.y2 = y_pos(msg_step.recvAt)

        self.received = msg_step.received
        if not self.received:
            receiverState = ''
            self.x2 = self.x1 + abs(self.x1 - self.x2)/2
            self.y2 = self.y1 + abs(self.y1 - self.y2)/2

        # The line for the label has to run left-to-right, for the writing
        x_positions = [ self.x1, self.x2 ]
        self.label_x1 = min(x_positions)
        self.label_x2 = max(x_positions)
        # Ugh, but whatever
        if self.label_x1 == x_pos(msg_step.sender, all_clients):
            self.label_y1 = self.y1
            self.label_y2 = self.y2
            self.label_offset_pct = "15"
            self.left_state = msg_step.senderState
            self.right_state = msg_step.receiverState
        else:
            self.label_y1 = self.y2
            self.label_y2 = self.y1
            self.label_offset_pct = "65"
            self.left_state = msg_step.receiverState
            self.right_state = msg_step.senderState

class ClientLine(object):
    def __init__(self, client, all_clients, num_steps):
        self.client = client
        self.all_clients = all_clients
        self.idx = client_idx(client, all_clients)
        self.num_steps = num_steps

    def x1(self): return x_pos(self.client, self.all_clients)
    def y1(self): return TopMargin
    def x2(self): return x_pos(self.client, self.all_clients)
    def y2(self): return TopMargin + (self.num_steps * StepSpacing)

def render_msg_steps(msg_steps, clients):
    template = env.get_template('tlc_timeline.svg')
    return template.render(
        image_height=y_pos(max_step(msg_steps)) + 10,
        client_lines=[ClientLine(c,
                                 clients,
                                 max_step(msg_steps))
                      for c in clients],
        msg_lines=[m.get_line(clients) for m in msg_steps])

def max_step(msg_steps):
    return max([m.recvAt for m in msg_steps])

state_re = re.compile(r'State \d+:.*?\n(.+?)\n\n', re.DOTALL)

def parse_states(tlc_output):
    """
    Return a list of dicts representing the states in the TLC output
    """
    return [ parse_tla_state(m.group(1))
             for m in state_re.finditer(tlc_output)]

def extract_channels(final_state):
    "Find the Channels object in a state from TLC output"
    channel_keys = set(['ClientInboxes',
                        'LogicalTime',
                        'MsgSteps',
                        'NextMsgId'])

    for key, value in final_state.items():
        if isinstance(value, Mapping) and set(value.keys()) == channel_keys:
            return value

    raise Exception("Could not find Channels object in TLC output")

def extract_msg_steps(final_state):
    """Return a list of message steps from the final state a TLC model run,
    when the Channels message passing machinery was used.

    This both collects the sent + received messages from the MsgSteps dict, and
    also the sent-but-not-received messages in ClientInboxes.

    For messages which were sent but not yet received, we set the "received"
    flag to False, and arbitrarily set their recvAt to be one greater than the
    sendAt.
    """
    channels_obj = extract_channels(final_state)
    received_steps = channels_obj['MsgSteps']

    unreceived_steps = []
    for inbox in channels_obj['ClientInboxes'].values():
        unreceived_steps.extend([ wrapped['rawMsg'] for wrapped in inbox])

    return (
        [ MsgStep(ms, received=True) for ms in received_steps ]  +
        [ MsgStep(ms, received=False) for ms in unreceived_steps ]
        )

def extract_clients(final_state):
    """Return a list of the client names found in the final state output from a TLC
    model run, where the Channels machinery was used.

    The list will be alpha-sorted by client name
    """
    return sorted(list(extract_channels(final_state)['ClientInboxes'].keys()))

if __name__ == '__main__':
    tlc_output = open(sys.argv[1]).read()
    final_state = parse_states(tlc_output)[-1]
    msg_steps = extract_msg_steps(final_state)
    clients = extract_clients(final_state)
    print(render_msg_steps(msg_steps, clients))
