#!/usr/bin/python
"""
Render timeline from an annotated TLC trace as an SVG file. Write to stdout.
"""

import re
import sys

from jinja2 import Environment, PackageLoader

from tlaparser import parse_tla_state

env = Environment(loader=PackageLoader('tlaparser', 'templates'))

TimelineSpacing = 200
StepSpacing = 55
LeftMargin = 50
TopMargin = 20

clients = ["client1", "client2"] # hardcoding for the win!!!

def x_pos(client_name):
    return LeftMargin + (client_idx(client_name) * TimelineSpacing)

def y_pos(sendAt):
    return TopMargin + (sendAt * StepSpacing)

def client_idx(client_name):
    return clients.index(client_name)

class MsgStep(object):

    STEP_IDX = 0

    def __init__(self, sender, receiver, msg, sendAt, recvAt,
                     senderState, receiverState,
                     received):
        self.recvAt = recvAt # hack so I can do max recvAt elsewhere
        self.msg = msg

        self.step_idx = MsgStep.STEP_IDX
        MsgStep.STEP_IDX += 1

        self.x1 = x_pos(sender)
        self.y1 = y_pos(sendAt)
        self.x2 = x_pos(receiver)
        self.y2 = y_pos(recvAt)

        self.received = received
        if not received:
            receiverState = ''
            self.x2 = self.x1 + abs(self.x1 - self.x2)/2
            self.y2 = self.y1 + abs(self.y1 - self.y2)/2

        # The line for the label has to run left-to-right, for the writing
        x_positions = [ self.x1, self.x2 ]
        self.label_x1 = min(x_positions)
        self.label_x2 = max(x_positions)
        # Ugh, but whatever
        if self.label_x1 == x_pos(sender):
            self.label_y1 = self.y1
            self.label_y2 = self.y2
            self.label_offset_pct = "15"
            self.left_state = senderState
            self.right_state = receiverState
        else:
            self.label_y1 = self.y2
            self.label_y2 = self.y1
            self.label_offset_pct = "65"
            self.left_state = receiverState
            self.right_state = senderState

class ClientLine(object):
    def __init__(self, client, num_steps):
        self.client = client
        self.idx = client_idx(client)
        self.num_steps = num_steps

    def x1(self): return x_pos(self.client)
    def y1(self): return TopMargin
    def x2(self): return x_pos(self.client)
    def y2(self): return TopMargin + (self.num_steps * StepSpacing)

def render_msg_steps(msg_steps):
    template = env.get_template('tlc_timeline.svg')
    return template.render(client_lines=[ClientLine(c, max_step(msg_steps))
                                         for c in clients],
                           msg_steps=msg_steps)

def max_step(msg_steps):
    return max([m.recvAt for m in msg_steps])

state_re = re.compile(r'State \d+:.*?\n(.+?)\n\n', re.DOTALL)

def extract_states(tlc_output):
    """
    Return a list of dicts representing the states in the TLC output
    """
    return [ parse_tla_state(m.group(1))
             for m in state_re.finditer(tlc_output)]

msg_steps_re = re.compile(r'MsgSteps .*? (\{.*?\})', re.DOTALL) # .*? matches = or |->
# Ugh, the regex below is kinda fragile -- depends on the trailing ],
# At some point, maybe write a parser
client_inbox_re = re.compile(r'ClientInboxes |->\s+\[(.*?)\],', re.DOTALL)
msg_re = re.compile(r'\[(.*?)\]')

def extract_msg_steps(tlc_output):
    """Return a list of message steps from the output of a TLC model run,

    when the abstract message passing machinery is used.

    For messages which were sent but not yet received (i.e. still in
    ClientInboxes), we set the "received" flag to False, and arbitrarily
    set their recvAt to be one greater than the sendAt.
    """
    # Grab the last one, which should have all the steps
    final_state = extract_states(tlc_output)[-1]
    all_msg_steps = final_state['C']['MsgSteps']

    #client_inbox_str = client_inbox_re.findall(tlc_output)[-1].replace("\n", " ")
    #all_unreceived_steps = msg_re.findall(client_inbox_str)
    return (
        [ extract_one_step(ms, True) for ms in all_msg_steps ]  #+
        #[ extract_one_step(ms, False) for ms in all_unreceived_steps ]
        )

def extract_one_step(step, received=True):
    "Return a MsgStep tuple from the parsed representation of a single step"
    sendAt = step['sendAt']
    if received:
        recvAt = step["recvAt"]
    else:
        recvAt = sendAt + 2
    return MsgStep(step["sender"],
                   step["receiver"],
                   step["msgLabel"],
                   sendAt,
                   recvAt,
                   step["senderState"],
                   step["receiverState"],
                   received)

if __name__ == '__main__':
    contents = open(sys.argv[1]).read()
    # import pprint
    # pp = pprint.PrettyPrinter(indent = 2)
    # pp.pprint(extract_states(contents)[-1])
    print(render_msg_steps(extract_msg_steps(contents)))
    #print(extract_msg_steps(contents))
