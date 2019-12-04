VENV=env-talk/bin

MODEL_TARGETS = $(patsubst %.pcal,%.model,$(wildcard *.pcal))
.PHONY: $(MODEL_TARGETS)
#.PHONY: wire.model

# wire.tla: wire.pcal
# 	cp wire.pcal wire.tla && pcal wire.tla

Channels%Test: Channels%Test.tla ChannelsUtils.tla
	tlc $@

%.tla: %.pcal
	cp $< $@ && pcal -nocfg $@

# One problem with this rule is that is "successfully" builds the .out file on
# failures, and thus rebuilds the .svg file, so I don't get the right rebuild
# behavior, and have to like, touch or rm files
%.out: %.tla %.cfg Channels.tla  # Channels: not always, but most of the time
	tlc -workers 4 $< | tee $@

%.svg: %.out
	$(VENV)/python ./render_timeline.py $< > $@

# Can't have implicit rules for phony targets, I guess
#%.model: %.tla
#	tlc $<

#tlc -difftrace counter.tla
inc_counter.model: inc_counter.tla inc_counter.cfg
	tlc -workers 4 $<

inc_dec_counter.model: inc_dec_counter.tla inc_dec_counter.cfg
	tlc -workers 4 $<

two_client_perfect_channel.model: two_client_perfect_channel.tla two_client_perfect_channel.cfg
	tlc -workers 4 $<

two_client_macros.model: two_client_macros.tla two_client_macros.cfg
	tlc -workers 4 $<

two_client_abstract_channel.out: two_client_abstract_channel.tla two_client_abstract_channel.cfg Messages.tla
	tlc -workers 4 $< | tee $@

two_client_abstract_channel_2.out: two_client_abstract_channel_2.tla two_client_abstract_channel_2.cfg Channels.tla
	tlc -workers 4 $< | tee $@
