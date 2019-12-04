.PHONY: test

Channels%Test: Channels%Test.tla ChannelsUtils.tla
	tlc $@

test: ChannelsReliableTest \
 ChannelsDuplicatesTest \
 ChannelsOutOfOrderTest \
 ChannelsAtLeastOnceTest
