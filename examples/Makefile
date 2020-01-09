# Depends on building a virtualenv named 'env-ch'
VENV=../env-ch/bin

%.tla: %.pcal
	cp $< $@ && pcal -nocfg $@

# One problem with this rule is that is "successfully" builds the .out file on
# failures, and thus rebuilds the .svg file, so I don't get the right rebuild
# behavior, and have to like, touch or rm files.
#
# Also depend on Channels implementations, how to show?
#
# Also also: keep the intervening .out file around on success? Maybe in subdir?
#
# Also also: I patched tla-bin to take a library path
%.out: %.tla %.cfg
	TLA_LIBRARY_PATH="../" tlc -workers 4 $< | tee $@

images/%.svg: %.out
	$(VENV)/python ../render_timeline.py $< > $@
