
%.lean:
	rm -f .lake/build/lib/extraction/$*.{olean,ilean,olean.trace}
	lake lean extraction/$*.lean -- --time 2>&1 | tee results.log
	grep '\[profiler\]' results.log | sort -t' ' -k2 -rn | head -30
