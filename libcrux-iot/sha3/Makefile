CHARON_EXE = charon
AENEAS_EXE = aeneas

AENEAS_OPTIONS ?=

.PHONY: extract
extract: ../libcrux_iot_sha3.llbc
	$(AENEAS_EXE) -backend lean ../libcrux_iot_sha3.llbc -split-files -dest proofs/LibcruxIotSha3 $(AENEAS_OPTIONS)

../libcrux_iot_sha3.llbc: $(wildcard */*.rs)
	RUSTFLAGS="--cfg hax" $(CHARON_EXE) cargo --preset=aeneas