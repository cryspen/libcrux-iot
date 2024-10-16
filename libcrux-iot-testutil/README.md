# libcrux-iot-testutil

This crate provides utils for testing and benchmarking on embedded hardware.

Utilities that are implemented right now:

- Test and Benchmark Runner

To receive output from test/benchmark binary `$bin` be sure to set `DEFMT_LOG=info`,
e.g. by running the test/benchmark as `DEFMT_LOG=info cargo rb $bin`.
