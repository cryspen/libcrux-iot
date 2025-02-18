# Debugging with OpenOCD

To start the debug server on the device run

```
openocd -f <INTERFACE> -f <TARGET> -l /tmp/openocd.log
```

For me `<INTERFACE>` is
`/usr/share/openocd/scripts/interface/stlink-v2-1.cfg` and `<TARGET>`
is `/usr/share/openocd/scripts/target/stm32l4x.cfg`, the exact
location of these scripts depends on your openocd installation.

The above will log to `/tmp/openocd.log`, so to view the logs while
the debug server is running, use e.g. `tail -f /tmp/openocd.log`.

## Starting gdb manually
To start gdb:
```
arm-none-eabi-gdb <path-to-binary>
```

## Using a cargo runner

If you have the `gdbgui` program set up you can use `cargo rb <bin>`
to start a debugging session using `gdbgui`.

## Connecting to target
Now you can connect to the gdb server using on some port (`3333` by
default) from whichever `gdb` console you are using.
```
target extended-remote :3333
```

Then load the binary onto the device.
```
load
```


## Stepping into Rust sources
To avoid `Missing source file` errors, we have to tell gdb where to
find the Rust sources.

Run `rustc --print=sysroot` to obtain your `RUST_SRC_PATH` and then
`rustc -Vv` to get the commit hash of your rust compiler. E.g. for me
`RUST_SRC_PATH=/home/jonas/.rustup/toolchains/stable-x86_64-unknown-linux-gnu`
and the commit hash is `e71f9a9a98b0faf423844bf0ba7438f29dc27d58`.

Then in `gdb` execute command `set-substitute-path
/rustc/e71f9a9a98b0faf423844bf0ba7438f29dc27d58
/home/jonas/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust`,
substituting your own commit hash and `RUST_SRC_PATH`.

It should be possible to put that into a `.gdbinit` file to avoid
having to run it manually every time.
