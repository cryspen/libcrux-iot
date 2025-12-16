# `libcrux-iot` Demo -- Client for STM32L4R5ZI

This crate contains the client application for the `libcrux-iot` demo application. The demo client is based on the `usb_serial` example from the `embassy` repository. 

The client device is an [STM32 Nucleo 144 dev board](https://www.st.com/en/evaluation-tools/nucleo-l4r5zi.html) with an STM32L4R5ZI MCU, attached via a USB serial port.

The simple two-message flow between host and client is as follows:

```
Inputs:
-------
    - Host: Long-term ML-DSA 65 signing key sk
    - Client: Long-term ML-DSA 65 verification key vk
    
Outputs:
--------
    - Both: fresh ML-KEM 768 shared secret ss
    
Protocol:
---------

Host:
    (ek, dk) <- MLKEM-768.KeyGen()
    sig <- MLDSA-65.Sign(sk, ek)
    
Host -> Client: ek, sig

Client:
    if MLDSA-65.Verify(vk, ek) != true {
        abort
    }
    (enc, ss) <- MLKEM-768.Encapsulate(ek)

Client -> Host: enc

Host:
    ss <- MLKEM-768.Decapsulate(dk, enc)
```

where inputs of random bytes are omitted for conciseness.

## How to run

This requires an installation of [`probe-rs`](https://probe.rs/).

After attaching the demo device's debug probe and User USB, run

```
cargo run --release --bin demo_client
```

to flash and run the demo application, printing a debug trace via the debug probe.

On success, the client application should print the derived shared secret.

On success
