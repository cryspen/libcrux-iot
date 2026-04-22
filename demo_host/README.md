# `libcrux-iot` IoT Demo -- Host

This crate contains the host application for the `libcrux-iot` demo application.

The host device is a Linux machine with the client device attached via a USB serial port.

The host program repeatedly runs a simple ad hoc protocol with the
client device, and opens a browser-based dashboard that allows
inspection of the protocol characterstics and interactive choice of
certain protocol parameters.

## How to run

After attaching the demo device run
```
cargo run -- --device $SERIAL
```
where `$SERIAL` is the serial device that the demo client is attached to.

On success, the host application should print the `localhost` address
of the interactive dashboard and start outputting protocol outcomes in
the console.

## Interactive Dashboard

The host application will start a local web server that allows for an
interactive choice of message payload to be sent to the client device
via a browser-based dashboard.

The dashboard also displays information on transmitted message sizes
as well as client-measured execution times for different operation
that are part of the protocol.

The dashboard also allows intentional insertion of faults in the data
transmitted by the host program, so the client can demonstrate
rejection of an ML-DSA signature.

## Ad Hoc Protocol Between Host and Client

⚠️ **This is not a secure protocol for any use-case.** It serves as a
proof of concept to exercise ML-KEM and ML-DSA operations on embedded
hardware.

The simple two-message flow between host and client is as follows:

```
Inputs:
-------
    - Host: Long-term ML-DSA 65 signing key sk, message payload msg
    - Client: Long-term ML-DSA 65 verification key vk
    
Outputs:
--------
    - Both: fresh ML-KEM 768 shared secret ss
    
Protocol:
---------

Host:
    (ek, dk) <- MLKEM-768.KeyGen()
    sig <- MLDSA-65.Sign(sk, ek || msg)
    
Host -> Client: ek || msg, sig

Client:
    if MLDSA-65.Verify(vk, ek || msg) != true {
        enc <- Error
    }
    (enc, ss) <- MLKEM-768.Encapsulate(ek)

Client -> Host: enc

Host:
    if enc != Error {
        ss <- MLKEM-768.Decapsulate(dk, enc)
    }
```

where inputs of random bytes are omitted for conciseness.

