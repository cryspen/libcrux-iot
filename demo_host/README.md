# `libcrux-iot` IoT Demo -- Host

This crate contains the host application for the `libcrux-iot` demo application.

The host device is a Linux machine with the client device attached via a USB serial port.

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

After attaching the demo device run
```
cargo run -- --device $SERIAL
```
where `$SERIAL` is the serial device that the demo client is attached to.

On success, the host application should print the derived shared secret.
