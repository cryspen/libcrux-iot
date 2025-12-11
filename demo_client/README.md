# `libcrux-iot` Demo Client for STM32L4R5ZI

This demo client accepts an ML-KEM encapsulation key, as well as an ML-DSA signature on the encapsulation key under a pinned verification key. If the signature verifies, the client encapsulates a message toward the received encapsulation key. 

The demo client is based on the `usb_serial` example from the `embassy` repository. 

Run with
```
cargo run --bin demo_client
```

