# Runtime Safety Annotation Examples

## Mutable slice arguments need `ensures` clauses stating the length does not change
```rust
#[hax_lib::ensures(|_| input.len() == future(input).len())]
fn mutable_slice_fn(input: &mut [u8]) {
// ...
}
```

## Mutable slices need loop invariants stating their length does not change
```rust
#[hax_lib::ensures(|_| input.len() == future(input).len())]
fn mutable_slice_loop(input: &mut [u8]) {
    #[cfg(hax)]
    let _input_len = input.len();
    
    for i in 0..input.len() {
        hax_lib::loop_invariant!(|_i:usize| input.len() == _input_len);
        input[i] ^= 1;
    }
}
```

## Trait and impl blocks need `hax_lib::attributes` annotations
```rust
struct A {}

#[hax_lib::attributes]
impl A {
    // ...
}

#[hax_lib::attributes]
trait B {
    // ...
}
```

## Functions in trait blocks need at least `requires(true)` preconditions
```rust
#[hax_lib::attributes]
trait B {
    
    #[hax_lib::requires(true)] // unless there are other pre-conditions
    fn some_function () {
    // ...
    }
}
```

## Arithmetic in pre- and postconditions should be done using `.to_int()`
```rust
#[cfg(hax)]
use hax_lib::ToInt;

#[hax_lib::requires(a.to_int() + b.to_int() < 20)
fn some_function (a: u8, b: u8) {
    // ...
}
```
