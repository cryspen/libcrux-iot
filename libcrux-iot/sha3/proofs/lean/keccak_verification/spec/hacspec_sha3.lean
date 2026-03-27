
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import keccak_verification.helpers
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace hacspec_sha3.keccak_f

--  Keccak-f[1600] state: 5×5 lanes of 64-bit words.
--  Keccak state type, exposed for cross-crate verification.
abbrev State : Type := (RustArray u64 25)

--  Read lane `A[x, y]`.
def get (state : (RustArray u64 25)) (x : usize) (y : usize) : RustM u64 := do
  state[(← ((← ((5 : usize) *? x)) +? y))]_?

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def get.spec (state : (RustArray u64 25)) (x : usize) (y : usize) :
    Spec
      (requires := do ((← (x <? (5 : usize))) &&? (← (y <? (5 : usize)))))
      (ensures := fun _ => pure True)
      (get (state : (RustArray u64 25)) (x : usize) (y : usize)) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [get] <;> sorry
}

--  Round constants `RC[ir]` for `ir = 0..23` — FIPS 202, Algorithm 5.
def ROUND_CONSTANTS : (RustArray u64 24) :=
  RustM.of_isOk
    (do
    (pure (RustArray.ofVec #v[(1 : u64),
                                (32898 : u64),
                                (9223372036854808714 : u64),
                                (9223372039002292224 : u64),
                                (32907 : u64),
                                (2147483649 : u64),
                                (9223372039002292353 : u64),
                                (9223372036854808585 : u64),
                                (138 : u64),
                                (136 : u64),
                                (2147516425 : u64),
                                (2147483658 : u64),
                                (2147516555 : u64),
                                (9223372036854775947 : u64),
                                (9223372036854808713 : u64),
                                (9223372036854808579 : u64),
                                (9223372036854808578 : u64),
                                (9223372036854775936 : u64),
                                (32778 : u64),
                                (9223372039002259466 : u64),
                                (9223372039002292353 : u64),
                                (9223372036854808704 : u64),
                                (2147483649 : u64),
                                (9223372039002292232 : u64)])))
    (by rfl)

--  Rotation offsets for ρ step — FIPS 202, Algorithm 2 / Table 2.
--
--  Indexed as `RHO_OFFSETS[5*x + y]`.
def RHO_OFFSETS : (RustArray u32 25) :=
  RustM.of_isOk
    (do
    (pure (RustArray.ofVec #v[(0 : u32),
                                (36 : u32),
                                (3 : u32),
                                (41 : u32),
                                (18 : u32),
                                (1 : u32),
                                (44 : u32),
                                (10 : u32),
                                (45 : u32),
                                (2 : u32),
                                (62 : u32),
                                (6 : u32),
                                (43 : u32),
                                (15 : u32),
                                (61 : u32),
                                (28 : u32),
                                (55 : u32),
                                (25 : u32),
                                (21 : u32),
                                (56 : u32),
                                (27 : u32),
                                (20 : u32),
                                (39 : u32),
                                (8 : u32),
                                (14 : u32)])))
    (by rfl)

--  ι step — FIPS 202, Algorithm 6.
--
--    A′[0,0] = A[0,0] ⊕ RC[ir]
def iota (state : (RustArray u64 25)) (round : usize) :
    RustM (RustArray u64 25) := do
  let state : (RustArray u64 25) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      state
      (0 : usize)
      (← ((← state[(0 : usize)]_?) ^^^? (← ROUND_CONSTANTS[round]_?))));
  (pure state)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def iota.spec (state : (RustArray u64 25)) (round : usize) :
    Spec
      (requires := do (round <? (24 : usize)))
      (ensures := fun _ => pure True)
      (iota (state : (RustArray u64 25)) (round : usize)) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [iota] <;> sorry
}

end hacspec_sha3.keccak_f

def hacspec_sha3.createi := core_models.array.from_fn

namespace hacspec_sha3.keccak_f

--  θ step — FIPS 202, Algorithm 1.
--
--    C[x]    = A[x,0] ⊕ A[x,1] ⊕ A[x,2] ⊕ A[x,3] ⊕ A[x,4]
--    D[x]    = C[x−1 mod 5] ⊕ rot(C[x+1 mod 5], 1)
--    A′[x,y] = A[x,y] ⊕ D[x]
@[spec]
def theta (state : (RustArray u64 25)) : RustM (RustArray u64 25) := do
  let c : (RustArray u64 5) ←
    (hacspec_sha3.createi u64 ((5 : usize)) (usize -> RustM u64)
      (fun x =>
        (do
        ((← ((← ((← ((← (get state x (0 : usize)))
                ^^^? (← (get state x (1 : usize)))))
              ^^^? (← (get state x (2 : usize)))))
            ^^^? (← (get state x (3 : usize)))))
          ^^^? (← (get state x (4 : usize)))) :
        RustM u64)));
  let d : (RustArray u64 5) ←
    (hacspec_sha3.createi u64 ((5 : usize)) (usize -> RustM u64)
      (fun x =>
        (do
        ((← c[(← ((← (x +? (4 : usize))) %? (5 : usize)))]_?)
          ^^^? (← (core_models.num.Impl_9.rotate_left
            (← c[(← ((← (x +? (1 : usize))) %? (5 : usize)))]_?)
            (1 : u32)))) :
        RustM u64)));
  (hacspec_sha3.createi u64 ((25 : usize)) (usize -> RustM u64)
    (fun idx =>
      (do
      ((← state[idx]_?) ^^^? (← d[(← (idx /? (5 : usize)))]_?)) : RustM u64)))

--  ρ step — FIPS 202, Algorithm 2.
--
--    A′[x,y] = rot(A[x,y], offset(x,y))
@[spec]
def rho (state : (RustArray u64 25)) : RustM (RustArray u64 25) := do
  (hacspec_sha3.createi u64 ((25 : usize)) (usize -> RustM u64)
    (fun idx =>
      (do
      (core_models.num.Impl_9.rotate_left
        (← state[idx]_?)
        (← RHO_OFFSETS[idx]_?)) :
      RustM u64)))

--  π step — FIPS 202, Algorithm 3.
--
--    A′[x,y] = A[(x + 3y) mod 5, x]
@[spec]
def pi (state : (RustArray u64 25)) : RustM (RustArray u64 25) := do
  (hacspec_sha3.createi u64 ((25 : usize)) (usize -> RustM u64)
    (fun idx =>
      (do
      let x : usize ← (idx /? (5 : usize));
      let y : usize ← (idx %? (5 : usize));
      (get state (← ((← (x +? (← ((3 : usize) *? y)))) %? (5 : usize))) x) :
      RustM u64)))

--  χ step — FIPS 202, Algorithm 4.
--
--    A′[x,y] = A[x,y] ⊕ (¬A[(x+1) mod 5, y] ∧ A[(x+2) mod 5, y])
@[spec]
def chi (state : (RustArray u64 25)) : RustM (RustArray u64 25) := do
  (hacspec_sha3.createi u64 ((25 : usize)) (usize -> RustM u64)
    (fun idx =>
      (do
      let x : usize ← (idx /? (5 : usize));
      let y : usize ← (idx %? (5 : usize));
      ((← (get state x y))
        ^^^? (← ((← (~? (← (get
            state
            (← ((← (x +? (1 : usize))) %? (5 : usize)))
            y))))
          &&&? (← (get state (← ((← (x +? (2 : usize))) %? (5 : usize))) y)))))
      :
      RustM u64)))

--  Keccak-f[1600] permutation — FIPS 202, Algorithm 7.
--
--    Rnd(A, ir) = ι(χ(π(ρ(θ(A)))), ir)
@[spec]
def keccak_f (state : (RustArray u64 25)) : RustM (RustArray u64 25) := do
  let state : (RustArray u64 25) ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      (24 : usize)
      (fun state _ => (do (pure true) : RustM Bool))
      state
      (fun state round =>
        (do
        (iota (← (chi (← (pi (← (rho (← (theta state)))))))) round) :
        RustM (RustArray u64 25))));
  (pure state)

end hacspec_sha3.keccak_f
