-- Orientation/AC experiments for the L6 algebraic-close blocker.
-- Tests whether grind/agrind/libcruxgrind/simp_only can close the L6 shape
-- under different lemma orientations and explicit AC hints.
import LibcruxIotSha3.Equivalence.Lift
import LibcruxIotSha3.Equivalence.LibcruxGrindSetup

open Aeneas Aeneas.Std libcrux_iot_sha3 libcrux_iot_sha3.Equivalence Aeneas.Grind

attribute [local irreducible] spread_to_even lift_lane_bv

-- Helper notation for compact goals
local notation "LL" => lift_lane_bv

-- ---------------------------------------------------------------------------
-- The L6-shaped goal under test (canonical form, matches theta_lift_spec step b)
-- ---------------------------------------------------------------------------
-- LHS: a folded `LL a b` XOR'd with a 5-fold LL tower whose last term is rotated.
-- RHS: the same algebraic identity, hoisted entirely inside one `LL`.

-- ---------------------------------------------------------------------------
-- Experiment 1: re-orient `lift_xor`/`lift_td`/`lift_rot1` to `@[grind =_]`
-- This makes the RHS (which matches the post-mvcgen tower) the pattern.
-- ---------------------------------------------------------------------------

attribute [agrind =_, libcruxgrind =_, grind =_] lift_xor lift_td lift_rot1
attribute [agrind =, libcruxgrind =, grind =] lift_xor5 lift_and lift_not lift_chi lift_theta_apply

set_option maxHeartbeats 4000000 in
example (a b c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 e0 e1 e2 e3 e4 f0 f1 f2 f3 f4 : BitVec 32) :
    LL a b ^^^
      (LL c0 d0 ^^^ LL c1 d1 ^^^ LL c2 d2 ^^^
       LL c3 d3 ^^^ LL c4 d4 ^^^
       (LL e0 f0 ^^^ LL e1 f1 ^^^ LL e2 f2 ^^^
        LL e3 f3 ^^^ LL e4 f4).rotateLeft 1) =
    LL (a ^^^ (c0 ^^^ c1 ^^^ c2 ^^^ c3 ^^^ c4 ^^^ (f0 ^^^ f1 ^^^ f2 ^^^ f3 ^^^ f4).rotateLeft 1))
       (b ^^^ (d0 ^^^ d1 ^^^ d2 ^^^ d3 ^^^ d4 ^^^ (e0 ^^^ e1 ^^^ e2 ^^^ e3 ^^^ e4))) := by
  agrind

set_option maxHeartbeats 4000000 in
example (a b c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 e0 e1 e2 e3 e4 f0 f1 f2 f3 f4 : BitVec 32) :
    LL a b ^^^
      (LL c0 d0 ^^^ LL c1 d1 ^^^ LL c2 d2 ^^^
       LL c3 d3 ^^^ LL c4 d4 ^^^
       (LL e0 f0 ^^^ LL e1 f1 ^^^ LL e2 f2 ^^^
        LL e3 f3 ^^^ LL e4 f4).rotateLeft 1) =
    LL (a ^^^ (c0 ^^^ c1 ^^^ c2 ^^^ c3 ^^^ c4 ^^^ (f0 ^^^ f1 ^^^ f2 ^^^ f3 ^^^ f4).rotateLeft 1))
       (b ^^^ (d0 ^^^ d1 ^^^ d2 ^^^ d3 ^^^ d4 ^^^ (e0 ^^^ e1 ^^^ e2 ^^^ e3 ^^^ e4))) := by
  libcruxgrind

set_option maxHeartbeats 4000000 in
example (a b c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 e0 e1 e2 e3 e4 f0 f1 f2 f3 f4 : BitVec 32) :
    LL a b ^^^
      (LL c0 d0 ^^^ LL c1 d1 ^^^ LL c2 d2 ^^^
       LL c3 d3 ^^^ LL c4 d4 ^^^
       (LL e0 f0 ^^^ LL e1 f1 ^^^ LL e2 f2 ^^^
        LL e3 f3 ^^^ LL e4 f4).rotateLeft 1) =
    LL (a ^^^ (c0 ^^^ c1 ^^^ c2 ^^^ c3 ^^^ c4 ^^^ (f0 ^^^ f1 ^^^ f2 ^^^ f3 ^^^ f4).rotateLeft 1))
       (b ^^^ (d0 ^^^ d1 ^^^ d2 ^^^ d3 ^^^ d4 ^^^ (e0 ^^^ e1 ^^^ e2 ^^^ e3 ^^^ e4))) := by
  grind

-- ---------------------------------------------------------------------------
-- Experiment 2: bidirectional `@[grind _=_]` (loop risk, capped at 4M)
-- ---------------------------------------------------------------------------

namespace Bidi
attribute [grind _=_] lift_xor lift_td lift_rot1

set_option maxHeartbeats 4000000 in
example (a b c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 e0 e1 e2 e3 e4 f0 f1 f2 f3 f4 : BitVec 32) :
    LL a b ^^^
      (LL c0 d0 ^^^ LL c1 d1 ^^^ LL c2 d2 ^^^
       LL c3 d3 ^^^ LL c4 d4 ^^^
       (LL e0 f0 ^^^ LL e1 f1 ^^^ LL e2 f2 ^^^
        LL e3 f3 ^^^ LL e4 f4).rotateLeft 1) =
    LL (a ^^^ (c0 ^^^ c1 ^^^ c2 ^^^ c3 ^^^ c4 ^^^ (f0 ^^^ f1 ^^^ f2 ^^^ f3 ^^^ f4).rotateLeft 1))
       (b ^^^ (d0 ^^^ d1 ^^^ d2 ^^^ d3 ^^^ d4 ^^^ (e0 ^^^ e1 ^^^ e2 ^^^ e3 ^^^ e4))) := by
  grind
end Bidi

-- ---------------------------------------------------------------------------
-- Experiment 3: explicit AC hints — give grind BitVec.xor_comm/assoc directly
-- ---------------------------------------------------------------------------

set_option maxHeartbeats 4000000 in
example (a b c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 e0 e1 e2 e3 e4 f0 f1 f2 f3 f4 : BitVec 32) :
    LL a b ^^^
      (LL c0 d0 ^^^ LL c1 d1 ^^^ LL c2 d2 ^^^
       LL c3 d3 ^^^ LL c4 d4 ^^^
       (LL e0 f0 ^^^ LL e1 f1 ^^^ LL e2 f2 ^^^
        LL e3 f3 ^^^ LL e4 f4).rotateLeft 1) =
    LL (a ^^^ (c0 ^^^ c1 ^^^ c2 ^^^ c3 ^^^ c4 ^^^ (f0 ^^^ f1 ^^^ f2 ^^^ f3 ^^^ f4).rotateLeft 1))
       (b ^^^ (d0 ^^^ d1 ^^^ d2 ^^^ d3 ^^^ d4 ^^^ (e0 ^^^ e1 ^^^ e2 ^^^ e3 ^^^ e4))) := by
  grind [BitVec.xor_comm, BitVec.xor_assoc]

-- ---------------------------------------------------------------------------
-- Experiment 4: simp_only ← direction (the baseline)
-- ---------------------------------------------------------------------------

set_option maxHeartbeats 4000000 in
example (a b c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 e0 e1 e2 e3 e4 f0 f1 f2 f3 f4 : BitVec 32) :
    LL a b ^^^
      (LL c0 d0 ^^^ LL c1 d1 ^^^ LL c2 d2 ^^^
       LL c3 d3 ^^^ LL c4 d4 ^^^
       (LL e0 f0 ^^^ LL e1 f1 ^^^ LL e2 f2 ^^^
        LL e3 f3 ^^^ LL e4 f4).rotateLeft 1) =
    LL (a ^^^ (c0 ^^^ c1 ^^^ c2 ^^^ c3 ^^^ c4 ^^^ (f0 ^^^ f1 ^^^ f2 ^^^ f3 ^^^ f4).rotateLeft 1))
       (b ^^^ (d0 ^^^ d1 ^^^ d2 ^^^ d3 ^^^ d4 ^^^ (e0 ^^^ e1 ^^^ e2 ^^^ e3 ^^^ e4))) := by
  simp only [← lift_xor, ← lift_td]
