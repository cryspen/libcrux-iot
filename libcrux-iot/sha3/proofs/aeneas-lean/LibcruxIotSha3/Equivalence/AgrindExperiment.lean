-- Experiment: compare agrind / libcruxgrind / grind on the L6 algebraic-fold goal.
import LibcruxIotSha3.Equivalence.Lift
import LibcruxIotSha3.Equivalence.LiftLemmas
import LibcruxIotSha3.Equivalence.LibcruxGrindSetup

open Aeneas Aeneas.Std libcrux_iot_sha3 libcrux_iot_sha3.Equivalence Aeneas.Grind

attribute [local irreducible] spread_to_even lift_lane_bv

attribute [agrind =, libcruxgrind =, grind =] lift_xor lift_xor5 lift_td lift_rot1 lift_and lift_not lift_chi lift_theta_apply

-- The L6-shaped goal (one lane of theta_lift_spec, after step (a) collapses the chain).
-- Both sides are LL towers + a rotateLeft; LHS is the expanded form, RHS is the folded.

-- Test 1: agrind
example (a b c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 e0 e1 e2 e3 e4 f0 f1 f2 f3 f4 : BitVec 32) :
    lift_lane_bv a b ^^^
      (lift_lane_bv c0 d0 ^^^ lift_lane_bv c1 d1 ^^^ lift_lane_bv c2 d2 ^^^
       lift_lane_bv c3 d3 ^^^ lift_lane_bv c4 d4 ^^^
       (lift_lane_bv e0 f0 ^^^ lift_lane_bv e1 f1 ^^^ lift_lane_bv e2 f2 ^^^
        lift_lane_bv e3 f3 ^^^ lift_lane_bv e4 f4).rotateLeft 1) =
    lift_lane_bv (a ^^^ (c0 ^^^ c1 ^^^ c2 ^^^ c3 ^^^ c4 ^^^ (f0 ^^^ f1 ^^^ f2 ^^^ f3 ^^^ f4).rotateLeft 1))
                 (b ^^^ (d0 ^^^ d1 ^^^ d2 ^^^ d3 ^^^ d4 ^^^ (e0 ^^^ e1 ^^^ e2 ^^^ e3 ^^^ e4))) := by
  agrind

-- Test 2: libcruxgrind
example (a b c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 e0 e1 e2 e3 e4 f0 f1 f2 f3 f4 : BitVec 32) :
    lift_lane_bv a b ^^^
      (lift_lane_bv c0 d0 ^^^ lift_lane_bv c1 d1 ^^^ lift_lane_bv c2 d2 ^^^
       lift_lane_bv c3 d3 ^^^ lift_lane_bv c4 d4 ^^^
       (lift_lane_bv e0 f0 ^^^ lift_lane_bv e1 f1 ^^^ lift_lane_bv e2 f2 ^^^
        lift_lane_bv e3 f3 ^^^ lift_lane_bv e4 f4).rotateLeft 1) =
    lift_lane_bv (a ^^^ (c0 ^^^ c1 ^^^ c2 ^^^ c3 ^^^ c4 ^^^ (f0 ^^^ f1 ^^^ f2 ^^^ f3 ^^^ f4).rotateLeft 1))
                 (b ^^^ (d0 ^^^ d1 ^^^ d2 ^^^ d3 ^^^ d4 ^^^ (e0 ^^^ e1 ^^^ e2 ^^^ e3 ^^^ e4))) := by
  libcruxgrind

-- Test 3: global grind
example (a b c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 e0 e1 e2 e3 e4 f0 f1 f2 f3 f4 : BitVec 32) :
    lift_lane_bv a b ^^^
      (lift_lane_bv c0 d0 ^^^ lift_lane_bv c1 d1 ^^^ lift_lane_bv c2 d2 ^^^
       lift_lane_bv c3 d3 ^^^ lift_lane_bv c4 d4 ^^^
       (lift_lane_bv e0 f0 ^^^ lift_lane_bv e1 f1 ^^^ lift_lane_bv e2 f2 ^^^
        lift_lane_bv e3 f3 ^^^ lift_lane_bv e4 f4).rotateLeft 1) =
    lift_lane_bv (a ^^^ (c0 ^^^ c1 ^^^ c2 ^^^ c3 ^^^ c4 ^^^ (f0 ^^^ f1 ^^^ f2 ^^^ f3 ^^^ f4).rotateLeft 1))
                 (b ^^^ (d0 ^^^ d1 ^^^ d2 ^^^ d3 ^^^ d4 ^^^ (e0 ^^^ e1 ^^^ e2 ^^^ e3 ^^^ e4))) := by
  grind

-- Test 4: baseline simp_only [← lift_xor, ← lift_td] (the standalone reproducer)
example (a b c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 e0 e1 e2 e3 e4 f0 f1 f2 f3 f4 : BitVec 32) :
    lift_lane_bv a b ^^^
      (lift_lane_bv c0 d0 ^^^ lift_lane_bv c1 d1 ^^^ lift_lane_bv c2 d2 ^^^
       lift_lane_bv c3 d3 ^^^ lift_lane_bv c4 d4 ^^^
       (lift_lane_bv e0 f0 ^^^ lift_lane_bv e1 f1 ^^^ lift_lane_bv e2 f2 ^^^
        lift_lane_bv e3 f3 ^^^ lift_lane_bv e4 f4).rotateLeft 1) =
    lift_lane_bv (a ^^^ (c0 ^^^ c1 ^^^ c2 ^^^ c3 ^^^ c4 ^^^ (f0 ^^^ f1 ^^^ f2 ^^^ f3 ^^^ f4).rotateLeft 1))
                 (b ^^^ (d0 ^^^ d1 ^^^ d2 ^^^ d3 ^^^ d4 ^^^ (e0 ^^^ e1 ^^^ e2 ^^^ e3 ^^^ e4))) := by
  simp only [← lift_xor, ← lift_td]
