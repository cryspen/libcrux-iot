/-
  Pure-Lean intermediate spec for the Keccak `keccakf1600` impl.

  Mirrors the Aeneas-extracted `keccak.keccakf1600_*` sub-functions
  line-by-line, but as plain `BitVec 32` arithmetic on the pure-Lean
  `KState` record (no `Result` monad, no `Aeneas.Std.UScalar`, no
  `Lane2U32` wrappers).

  This is the *impl side* of Campaign 2's domain — the Campaign-1
  equivalence (`StructEquiv.lean`) proves `keccakf1600_round*_*` ≡
  the corresponding `bit_*` definition here via `hax_mvcgen`.

  Phase 1 Step A (rosetta stone): only `bit_pi_rho_chi_y0_zeta0` is
  defined here. Scaling to the remaining ~29 sub-fns is mechanical
  and happens in subsequent sessions.

  Plan: `~/.claude/plans/fancy-gliding-swan.md`, Phase 1 Step 1.3.
-/
import LibcruxIotSha3.BitKeccak.State
import LibcruxIotSha3.Extraction.Funs

namespace libcrux_iot_sha3.BitKeccak

open Aeneas Aeneas.Std libcrux_iot_sha3

/-! ## Pure-Lean primitive helpers on `KState`

    Each mirrors an Aeneas method on `state.KeccakState`. -/

/-- Read lane at index `(5*j + i)`, half `zeta`. Mirrors
    `state.KeccakState.get_with_zeta`. Returns 0 on out-of-range. -/
@[inline] def KState.getWithZeta (s : KState) (i j zeta : Nat) : BitVec 32 :=
  let idx := 5 * j + i
  let lane := s.st.toList[idx]?.getD Lane.zero
  if zeta = 0 then lane.z0 else lane.z1

/-- Read `s.d[col]!.val[zeta]!`. Mirrors the impl's d-cell read pattern. -/
@[inline] def KState.getDCell (s : KState) (col zeta : Nat) : BitVec 32 :=
  let lane := s.d.toList[col]?.getD Lane.zero
  if zeta = 0 then lane.z0 else lane.z1

/-- Write `v` into lane at index `(5*j + i)`, half `zeta`. Mirrors
    `state.KeccakState.set_with_zeta`. No-op if `(5*j + i) ≥ 25`. -/
@[inline] def KState.setWithZeta (s : KState) (i j zeta : Nat) (v : BitVec 32) : KState :=
  let idx := 5 * j + i
  if h : idx < 25 then
    let old := s.st[idx]
    let newLane : Lane := if zeta = 0 then { old with z0 := v } else { old with z1 := v }
    { s with st := s.st.set idx newLane h }
  else s

/-! ## `bit_pi_rho_chi_y0_zeta0` — rosetta-stone sub-fn

    Pure-Lean mirror of
    `keccak.keccakf1600_round0_pi_rho_chi_y0_zeta0` (Funs.lean:3417).

    Lane reads: (i=0,j=0,ζ=0)→idx0/h0, (1,1,0)→idx6/h0, (2,2,1)→idx12/h1,
                (3,3,1)→idx18/h1, (4,4,0)→idx24/h0.
    D-cell reads: d[0][0], d[1][0], d[2][1], d[3][1], d[4][0].
    Rotation amounts: 0, 22, 22, 11, 7.
    Iota: RC_INTERLEAVED_0[s.i] XORed into ax0 only.
    Writes (same lanes/halves as reads):
      lane 0/h0 := bx0 ⊕ (¬bx1 ∧ bx2) ⊕ RC_INTERLEAVED_0[s.i]
      lane 6/h0 := bx1 ⊕ (¬bx2 ∧ bx3)
      lane 12/h1 := bx2 ⊕ (¬bx3 ∧ bx4)
      lane 18/h1 := bx3 ⊕ (¬bx4 ∧ bx0)
      lane 24/h0 := bx4 ⊕ (¬bx0 ∧ bx1)
    No `s.i` increment (only `_y0_zeta1` increments `s.i`). -/
def bit_pi_rho_chi_y0_zeta0 (_BR : Std.Usize) (s : KState) : KState :=
  let a0 := s.st[0].z0
  let d0 := s.d[0].z0
  let a1 := s.st[6].z0
  let d1 := s.d[1].z0
  let a2 := s.st[12].z1
  let d2 := s.d[2].z1
  let a3 := s.st[18].z1
  let d3 := s.d[3].z1
  let a4 := s.st[24].z0
  let d4 := s.d[4].z0
  let bx0 := (a0 ^^^ d0).rotateLeft 0
  let bx1 := (a1 ^^^ d1).rotateLeft 22
  let bx2 := (a2 ^^^ d2).rotateLeft 22
  let bx3 := (a3 ^^^ d3).rotateLeft 11
  let bx4 := (a4 ^^^ d4).rotateLeft 7
  let rc  := (keccak.RC_INTERLEAVED_0.val[s.i.val]!).bv
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2) ^^^ rc
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new0  : Lane := ⟨ax0, s.st[0].z1⟩
  let new6  : Lane := ⟨ax1, s.st[6].z1⟩
  let new12 : Lane := ⟨s.st[12].z0, ax2⟩
  let new18 : Lane := ⟨s.st[18].z0, ax3⟩
  let new24 : Lane := ⟨ax4, s.st[24].z1⟩
  let st' := s.st.set 0 new0 |>.set 6 new6 |>.set 12 new12 |>.set 18 new18 |>.set 24 new24
  { s with st := st' }

end libcrux_iot_sha3.BitKeccak
