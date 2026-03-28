import keccak_verification.spec.hacspec_sha3
open Std.Do

/-- If each iteration `f i` succeeds with value `g i` (proved pointwise), then
    `createi f` succeeds and equals `RustArray.ofVec (Vector.ofFn g)`.
    The caller provides `g` explicitly — no metavariables, clean for nested createi. -/
theorem hacspec_sha3.createi_ofFn {α : Type} {n : usize}
    (f : usize → RustM α)
    (g : Fin n.toNat → α)
    (hfg : ∀ i : Fin n.toNat, f (USize64.ofNat i.val) = .ok (g i)) :
    hacspec_sha3.createi α n (usize → RustM α) f = .ok (RustArray.ofVec (Vector.ofFn g)) := by
  unfold hacspec_sha3.createi core_models.array.from_fn rust_primitives.slice.array_from_fn
  simp only [bind, pure, RustM.bind]
  suffices h : Vector.mapM (fun i => f (USize64.ofNat i)) (Vector.range n.toNat) = .ok (Vector.ofFn g) by
    rw [h]
  have hrange : Vector.range n.toNat = Vector.map Fin.val (Vector.ofFn id) := by
    ext i hi; simp [Vector.getElem_range, Vector.getElem_ofFn]
  rw [hrange, Vector.mapM_map]
  have hfg' : (fun i => f (USize64.ofNat i)) ∘ Fin.val = fun i => pure (g i) := by
    funext i; exact hfg i
  rw [hfg', Vector.mapM_pure, Vector.map_ofFn]
  rfl

-- The following (ofTotal, ofTotal_spec, createi_ofFn') are unused but kept as documentation.
-- They show an alternative approach where g is constructed internally via ofTotal,
-- but this causes metavariable issues in nested createi usage.

/-- Constructively extract the value from a `RustM` computation that is
proven total via a Hoare triple. Uses only `propext` and `Quot.sound`. -/
def RustM.ofTotal (x : RustM α) {P : Prop} (hP : P)
    (h : ⦃⌜P⌝⦄ x ⦃⇓ _ => ⌜True⌝⦄) : α :=
  match x, h with
  | .ok v, _ => v
  | .fail _, h => False.elim (h hP)
  | .div, h => False.elim (h hP)

theorem RustM.ofTotal_spec (x : RustM α) {P : Prop} (hP : P)
    (h : ⦃⌜P⌝⦄ x ⦃⇓ _ => ⌜True⌝⦄) :
    x = .ok (RustM.ofTotal x hP h) := by
  cases x with
  | ok v => rfl
  | fail e => exact absurd (h hP) id
  | div => exact absurd (h hP) id

/-- Original createi_ofFn with internally constructed g via ofTotal.
    Unused: causes metavariable issues in nested createi proofs. -/
theorem hacspec_sha3.createi_ofFn' {α : Type} {n : usize}
    (P : Prop) (f : usize → RustM α)
    (hf : ∀ i : Fin n.toNat, ⦃⌜P⌝⦄ f (USize64.ofNat i.val) ⦃⇓ _ => ⌜True⌝⦄)
    (hP : P) :
    let g : Fin n.toNat → α := fun i => RustM.ofTotal (f (USize64.ofNat i.val)) hP (hf i)
    (∀ i, f (USize64.ofNat i.val) = .ok (g i)) ∧
    hacspec_sha3.createi α n (usize → RustM α) f = .ok (RustArray.ofVec (Vector.ofFn g)) := by
  intro g
  have hg : ∀ i, f (USize64.ofNat i.val) = .ok (g i) :=
    fun i => RustM.ofTotal_spec _ hP (hf i)
  refine ⟨hg, ?_⟩
  exact hacspec_sha3.createi_ofFn f g hg
