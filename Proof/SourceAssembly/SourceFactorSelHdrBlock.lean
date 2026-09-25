import Proof.SourceAssembly.SourceFactorSelNat

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceFactorSel.HdrBlock
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation
noncomputable section

/-- The printer's dock: its scratch `0..21` on `8..29`, its resident `22 ↦ 0` (`1^k`), driver `23 ↦ 5`, log `24 ↦ 6`. -/
def natSl (j : Fin 25) : Fin 35 :=
  if j.val = 22 then 0 else if j.val = 23 then 5 else if j.val = 24 then 6 else ⟨8 + j.val, by omega⟩

theorem natSl_val (j : Fin 25) : (natSl j).val =
    if j.val = 22 then 0 else if j.val = 23 then 5 else if j.val = 24 then 6 else 8 + j.val := by
  unfold natSl
  split_ifs <;> rfl

theorem natSl_inj : Function.Injective natSl := by
  intro a b h
  have e := congrArg Fin.val h
  rw [natSl_val, natSl_val] at e
  have := a.isLt
  have := b.isLt
  apply Fin.ext
  split_ifs at e <;> omega

/-- The header stage's dock: the five fields `1..4, 28`, scratch `30..33, 34`, output `7`. -/
def hdSl : Fin 11 → Fin 35 := ![1, 2, 3, 4, 28, 30, 31, 32, 33, 7, 34]

theorem hdSl_inj : Function.Injective hdSl := by decide

theorem hdSl_val : ∀ i : Fin 4, (hdSl ⟨i.val, by omega⟩).val = i.val + 1 := by decide

/-- **The header block** (ONE fixed machine). -/
def hdrM := Composition.machine (RecoveryFocus.machine natSl Nat.natM) (Header.stage hdSl)

def hdrCost (mode : Bool) (q L target k D : Nat) : Nat :=
  Nat.natCost k D + 1 + SourceRequest.FieldPass.cost 5 (Header.fields mode q L target k)

/-- The width facts. -/
structure Fits (mode : Bool) (q L target k c D Qr S R C : Nat) : Prop where
  cap : CloseoutRowsEstimatorParity.Capacity.value k ≤ S
  kD : k ≤ D
  dS : D ≤ S
  dC : D + 1 ≤ C
  fc : ∀ i, 2 * (Header.fields mode q L target k i).length + 1 ≤ c
  cQ : c ≤ Qr
  cS : c ≤ S
  hS : 2 * (SourceRequest.header mode q L target k).length + 1 ≤ S

theorem hdr_run (mode : Bool) (q L target k c D Qk Qr Qd S R C : Nat) (E : Fin 35 → List Bool)
    (h0 : E 0 = ZeroPadding.pad Qk (List.replicate k true))
    (hf : ∀ i : Fin 4, E ⟨i.val + 1, by omega⟩ =
      ZeroPadding.pad Qr (frame (Header.fields mode q L target k ⟨i.val, by omega⟩)))
    (h5 : E 5 = ZeroPadding.pad Qd (List.replicate D true)) (h6 : E 6 = List.replicate C false)
    (h7 : E 7 = List.replicate R false) (hscr : ∀ j : Fin 35, 8 ≤ j.val → E j = List.replicate S false)
    (fit : Fits mode q L target k c D Qr S R C) :
    ∃ E' : Fin 35 → List Bool, Step hdrM (hdrCost mode q L target k D) (fun _ => 0) E (fun _ => 0) E' ∧
      E' 7 = ZeroPadding.pad R (frame (SourceRequest.header mode q L target k)) ∧
      (∀ j : Fin 35, j.val < 7 → E' j = E j) := by
  -- 1. `1^k ↦ frame (natWord k)` on 28
  obtain ⟨E1, s1, o1, k1, _, f1⟩ := Nat.nat_step natSl natSl_inj k k Qk Qd D C S (le_refl k) fit.cap fit.kD fit.dS
    fit.dC (fun _ => 0) E (fun _ => rfl)
    (by rw [show natSl 22 = 0 by decide]; exact h0) (by rw [show natSl 23 = 5 by decide]; exact h5)
    (by rw [show natSl 24 = 6 by decide]; exact h6)
    (by
      intro j hj
      apply hscr
      rw [natSl_val]
      split_ifs <;> omega)
  rw [show natSl 20 = 28 by decide] at o1
  have k1' : ∀ x : Fin 35, (x.val < 8 ∨ 30 ≤ x.val) → x.val ≠ 0 → x.val ≠ 5 → x.val ≠ 6 → E1 x = E x := by
    intro x hx h0' h5' h6'
    apply f1
    intro j e
    subst e
    rw [natSl_val] at hx h0' h5' h6'
    split_ifs at hx h0' h5' h6' <;> omega
  have k1k : ∀ x : Fin 35, x.val = 0 ∨ x.val = 5 ∨ x.val = 6 → E1 x = E x := by
    intro x hx
    rcases hx with h | h | h
    · have e : x = natSl 22 := Fin.ext (by rw [natSl_val]; simp [h])
      rw [e]; exact k1 22 (by decide)
    · have e : x = natSl 23 := Fin.ext (by rw [natSl_val]; simp [h])
      rw [e]; exact k1 23 (by decide)
    · have e : x = natSl 24 := Fin.ext (by rw [natSl_val]; simp [h])
      rw [e]; exact k1 24 (by decide)
  have keep1 : ∀ x : Fin 35, (x.val < 8 ∨ 30 ≤ x.val) → E1 x = E x := by
    intro x hx
    by_cases h : x.val = 0 ∨ x.val = 5 ∨ x.val = 6
    · exact k1k x h
    · exact k1' x hx (by omega) (by omega) (by omega)
  -- 2. the header stage onto 7
  obtain ⟨E2, s2, o2, k2, f2⟩ := Header.stage_step hdSl hdSl_inj mode q L target k c S R ![Qr, Qr, Qr, Qr, S]
    (fun _ => 0) E1 (fun _ => rfl)
    (by
      intro i
      fin_cases i
      · exact (keep1 1 (by decide)).trans (hf 0)
      · exact (keep1 2 (by decide)).trans (hf 1)
      · exact (keep1 3 (by decide)).trans (hf 2)
      · exact (keep1 4 (by decide)).trans (hf 3)
      · exact o1)
    ((keep1 30 (by decide)).trans (hscr 30 (by decide))) ((keep1 31 (by decide)).trans (hscr 31 (by decide)))
    ((keep1 32 (by decide)).trans (hscr 32 (by decide))) ((keep1 33 (by decide)).trans (hscr 33 (by decide)))
    ((keep1 7 (by decide)).trans h7) ((keep1 34 (by decide)).trans (hscr 34 (by decide)))
    fit.fc (by intro i; fin_cases i <;> simp [fit.cQ, fit.cS]) fit.cS fit.hS
  refine ⟨E2, s1.seq s2, o2, ?_⟩
  intro j hj
  by_cases hmid : 1 ≤ j.val ∧ j.val ≤ 4
  · have e : j = hdSl ⟨j.val - 1, by omega⟩ := by
      apply Fin.ext
      have := hdSl_val ⟨j.val - 1, by omega⟩
      simp only at this
      omega
    have := k2 ⟨j.val - 1, by omega⟩
    rw [← e] at this
    rw [this]
    exact keep1 j (Or.inl (by omega))
  · rw [f2 j (by intro i e; subst e; revert hj hmid; fin_cases i <;> decide)]
    exact keep1 j (Or.inl (by omega))

/-- **The header block, docked** by any injective `sl : Fin 35 → Fin U` (entry heads `0` on the dock; heads kept). -/
theorem hdr_step {U : Nat} (sl : Fin 35 → Fin U) (hsl : Function.Injective sl)
    (mode : Bool) (q L target k c D Qk Qr Qd S R C : Nat) (H : Fin U → Nat) (A : Fin U → List Bool)
    (hH : ∀ j, H (sl j) = 0)
    (h0 : A (sl 0) = ZeroPadding.pad Qk (List.replicate k true))
    (hf : ∀ i : Fin 4, A (sl ⟨i.val + 1, by omega⟩) =
      ZeroPadding.pad Qr (frame (Header.fields mode q L target k ⟨i.val, by omega⟩)))
    (h5 : A (sl 5) = ZeroPadding.pad Qd (List.replicate D true)) (h6 : A (sl 6) = List.replicate C false)
    (h7 : A (sl 7) = List.replicate R false) (hscr : ∀ j : Fin 35, 8 ≤ j.val → A (sl j) = List.replicate S false)
    (fit : Fits mode q L target k c D Qr S R C) :
    ∃ A' : Fin U → List Bool, Step (RecoveryFocus.machine sl hdrM) (hdrCost mode q L target k D) H A H A' ∧
      A' (sl 7) = ZeroPadding.pad R (frame (SourceRequest.header mode q L target k)) ∧
      (∀ x, (∀ j : Fin 35, sl j = x → j.val < 7) → A' x = A x) := by
  obtain ⟨E', st, o7, kp⟩ := hdr_run mode q L target k c D Qk Qr Qd S R C (fun j => A (sl j)) h0 hf h5 h6 h7 hscr fit
  have d := st.dock sl hsl H A (fun j => hH j) (fun j => rfl)
  rw [dockH_existing sl H (fun _ => 0) hH] at d
  refine ⟨_, d, by rw [install_slot sl hsl]; exact o7, ?_⟩
  intro x hx
  by_cases hp : ∃ j, sl j = x
  · obtain ⟨j, rfl⟩ := hp
    rw [install_slot sl hsl]
    exact kp j (hx j rfl)
  · exact install_other sl A E' x (fun j e => hp ⟨j, e⟩)

end
end NearCubicWires.SourceFactorSel.HdrBlock

