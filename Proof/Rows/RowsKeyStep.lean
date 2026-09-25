import Proof.Rows.RowsBaseLayout

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.KeyStep
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open SignedSortKey
noncomputable section

/-- A framed binary word. -/
abbrev fb (w x : Nat) : List Bool := frame (binary w x)

/-! ## 1. The four local stages -/

theorem pair_eq (a b : List Bool) :
    (Fin.addCases (motive := fun _ : Fin (1+1) => List Bool) (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)) = ![a, b] := by
  funext i
  fin_cases i <;> rfl

theorem inc_local (w x cI : Nat) (hx : x+1 < 2^w) (hc : 2*w ≤ cI) :
    Step FramedIncrement.machine (4*w+2) (fun _ => 0) ![fb w x, List.replicate cI false]
      (fun _ => 0) ![fb w (x+1), List.replicate cI false] := by
  obtain ⟨r, hr, h0, h1, hh, _, _⟩ := FramedIncrement.increment_run w x cI hx hc
  rw [← pair_eq, ← pair_eq]
  apply Step.of_run hr (funext hh)
  funext i
  fin_cases i
  · exact h0
  · exact h1

theorem cmp_local (w b y cC : Nat) (hb : b < 2^w) (hy : y < 2^w) (hc : 2*w+1 ≤ cC) :
    Step WitnessCounterCheck.machine (4*w+4) (fun _ => 0)
      ![fb w b, fb w y, [false], List.replicate cC false] (fun _ => 0)
      ![fb w b, fb w y, [decide (b ≤ y)], List.replicate cC false] := by
  obtain ⟨r, hr, hf⟩ := WitnessCounterCheck.compare_run w b y cC hb hy hc
  exact Step.of_run hr (by rw [hf]; rfl) (by rw [hf]; rfl)

theorem clr_local (w x cL : Nat) (hc : 2*w+1 ≤ cL) :
    Step (MaskedReset.machine FinalPrimeCursor.clearMachine (fun _ => true)) (2*(2*w+1)+2)
      (fun _ => 0) ![fb w x, List.replicate cL false] (fun _ => 0) ![fb w 0, List.replicate cL false] := by
  have h := (FinalPrimeCursor.clear_step (binary w x)).mask (fun _ => true) (fun _ _ => rfl)
    (cap := cL) (by rw [binary_length]; exact hc)
  rw [binary_length] at h
  have eH : (Fin.addCases (motive := fun _ : Fin (1+1) => ℕ) (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0)) =
      (fun _ => 0) := by
    funext i; fin_cases i <;> rfl
  have eH' : (Fin.addCases (motive := fun _ : Fin (1+1) => ℕ)
      (fun i : Fin 1 => if (fun _ => true) i = true then 0 else (fun _ => 2*w+1) i) (fun _ : Fin 1 => 0)) =
      (fun _ => 0) := by
    funext i; fin_cases i <;> rfl
  rw [eH, eH', pair_eq, pair_eq] at h
  exact h

theorem pad_false (R : Nat) (hR : 1 ≤ R) : ZeroPadding.pad R [false] = List.replicate R false := by
  obtain ⟨k, rfl⟩ : ∃ k, R = k+1 := ⟨R-1, by omega⟩
  simp [ZeroPadding.pad, List.replicate_succ]

theorem pad_zero (l : List Bool) : ZeroPadding.pad 0 l = l := by
  simp [ZeroPadding.pad]

/-- The comparison with its flag cell padded to `R` (the flag lives on a blank `0^R` scratch tape). -/
theorem cmp_localR (w b y R : Nat) (hb : b < 2^w) (hy : y < 2^w) (hR : 2*w+1 ≤ R) :
    Step WitnessCounterCheck.machine (4*w+4) (fun _ => 0)
      ![fb w b, fb w y, List.replicate R false, List.replicate R false] (fun _ => 0)
      ![fb w b, fb w y, ZeroPadding.pad R [decide (b ≤ y)], List.replicate R false] := by
  have h := (cmp_local w b y R hb hy hR).pad ![0, 0, R, 0]
  have e1 : (fun i => ZeroPadding.pad (![0, 0, R, 0] i)
      (![fb w b, fb w y, [false], List.replicate R false] i)) =
      ![fb w b, fb w y, List.replicate R false, List.replicate R false] := by
    funext i; fin_cases i <;> simp [pad_false R (by omega)]
  have e2 : (fun i => ZeroPadding.pad (![0, 0, R, 0] i)
      (![fb w b, fb w y, [decide (b ≤ y)], List.replicate R false] i)) =
      ![fb w b, fb w y, ZeroPadding.pad R [decide (b ≤ y)], List.replicate R false] := by
    funext i; fin_cases i <;> simp
  rw [e1, e2] at h
  exact h

/-- The flag reset, on the `R`-padded flag with the cell bank's clock `1^R` and log `0^(R+1)`. -/
theorem rst_localR (b : Bool) (R : Nat) (hR : 1 ≤ R) :
    Step (RecoveryScratchErase.resetMachine 1) (2*R+4) (fun _ => 0)
      ![ZeroPadding.pad R [b], List.replicate R true, List.replicate (R+1) false]
      (fun _ => 0) ![List.replicate R false, List.replicate R true, List.replicate (R+1) false] := by
  have h := Step.of_ready (RecoveryScratchErase.erase_ready (t := 1) R (R+1) (fun _ => ZeroPadding.pad R [b])
    (fun _ => by rw [ZeroPadding.pad_length]; simp; omega))
  have e1 : (Fin.addCases (motive := fun _ : Fin (1+1+1) => List Bool)
      (Fin.addCases (motive := fun _ : Fin (1+1) => List Bool) (fun _ : Fin 1 => ZeroPadding.pad R [b])
        (fun _ : Fin 1 => List.replicate R true)) (fun _ : Fin 1 => List.replicate (R+1) false)) =
      ![ZeroPadding.pad R [b], List.replicate R true, List.replicate (R+1) false] := by
    funext i; fin_cases i <;> rfl
  have e2 : (Fin.addCases (motive := fun _ : Fin (1+1+1) => List Bool)
      (Fin.addCases (motive := fun _ : Fin (1+1) => List Bool) (fun _ : Fin 1 => List.replicate R false)
        (fun _ : Fin 1 => List.replicate R true)) (fun _ : Fin 1 => List.replicate (max (R+1) (R+1)) false)) =
      ![List.replicate R false, List.replicate R true, List.replicate (R+1) false] := by
    funext i; fin_cases i <;> (simp only [max_self]; rfl)
  rw [e1, e2] at h
  exact h

/-! ## 2. The stages docked on a bank through a slot map `sl : Fin 8 → Fin t`

`sl 0` digit `x`, `sl 1` bound `b`, `sl 2` flag `[false]`, `sl 3` increment scratch `0^cI`, `sl 4` compare scratch
`0^cC`, `sl 5` clear log `0^cL`, `sl 6` eraser driver `[true]`, `sl 7` eraser log `[false,false]`. -/

section Dock
variable {t : Nat} (sl : Fin 8 → Fin t)

def incM := RecoveryFocus.machine (sl ∘ ![0, 3]) FramedIncrement.machine
def cmpM := RecoveryFocus.machine (sl ∘ ![1, 0, 2, 4]) WitnessCounterCheck.machine
def clrM := RecoveryFocus.machine (sl ∘ ![0, 5]) (MaskedReset.machine FinalPrimeCursor.clearMachine (fun _ => true))
def rstM := RecoveryFocus.machine (sl ∘ ![2, 6, 7]) (RecoveryScratchErase.resetMachine 1)

/-- **The generic digit step**, continuing with `K` on a carry. -/
def digitStep {sK : Nat} (K : Machine t sK) :=
  Composition.machine (incM sl) (Composition.machine (cmpM sl)
    (CloseoutRowsOriginalSwitch.machine (Composition.machine (clrM sl) (Composition.machine (rstM sl) K))
      (rstM sl) (sl 2)))

/-- The resident words a digit step needs: every scratch word is a cell-bank blank `0^R`, the eraser is the
cell bank's clock `1^R` and log `0^(R+1)`. -/
structure Ready (w R : Nat) (H : Fin t → ℕ) (A : Fin t → List Bool) : Prop where
  heads : ∀ i, H (sl i) = 0
  flag : A (sl 2) = List.replicate R false
  capI : A (sl 3) = List.replicate R false
  capC : A (sl 4) = List.replicate R false
  capL : A (sl 5) = List.replicate R false
  drv : A (sl 6) = List.replicate R true
  log : A (sl 7) = List.replicate (R+1) false
  hR : 2*w+1 ≤ R

theorem update_same (A : Fin t → List Bool) (j : Fin t) (v : List Bool) (h : A j = v) :
    Function.update A j v = A := by
  rw [← h]; exact Function.update_eq_self j A

variable (hinj : Function.Injective sl)
include hinj

theorem inc_at (w x cI : Nat) (H : Fin t → ℕ) (A : Fin t → List Bool) (hH : ∀ i, H (sl i) = 0)
    (hX : A (sl 0) = fb w x) (hI : A (sl 3) = List.replicate cI false) (hx : x+1 < 2^w) (hc : 2*w ≤ cI) :
    Step (incM sl) (4*w+2) H A H (Function.update A (sl 0) (fb w (x+1))) := by
  have hs : Function.Injective (sl ∘ ![0, 3]) := hinj.comp (by decide)
  have h := SymVerdict.focus_at (inc_local w x cI hx hc) (sl ∘ ![0, 3]) hs H A
    (fun j => by fin_cases j <;> exact hH _) (fun j => by fin_cases j <;> simp [hX, hI])
  rw [dockH_existing _ H _ (fun j => by fin_cases j <;> exact hH _),
    SymVerdict.install_update _ hs A _ 0 (fun j hj => by fin_cases j <;> first | exact absurd rfl hj | simp [hI])] at h
  exact h

theorem cmp_at (w b y R : Nat) (H : Fin t → ℕ) (A : Fin t → List Bool) (hH : ∀ i, H (sl i) = 0)
    (hB : A (sl 1) = fb w b) (hY : A (sl 0) = fb w y) (hF : A (sl 2) = List.replicate R false)
    (hCc : A (sl 4) = List.replicate R false) (hb : b < 2^w) (hy : y < 2^w) (hc : 2*w+1 ≤ R) :
    Step (cmpM sl) (4*w+4) H A H (Function.update A (sl 2) (ZeroPadding.pad R [decide (b ≤ y)])) := by
  have hs : Function.Injective (sl ∘ ![1, 0, 2, 4]) := hinj.comp (by decide)
  have h := SymVerdict.focus_at (cmp_localR w b y R hb hy hc) (sl ∘ ![1, 0, 2, 4]) hs H A
    (fun j => by fin_cases j <;> exact hH _) (fun j => by fin_cases j <;> simp [hB, hY, hF, hCc])
  rw [dockH_existing _ H _ (fun j => by fin_cases j <;> exact hH _),
    SymVerdict.install_update _ hs A _ 2 (fun j hj => by
      fin_cases j
      · simp [hB]
      · simp [hY]
      · exact absurd rfl hj
      · simp [hCc])] at h
  exact h

theorem clr_at (w x cL : Nat) (H : Fin t → ℕ) (A : Fin t → List Bool) (hH : ∀ i, H (sl i) = 0)
    (hX : A (sl 0) = fb w x) (hL : A (sl 5) = List.replicate cL false) (hc : 2*w+1 ≤ cL) :
    Step (clrM sl) (2*(2*w+1)+2) H A H (Function.update A (sl 0) (fb w 0)) := by
  have hs : Function.Injective (sl ∘ ![0, 5]) := hinj.comp (by decide)
  have h := SymVerdict.focus_at (clr_local w x cL hc) (sl ∘ ![0, 5]) hs H A
    (fun j => by fin_cases j <;> exact hH _) (fun j => by fin_cases j <;> simp [hX, hL])
  rw [dockH_existing _ H _ (fun j => by fin_cases j <;> exact hH _),
    SymVerdict.install_update _ hs A _ 0 (fun j hj => by fin_cases j <;> first | exact absurd rfl hj | simp [hL])] at h
  exact h

theorem rst_at (b : Bool) (R : Nat) (hR : 1 ≤ R) (H : Fin t → ℕ) (A : Fin t → List Bool) (hH : ∀ i, H (sl i) = 0)
    (hF : A (sl 2) = ZeroPadding.pad R [b]) (hD : A (sl 6) = List.replicate R true)
    (hG : A (sl 7) = List.replicate (R+1) false) :
    Step (rstM sl) (2*R+4) H A H (Function.update A (sl 2) (List.replicate R false)) := by
  have hs : Function.Injective (sl ∘ ![2, 6, 7]) := hinj.comp (by decide)
  have h := SymVerdict.focus_at (rst_localR b R hR) (sl ∘ ![2, 6, 7]) hs H A
    (fun j => by fin_cases j <;> exact hH _) (fun j => by fin_cases j <;> simp [hF, hD, hG])
  rw [dockH_existing _ H _ (fun j => by fin_cases j <;> exact hH _),
    SymVerdict.install_update _ hs A _ 0 (fun j hj => by
      fin_cases j
      · exact absurd rfl hj
      · simp [hD]
      · simp [hG])] at h
  exact h

/-! ## 3. The digit step: no carry, and carry into `K` -/

theorem ne_of_idx {i j : Fin 8} (h : i ≠ j) : sl i ≠ sl j := fun e => h (hinj e)

/-- **No carry** (`x+1 < b`): the digit advances; every other port and head is unchanged. -/
theorem digit_noCarry {sK : Nat} (K : Machine t sK) (w x b R : Nat) (H : Fin t → ℕ) (A : Fin t → List Bool)
    (hr : Ready sl w R H A) (hX : A (sl 0) = fb w x) (hB : A (sl 1) = fb w b)
    (hxb : x+1 < b) (hb : b < 2^w) :
    Step (digitStep sl K) (4*w+2+1+((4*w+4)+1+((2*R+4)+2))) H A H (Function.update A (sl 0) (fb w (x+1))) := by
  have s1 := inc_at sl hinj w x R H A hr.heads hX hr.capI (by omega) (by have := hr.hR; omega)
  set A1 := Function.update A (sl 0) (fb w (x+1)) with hA1
  have n20 := ne_of_idx sl hinj (i := 2) (j := 0) (by decide)
  have n10 := ne_of_idx sl hinj (i := 1) (j := 0) (by decide)
  have n40 := ne_of_idx sl hinj (i := 4) (j := 0) (by decide)
  have n60 := ne_of_idx sl hinj (i := 6) (j := 0) (by decide)
  have n70 := ne_of_idx sl hinj (i := 7) (j := 0) (by decide)
  have hR1 : 1 ≤ R := by have := hr.hR; omega
  have s2 := cmp_at sl hinj w b (x+1) R H A1 hr.heads
    (by rw [hA1, Function.update_of_ne n10, hB]) (by rw [hA1, Function.update_self])
    (by rw [hA1, Function.update_of_ne n20, hr.flag])
    (by rw [hA1, Function.update_of_ne n40, hr.capC]) hb (by omega) hr.hR
  have hdec : decide (b ≤ x+1) = false := by simp; omega
  rw [hdec] at s2
  have s3 := rst_at sl hinj false R hR1 H (Function.update A1 (sl 2) (ZeroPadding.pad R [false])) hr.heads
    (by rw [Function.update_self]) (by rw [Function.update_of_ne (ne_of_idx sl hinj (by decide)), hA1,
      Function.update_of_ne n60, hr.drv])
    (by rw [Function.update_of_ne (ne_of_idx sl hinj (by decide)), hA1, Function.update_of_ne n70, hr.log])
  have e3 : Function.update (Function.update A1 (sl 2) (ZeroPadding.pad R [false])) (sl 2)
      (List.replicate R false) = A1 := by
    rw [Function.update_idem, update_same A1 (sl 2) _ (by rw [hA1, Function.update_of_ne n20, hr.flag])]
  rw [e3] at s3
  have s4 := CloseoutRowsOriginalSwitch.false_run
    (Composition.machine (clrM sl) (Composition.machine (rstM sl) K)) (rstM sl) (sl 2) s3
    (by rw [Function.update_self, hr.heads, ZeroPadding.read_pad]; rfl)
  exact s1.seq (s2.seq s4)

/-- **Carry** (`x+1 = b`): the digit is cleared to `0`, the flag is restored, and `K` runs. -/
theorem digit_carry {sK : Nat} (K : Machine t sK) (w x b R n : Nat) (H H' : Fin t → ℕ)
    (A A' : Fin t → List Bool) (hr : Ready sl w R H A) (hX : A (sl 0) = fb w x) (hB : A (sl 1) = fb w b)
    (hxb : x+1 = b) (hb : b < 2^w)
    (hK : Step K n H (Function.update A (sl 0) (fb w 0)) H' A') :
    Step (digitStep sl K) (4*w+2+1+((4*w+4)+1+(((2*(2*w+1)+2)+1+((2*R+4)+1+n))+2))) H A H' A' := by
  have s1 := inc_at sl hinj w x R H A hr.heads hX hr.capI (by omega) (by have := hr.hR; omega)
  set A1 := Function.update A (sl 0) (fb w (x+1)) with hA1
  have n20 := ne_of_idx sl hinj (i := 2) (j := 0) (by decide)
  have n10 := ne_of_idx sl hinj (i := 1) (j := 0) (by decide)
  have n40 := ne_of_idx sl hinj (i := 4) (j := 0) (by decide)
  have n50 := ne_of_idx sl hinj (i := 5) (j := 0) (by decide)
  have n60 := ne_of_idx sl hinj (i := 6) (j := 0) (by decide)
  have n70 := ne_of_idx sl hinj (i := 7) (j := 0) (by decide)
  have n02 := ne_of_idx sl hinj (i := 0) (j := 2) (by decide)
  have n52 := ne_of_idx sl hinj (i := 5) (j := 2) (by decide)
  have n62 := ne_of_idx sl hinj (i := 6) (j := 2) (by decide)
  have n72 := ne_of_idx sl hinj (i := 7) (j := 2) (by decide)
  have hR1 : 1 ≤ R := by have := hr.hR; omega
  have s2 := cmp_at sl hinj w b (x+1) R H A1 hr.heads
    (by rw [hA1, Function.update_of_ne n10, hB]) (by rw [hA1, Function.update_self])
    (by rw [hA1, Function.update_of_ne n20, hr.flag])
    (by rw [hA1, Function.update_of_ne n40, hr.capC]) hb (by omega) hr.hR
  have hdec : decide (b ≤ x+1) = true := by simp; omega
  rw [hdec] at s2
  set A2 := Function.update A1 (sl 2) (ZeroPadding.pad R [true]) with hA2
  have c1 := clr_at sl hinj w (x+1) R H A2 hr.heads
    (by rw [hA2, Function.update_of_ne n02, hA1, Function.update_self])
    (by rw [hA2, Function.update_of_ne n52, hA1, Function.update_of_ne n50, hr.capL]) hr.hR
  set A3 := Function.update A2 (sl 0) (fb w 0) with hA3
  have c2 := rst_at sl hinj true R hR1 H A3 hr.heads
    (by rw [hA3, Function.update_of_ne n20, hA2, Function.update_self])
    (by rw [hA3, Function.update_of_ne n60, hA2, Function.update_of_ne n62, hA1, Function.update_of_ne n60, hr.drv])
    (by rw [hA3, Function.update_of_ne n70, hA2, Function.update_of_ne n72, hA1, Function.update_of_ne n70, hr.log])
  have e4 : Function.update A3 (sl 2) (List.replicate R false) = Function.update A (sl 0) (fb w 0) := by
    funext z
    by_cases h2 : z = sl 2
    · subst h2
      rw [Function.update_self, Function.update_of_ne n20, hr.flag]
    · by_cases h0 : z = sl 0
      · subst h0
        rw [Function.update_of_ne n02, hA3, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne h2, hA3, Function.update_of_ne h0, hA2, Function.update_of_ne h2, hA1,
          Function.update_of_ne h0, Function.update_of_ne h0]
  rw [e4] at c2
  have s4 := CloseoutRowsOriginalSwitch.true_run
    (Composition.machine (clrM sl) (Composition.machine (rstM sl) K)) (rstM sl) (sl 2) (c1.seq (c2.seq hK))
    (by rw [hA2, Function.update_self, hr.heads, ZeroPadding.read_pad]; rfl)
  exact s1.seq (s2.seq s4)

end Dock

end
end RowsConstruction.KeyStep
