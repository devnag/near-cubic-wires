import Proof.SourceAssembly.SourceFactorSelCoefReduce
import Proof.SourceAssembly.SourceFactorSelCoefValue

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceFactorSel.Coef
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding RepairOrdinary.RadixSemantics RepairOrdinary.SignedSortKey
open NearCubicWires.SourceFactorSel.CoefPrim NearCubicWires.SourceFactorSel.CoefAcc NearCubicWires.SourceFactorSel.CoefBin
open NearCubicWires.SourceFactorSel.CoefReduce NearCubicWires.SourceFactorSel.CoefValue
noncomputable section

/-! ## Generic docking with a kept set -/

theorem dock_keep {t U s : Nat} {p : Machine t s} {n : Nat} (sl : Fin t → Fin U) (hsl : Function.Injective sl)
    (A : Fin U → List Bool) {E' : Fin t → List Bool}
    (h : Step p n (fun _ => 0) (fun j => A (sl j)) (fun _ => 0) E') (P : Fin t → Prop)
    (hk : ∀ j, P j → E' j = A (sl j)) :
    Step (RecoveryFocus.machine sl p) n (fun _ => 0) A (fun _ => 0) (install sl A E') ∧
      (∀ j, install sl A E' (sl j) = E' j) ∧
      (∀ x, (∀ j, ¬ P j → sl j ≠ x) → install sl A E' x = A x) := by
  refine ⟨dz h sl hsl (fun _ => 0) A (fun _ => rfl) (fun _ => rfl), fun j => install_slot sl hsl A E' j, ?_⟩
  intro x hx
  by_cases hex : ∃ j, sl j = x
  · obtain ⟨j, rfl⟩ := hex
    rw [install_slot sl hsl]
    by_cases hj : P j
    · exact hk j hj
    · exact absurd rfl (hx j hj)
  · exact install_other sl A E' x (fun j e => hex ⟨j, e⟩)

theorem keep_of {t U : Nat} (sl : Fin t → Fin U) (A A' : Fin U → List Bool) (P : Fin t → Prop)
    (h : ∀ x, (∀ j, ¬ P j → sl j ≠ x) → A' x = A x) (lo hi : Nat)
    (hr : ∀ j, ¬ P j → lo ≤ (sl j).val ∧ (sl j).val ≤ hi) : Keep lo hi A A' := by
  intro x hx
  apply h x
  intro j hj e
  subst e
  have := hr j hj
  omega

/-! ## One slot, docked -/

def slotKept (j : Fin 32) : Prop := j.val < 4 ∨ j.val = 7 ∨ j.val = 30

instance : DecidablePred slotKept := fun j => by unfold slotKept; infer_instance

theorem slot_step {U : Nat} (sl : Fin 32 → Fin U) (hsl : Function.Injective sl)
    (f s : Bool) (n d c Qr Qf S C Na Da sa : Nat) (hn : n < 2 ^ c) (hd : d < 2 ^ c) (A : Fin U → List Bool)
    (h0 : f = true → A (sl 0) = recW s n d c Qr) (h1 : A (sl 1) = ZeroPadding.pad S (List.replicate Na true))
    (h2 : A (sl 2) = ZeroPadding.pad S (List.replicate Da true))
    (h3 : A (sl 3) = ZeroPadding.pad S (List.replicate sa true))
    (h7 : A (sl 7) = List.replicate C false) (h30 : A (sl 30) = ZeroPadding.pad Qf [f])
    (hscr : ∀ j : Fin 32, (j.val = 4 ∨ j.val = 5 ∨ j.val = 6 ∨ (8 ≤ j.val ∧ j.val ≠ 30)) →
      A (sl j) = List.replicate S false)
    (hf : AccFits c n d Na Da sa S C) :
    ∃ A' : Fin U → List Bool, Step (RecoveryFocus.machine sl accSwM) (accSwCost f s n d c Na Da sa)
        (fun _ => 0) A (fun _ => 0) A' ∧
      A' (sl 4) = ZeroPadding.pad S (List.replicate (Na * (if f then n else 1)) true) ∧
      A' (sl 5) = ZeroPadding.pad S (List.replicate (Da * (if f then d else 1)) true) ∧
      A' (sl 6) = ZeroPadding.pad S (List.replicate (sa + (if f then s.toNat else 0)) true) ∧
      (∀ x, (∀ j, ¬ slotKept j → sl j ≠ x) → A' x = A x) := by
  obtain ⟨L, hs, l4, l5, l6, lk, l7, l30⟩ := accsw_run f s n d c Qr S Qf S C Na Da sa hn hd
    (fun j => A (sl j)) h0 h1 h2 h3 h7 h30 hscr hf
  obtain ⟨st, sv, sk⟩ := dock_keep sl hsl A hs slotKept (by
    intro j hj
    rcases hj with h | h | h
    · exact lk j h
    · have e : j = 7 := Fin.ext h
      subst e
      exact l7
    · have e : j = 30 := Fin.ext h
      subst e
      exact l30)
  exact ⟨_, st, (sv 4).trans l4, (sv 5).trans l5, (sv 6).trans l6, sk⟩

/-! ## The per-slot values passed to the accumulator -/

def nS (f : Bool) (t : ℚ) : ℕ := if f then t.num.natAbs else 0
def dS (f : Bool) (t : ℚ) : ℕ := if f then t.den else 0
def sS (f : Bool) (t : ℚ) : Bool := if f then decide (t.num < 0) else false

theorem nS_mul (f : Bool) (t : ℚ) (N : ℕ) : N * (if f then nS f t else 1) = N * nA f t := by
  cases f <;> rfl
theorem dS_mul (f : Bool) (t : ℚ) (N : ℕ) : N * (if f then dS f t else 1) = N * dA f t := by
  cases f <;> rfl
theorem sS_add (f : Bool) (t : ℚ) (N : ℕ) : N + (if f then (sS f t).toNat else 0) = N + sA f t := by
  cases f <;> rfl

theorem slot_bits (f : Bool) (t : ℚ) (cw : ℕ) (h : f = true → t.num.natAbs < 2 ^ cw ∧ t.den < 2 ^ cw) :
    nS f t < 2 ^ cw ∧ dS f t < 2 ^ cw := by
  cases f
  · exact ⟨Nat.two_pow_pos cw, Nat.two_pow_pos cw⟩
  · exact h rfl

theorem slot_record (f : Bool) (t : ℚ) (cw Qr : ℕ) (h : f = true) :
    ZeroPadding.pad Qr (CloseoutRowsEstimatorCoefficients.Product.record cw t) = recW (sS f t) (nS f t) (dS f t) cw Qr := by
  subst h
  exact record_eq cw Qr t

/-! ## The machine -/





/-- The consumer's three words for a coefficient. -/
def coefWord (b R : ℕ) (x : ℚ) (i : Fin 3) : List Bool :=
  ZeroPadding.pad R (frame (CloseoutRowsEstimatorCoefficients.Stream.recordFields b
    (CloseoutFinalC10SupplierCalls.coefficientEstimate x) 0 0 ⟨i.val, by omega⟩))

/-! ## The run -/

theorem nA_le (f : Bool) (t : ℚ) (T : ℕ) (hT : 1 ≤ T) (h : f = true → t.num.natAbs < T) : nA f t ≤ T := by
  cases f
  · exact hT
  · exact (h rfl).le

theorem dA_le (f : Bool) (t : ℚ) (T : ℕ) (hT : 1 ≤ T) (h : f = true → t.den < T) : dA f t ≤ T := by
  cases f
  · exact hT
  · exact (h rfl).le

theorem sA_le (f : Bool) (t : ℚ) : sA f t ≤ 1 := by
  unfold sA
  split
  · exact Bool.toNat_le _
  · exact Nat.zero_le _

theorem accFits_of (c n d Na Da sa S C X T : ℕ) (hT : 1 ≤ T) (hn : n < T) (hd : d < T) (hNa : Na ≤ X)
    (hDa : Da ≤ 2 * X) (hsa : sa ≤ 5) (hS : 2 * c + 3 ≤ S) (hc : 8 * c + 15 ≤ C) (hC : 10 * (X * T) + 8 ≤ C) :
    AccFits c n d Na Da sa S C := by
  have hXT : X ≤ X * T := Nat.le_mul_of_pos_right X hT
  have e1 : Na * (2 * n + 3) ≤ X * (2 * T + 3) := Nat.mul_le_mul hNa (by omega)
  have e2 : Da * (2 * d + 3) ≤ (2 * X) * (2 * T + 3) := Nat.mul_le_mul hDa (by omega)
  have r1 : X * (2 * T + 3) = 2 * (X * T) + 3 * X := by ring
  have r2 : (2 * X) * (2 * T + 3) = 4 * (X * T) + 6 * X := by ring
  exact ⟨by omega, by omega, by unfold parseCost; omega, by omega, by omega, by omega⟩

end
end NearCubicWires.SourceFactorSel.Coef

