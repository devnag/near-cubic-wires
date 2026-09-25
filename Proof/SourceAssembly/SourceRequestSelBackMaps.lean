import Proof.SourceAssembly.SourceFactorSelHdrBlock
import Proof.SourceAssembly.SourceFactorSelKBridge
import Proof.SourceAssembly.SourceFactorSelSlots4
import Proof.SourceAssembly.SourceRequestSelFrontB
import Proof.SourceAssembly.SourceRequestSelRho

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceRequest.SelBack
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open SourceInterfaces RepairRepresentation
open NearCubicWires.SourceRequest.SelFront
noncomputable section

section
variable {mode : Bool} {da : DecompositionAlgorithm} {n0 : Nat}
  {circuit : BooleanCircuit n0} {pcpp : PointwisePCPP circuit}
variable (P : FactorLoop.FactorProducer mode da pcpp)

/-- A fixed port. -/
def loP (k : Nat) (h : k < NF) : Fin (NF + (19 + 4 * P.t)) := Fin.castAdd _ ⟨k, h⟩
/-- A region port. -/
def rgP (x : Fin (19 + 4 * P.t)) : Fin (NF + (19 + 4 * P.t)) := Fin.natAdd NF x

theorem rg_val (x : Fin (19 + 4 * P.t)) : (rgP P x).val = NF + x.val := rfl

/-- A slot's `k`-th input port (`k < 17`). -/
def inPort (i k : Nat) : Nat :=
  if k < 4 then 1206 + 4 * i + k
  else ([129, 141, 103, 104, 19, 29, 30, 21, 22, 23, 24, 31, 42] : List Nat).getD (k - 4) 0

theorem inPort_lt : ∀ i < 4, ∀ k < 17, inPort i k < 1300 := by decide
theorem inPort_inj : ∀ i < 4, ∀ k < 17, ∀ k' < 17, inPort i k = inPort i k' → k = k' := by decide

/-- **Slot `i`'s dock** (`hd : P.d = 16`, both producers). -/
def slB (hd : P.d = 16) (i : Fin 4) (j : Fin 1121) : Fin (NF + (19 + 4 * P.t)) :=
  if h17 : j.val < 17 then loP P (inPort i.val j.val) (by have := inPort_lt i.val i.isLt j.val h17; unfold NF; omega)
  else if h33 : j.val < 33 then rgP P (FactorLoop.cslot P i (P.descSlots (Fin.cast hd.symm ⟨j.val - 17, by omega⟩)))
  else if j.val = 33 then loP P (1400 + i.val) (by have := i.isLt; unfold NF; omega)
  else loP P (1500 + 1100 * i.val + (j.val - 34)) (by have := i.isLt; have := j.isLt; unfold NF; omega)

/-- The value of a non-region slot port. -/
def loVal (i j : Nat) : Nat := if j < 17 then inPort i j else if j = 33 then 1400 + i else 1500 + 1100 * i + (j - 34)

theorem loVal_cases (i j : Nat) (hi : i < 4) (hn : ¬ (17 ≤ j ∧ j < 33)) :
    (j < 17 ∧ loVal i j = inPort i j ∧ inPort i j < 1300) ∨ (j = 33 ∧ loVal i j = 1400 + i) ∨
      (34 ≤ j ∧ loVal i j = 1500 + 1100 * i + (j - 34)) := by
  unfold loVal
  by_cases h17 : j < 17
  · left; exact ⟨h17, by rw [if_pos h17], inPort_lt i hi j h17⟩
  · rw [if_neg h17]
    by_cases h33 : j = 33
    · right; left; exact ⟨h33, by rw [if_pos h33]⟩
    · right; right; exact ⟨by omega, by rw [if_neg h33]⟩

theorem slB_lo (hd : P.d = 16) (i : Fin 4) (j : Fin 1121) (h : ¬ (17 ≤ j.val ∧ j.val < 33)) :
    (slB P hd i j).val = loVal i.val j.val := by
  unfold slB loVal
  by_cases h17 : j.val < 17
  · rw [dif_pos h17, if_pos h17]; rfl
  · rw [dif_neg h17, dif_neg (by omega), if_neg h17]
    split <;> rfl

theorem slB_rg (hd : P.d = 16) (i : Fin 4) (j : Fin 1121) (h1 : 17 ≤ j.val) (h2 : j.val < 33) :
    slB P hd i j = rgP P (FactorLoop.cslot P i (P.descSlots (Fin.cast hd.symm ⟨j.val - 17, by omega⟩))) := by
  unfold slB; rw [dif_neg (by omega), dif_pos h2]

theorem rgP_inj (x y : Fin (19 + 4 * P.t)) (h : rgP P x = rgP P y) : x = y :=
  Fin.ext (by have hv := congrArg Fin.val h; rw [rg_val, rg_val] at hv; omega)

theorem slB_inj (hd : P.d = 16) (i : Fin 4) : Function.Injective (slB P hd i) := by
  intro j j' h
  have hi := i.isLt; have := j.isLt; have := j'.isLt
  by_cases hj : 17 ≤ j.val ∧ j.val < 33
  · by_cases hj' : 17 ≤ j'.val ∧ j'.val < 33
    · rw [slB_rg P hd i j hj.1 hj.2, slB_rg P hd i j' hj'.1 hj'.2] at h
      have h1 := rgP_inj P _ _ h
      have h2 := FactorLoop.cslot_injective P i h1
      have h3 := P.descInjective h2
      have h4 := congrArg Fin.val h3
      simp at h4
      apply Fin.ext; omega
    · exfalso
      have hv := congrArg Fin.val h
      rw [slB_rg P hd i j hj.1 hj.2, rg_val, slB_lo P hd i j' hj'] at hv
      unfold NF at hv
      rcases loVal_cases i.val j'.val hi hj' with ⟨_, e, e'⟩ | ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] at hv <;> omega
  · by_cases hj' : 17 ≤ j'.val ∧ j'.val < 33
    · exfalso
      have hv := congrArg Fin.val h
      rw [slB_rg P hd i j' hj'.1 hj'.2, rg_val, slB_lo P hd i j hj] at hv
      unfold NF at hv
      rcases loVal_cases i.val j.val hi hj with ⟨_, e, e'⟩ | ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] at hv <;> omega
    · have hv := congrArg Fin.val h
      rw [slB_lo P hd i j hj, slB_lo P hd i j' hj'] at hv
      apply Fin.ext
      rcases loVal_cases i.val j.val hi hj with ⟨h1, e, e'⟩ | ⟨h1, e⟩ | ⟨h1, e⟩ <;>
        rcases loVal_cases i.val j'.val hi hj' with ⟨h2, f, f'⟩ | ⟨h2, f⟩ | ⟨h2, f⟩ <;> rw [e, f] at hv <;>
        first | omega | exact inPort_inj i.val hi j.val h1 j'.val h2 hv

theorem slB_disj (hd : P.d = 16) :
    ∀ (i i' : Fin 4) (j j' : Fin 1121), i ≠ i' → 17 ≤ j.val → slB P hd i j ≠ slB P hd i' j' := by
  intro i i' j j' hii hj h
  have hi := i.isLt; have hi' := i'.isLt; have := j.isLt; have := j'.isLt
  have hne : i.val ≠ i'.val := fun e => hii (Fin.ext e)
  by_cases hjr : j.val < 33
  · rw [slB_rg P hd i j hj hjr] at h
    by_cases hj' : 17 ≤ j'.val ∧ j'.val < 33
    · rw [slB_rg P hd i' j' hj'.1 hj'.2] at h
      exact FactorLoop.cslot_ne P i i' _ _ hii (rgP_inj P _ _ h)
    · have hv := congrArg Fin.val h
      rw [rg_val, slB_lo P hd i' j' hj'] at hv
      unfold NF at hv
      rcases loVal_cases i'.val j'.val hi' hj' with ⟨_, e, e'⟩ | ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] at hv <;> omega
  · have hv := congrArg Fin.val h
    rw [slB_lo P hd i j (by omega)] at hv
    by_cases hj' : 17 ≤ j'.val ∧ j'.val < 33
    · rw [slB_rg P hd i' j' hj'.1 hj'.2, rg_val] at hv
      unfold NF at hv
      rcases loVal_cases i.val j.val hi (by omega) with ⟨_, e, e'⟩ | ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] at hv <;> omega
    · rw [slB_lo P hd i' j' hj'] at hv
      rcases loVal_cases i.val j.val hi (by omega) with ⟨h1, e, e'⟩ | ⟨h1, e⟩ | ⟨h1, e⟩ <;>
        rcases loVal_cases i'.val j'.val hi' hj' with ⟨h2, f, f'⟩ | ⟨h2, f⟩ | ⟨h2, f⟩ <;> rw [e, f] at hv <;> omega

/-- The header block's dock. -/
def hdSl (j : Fin 35) : Fin (NF + (19 + 4 * P.t)) :=
  if j.val = 0 then loP P 1222 (by unfold NF; omega)
  else if j.val < 5 then loP P (24 + j.val) (by have := j.isLt; unfold NF; omega)
  else if j.val = 5 then loP P 31 (by unfold NF; omega)
  else if j.val = 6 then loP P 43 (by unfold NF; omega)
  else if j.val = 7 then rgP P ⟨0, by omega⟩
  else loP P (6000 + j.val) (by have := j.isLt; unfold NF; omega)

theorem hdSl_val (j : Fin 35) : (hdSl P j).val = if j.val = 0 then 1222 else if j.val < 5 then 24 + j.val
    else if j.val = 5 then 31 else if j.val = 6 then 43 else if j.val = 7 then NF else 6000 + j.val := by
  unfold hdSl
  split <;> [rfl; split <;> [rfl; split <;> [rfl; split <;> [rfl; split <;> rfl]]]]

theorem hdSl_inj : Function.Injective (hdSl P) := by
  intro j j' h
  have hv := congrArg Fin.val h
  rw [hdSl_val, hdSl_val] at hv
  have := j.isLt; have := j'.isLt
  apply Fin.ext
  split at hv <;> split at hv <;> (try split at hv) <;> (try split at hv) <;> (try split at hv) <;>
    (try split at hv) <;> (try split at hv) <;> (try split at hv) <;> (try split at hv) <;> (try split at hv) <;>
    (try unfold NF at hv) <;> omega

/-- The coefficient stage's dock. -/
def cfSl (j : Fin 245) : Fin (NF + (19 + 4 * P.t)) :=
  if j.val < 4 then loP P (1400 + j.val) (by have := j.isLt; unfold NF; omega)
  else if j.val < 8 then loP P (1207 + 4 * (j.val - 4)) (by have := j.isLt; unfold NF; omega)
  else if j.val = 8 then loP P 1223 (by unfold NF; omega)
  else if j.val = 9 then loP P 32 (by unfold NF; omega)
  else if j.val = 10 then loP P 39 (by unfold NF; omega)
  else if j.val < 14 then loP P (23 + j.val) (by have := j.isLt; unfold NF; omega)
  else if j.val = 14 then loP P 44 (by unfold NF; omega)
  else loP P (6100 + j.val) (by have := j.isLt; unfold NF; omega)

theorem cfSl_val (j : Fin 245) : (cfSl P j).val = if j.val < 4 then 1400 + j.val else if j.val < 8 then 1207 + 4 * (j.val - 4)
    else if j.val = 8 then 1223 else if j.val = 9 then 32 else if j.val = 10 then 39 else if j.val < 14 then 23 + j.val
    else if j.val = 14 then 44 else 6100 + j.val := by
  unfold cfSl
  split <;> [rfl; split <;> [rfl; split <;> [rfl; split <;> [rfl; split <;> [rfl; split <;> [rfl; split <;> rfl]]]]]]

theorem cfSl_inj : Function.Injective (cfSl P) := by
  intro j j' h
  have hv := congrArg Fin.val h
  rw [cfSl_val, cfSl_val] at hv
  have := j.isLt; have := j'.isLt
  apply Fin.ext
  split at hv <;> split at hv <;> (try split at hv) <;> (try split at hv) <;> (try split at hv) <;>
    (try split at hv) <;> (try split at hv) <;> (try split at hv) <;> (try split at hv) <;> (try split at hv) <;>
    (try split at hv) <;> (try split at hv) <;> (try split at hv) <;> (try split at hv) <;> omega

end
end
end NearCubicWires.SourceRequest.SelBack

