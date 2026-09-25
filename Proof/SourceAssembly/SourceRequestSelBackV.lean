import Proof.SourceAssembly.SourceRequestSelLocalMach

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.SourceRequest.SelLocal
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open SourceInterfaces RepairSource.VerifierDecoding
open NearCubicWires.ComponentwiseBranchExtraction NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.SourceRequest.SelFront NearCubicWires.SourceRequest.SelBack
open NearCubicWires.SourceRequest.SelSpec NearCubicWires.SourceRequest.CurSpec
open NearCubicWires.SourceRequest.CurContract NearCubicWires.SourceRequest.CoordBridge NearCubicWires.SourceRequest.TermReader
open NearCubicWires.SourceFactorSel.Modes (kindOf bmOf bitsOf)
noncomputable section

/-! ## The coefficient dock's port values, decided once -/

/-- `SelBack.cfSl`'s port values. -/
def cfv (j : Nat) : Nat :=
  if j < 4 then 1400 + j else if j < 8 then 1207 + 4 * (j - 4) else if j = 8 then 1223 else if j = 9 then 32
  else if j = 10 then 39 else if j < 14 then 23 + j else if j = 14 then 44 else 6100 + j

theorem cfv_lo : ∀ j < 245, 4 ≤ j → cfv j < 1400 ∨ (6000 ≤ cfv j ∧ cfv j < 7000) := by decide
theorem cfv_mid : ∀ j < 245, 4 ≤ j → j < 8 → cfv j = 1200 + (7 + 4 * (j - 4)) := by decide
theorem cfv_hi : ∀ j < 245, 15 ≤ j → cfv j = 6100 + j := by decide
theorem cfv_heads : ∀ j < 245, 9 ≤ j → ¬ (300 ≤ cfv j ∧ cfv j < 1400) := by decide
theorem cfv_cv : ∀ j < 245, 4 ≤ j → (cfv j < 6008 ∨ 6035 ≤ cfv j) ∧ cfv j < 7000 := by decide
theorem cfv_frame : ∀ j < 245, ¬ (j < 11 ∨ j = 14) → (34 ≤ cfv j ∧ cfv j < 37) ∨ (6115 ≤ cfv j ∧ cfv j < 7000) := by
  decide

section
variable {n0 : Nat} {circuit : BooleanCircuit n0} {pcpp : PointwisePCPP circuit}

theorem cfSl_cfv {mode : Bool} {da : RepairRepresentation.DecompositionAlgorithm}
    (P : FactorLoop.FactorProducer mode da pcpp) (j : Fin 245) : (cfSl P j).val = cfv j.val := cfSl_val P j

theorem curSl_hi (ph : Phase) (j : Fin 128) (h : 6 ≤ j.val) : (SelFront.curSl ph j).val = 1200 + j.val := by
  rw [SelFront.curSl_val]
  have h0 : j.val ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) h)
  have h1 : j.val ≠ 1 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) h)
  have h2 : j.val ≠ 2 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) h)
  have h3 : j.val ≠ 3 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) h)
  have h4 : j.val ≠ 4 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) h)
  have h5 : j.val ≠ 5 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) h)
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]

/-- A coefficient bound by a value bound `V`. -/
theorem tco_V (T : Bool → List (CircuitMonomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp) 1)) (V : Nat)
    (hV : 2 ≤ V) (hTV : ∀ r, ∀ mo ∈ T r, mo.coefficient.num.natAbs < V ∧ mo.coefficient.den < V)
    (x : Option Fac) :
    (SourceFactorSel.CoefBridge.tco T x).num.natAbs < V ∧ (SourceFactorSel.CoefBridge.tco T x).den < V := by
  have z : ((0 : ℚ).num.natAbs < V ∧ (0 : ℚ).den < V) := by simp; omega
  cases x with
  | none => exact z
  | some f =>
    cases f with
    | sys r => exact z
    | term r j =>
      simp only [SourceFactorSel.CoefBridge.tco]
      cases h : (T r)[j]? with
      | none => exact z
      | some mo => exact hTV r mo (List.mem_of_getElem? h)

end

end
end NearCubicWires.SourceRequest.SelLocal

