import Proof.SourceAssembly.SourceRequestSelBackThr

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.SourceRequest.SelBack
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open SourceInterfaces RepairSource.VerifierDecoding
open NearCubicWires.ComponentwiseBranchExtraction NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.SourceRequest.SelFront NearCubicWires.SourceRequest.SelSpec NearCubicWires.SourceRequest.CurSpec
open NearCubicWires.SourceRequest.CurContract NearCubicWires.SourceRequest.CoordBridge NearCubicWires.SourceRequest.TermReader
open NearCubicWires.SourceFactorSel.Modes (kindOf bmOf bitsOf)
noncomputable section

section run
variable {n0 : Nat} {circuit : BooleanCircuit n0} {pcpp : PointwisePCPP circuit}

theorem tco_bits (T : Bool → List (CircuitMonomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp) 1)) (cw : Nat)
    (hcw1 : 1 ≤ cw) (hT : ∀ r, ∀ mo ∈ T r, mo.coefficient.num.natAbs < 2 ^ cw ∧ mo.coefficient.den < 2 ^ cw)
    (x : Option Fac) :
    (SourceFactorSel.CoefBridge.tco T x).num.natAbs < 2 ^ cw ∧ (SourceFactorSel.CoefBridge.tco T x).den < 2 ^ cw := by
  have h2 : 2 ≤ 2 ^ cw := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ cw := Nat.pow_le_pow_right (by decide) hcw1
  have z : ((0 : ℚ).num.natAbs < 2 ^ cw ∧ (0 : ℚ).den < 2 ^ cw) := by simp; omega
  cases x with
  | none => exact z
  | some f =>
    cases f with
    | sys r => exact z
    | term r j =>
      simp only [SourceFactorSel.CoefBridge.tco]
      cases h : (T r)[j]? with
      | none => exact z
      | some mo => exact hT r mo (List.mem_of_getElem? h)

/-- The four slots' cost at cursor record `σ` (THR). -/
def fourCostT (bits : List Bool) (iL iR : Nat) (σ : Option Sel) (cwid cw D : Nat) : Nat :=
  SourceFactorSel.Slot.slotCost bits (if fSide (facAt σ 0) then iR else iL) (fIdx (facAt σ 0)) cwid cw D + 1 +
  (SourceFactorSel.Slot.slotCost bits (if fSide (facAt σ 1) then iR else iL) (fIdx (facAt σ 1)) cwid cw D + 1 +
  (SourceFactorSel.Slot.slotCost bits (if fSide (facAt σ 2) then iR else iL) (fIdx (facAt σ 2)) cwid cw D + 1 +
  SourceFactorSel.Slot.slotCost bits (if fSide (facAt σ 3) then iR else iL) (fIdx (facAt σ 3)) cwid cw D))

/-- The back's cost (THR): four slots ; header ; coefficient words. `Rc`-free. -/
def backThrCost {Atom : Type} (T : Bool → List (CircuitMonomial Atom 1)) (bits : List Bool) (iL iR : Nat)
    (σ : Option Sel) (cwid cw D q L target k K b : Nat) : Nat :=
  fourCostT bits iL iR σ cwid cw D + 1 + (SourceFactorSel.HdrBlock.hdrCost false q L target k D + 1 +
    SourceFactorSel.CoefR.coefRCost cw rhoW K b (rhoOf σ) (fun i => fTerm (facAt σ i.val))
      (fun i => SourceFactorSel.CoefBridge.tco T (facAt σ i.val)))

/-- Port helper: a fixed port is `up` of its value. -/
theorem up_mk_val {t : Nat} (k : Nat) (h : k < NF) : (up (t := t) ⟨k, h⟩).val = k := rfl

theorem up_of {t : Nat} (x : Fin (NF + (19 + 4 * t))) (h : x.val < NF) : x = up ⟨x.val, h⟩ := Fin.ext rfl

end run
end
end NearCubicWires.SourceRequest.SelBack

