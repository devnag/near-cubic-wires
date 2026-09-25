import Proof.Packets.PacketsRowPolyPlan

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent
noncomputable section

/-! ## What the coordinate stage produces -/

/-- SYM: one mask per circuit. -/
def symMasks (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    List (Finset (Fin (symmetricFourfoldOccurrences r).length)) :=
  List.ofFn (fun i : Fin r.circuits.length => symmetricCircuitMask r i)

/-- THR: one mask per residue digit of the selected equation modulo the key's prime. -/
def thrMasks (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (L target : ℕ) (k : RCFive.RowKeys.ThrKey a r L target) :
    List (Finset (Fin (thresholdFourfoldOccurrences r).length)) :=
  List.ofFn (fun digit : Fin (modulusDigitCount k.prime.val) => Finset.univ.filter (fun i =>
    (modularCoefficientResidue (ThresholdRows.equation a r k.selection) k.prime.val i).testBit digit.val))

/-- The mode bit: true for SYM requests. -/
def modeBit : Request → Bool
  | .sym _ _ _ _ => true
  | _ => false

/-! ## The split shape inside `P1` -/

/-- F1's private region split: two handoff tapes and three private sub-regions. -/
structure RowPolyShape {a : DecompositionAlgorithm} (X : WriterShape a) where
  u1 : ℕ
  u2 : ℕ
  u3 : ℕ
  hw1 : X.w1 = 2 + u1 + u2 + u3

namespace RowPolyShape
variable {a : DecompositionAlgorithm} {X : WriterShape a} (Y : RowPolyShape X)

def inQ1 (i : Fin (10 + X.w)) : Prop := 21 ≤ i.val ∧ i.val < 21 + Y.u1
def inQ2 (i : Fin (10 + X.w)) : Prop := 21 + Y.u1 ≤ i.val ∧ i.val < 21 + Y.u1 + Y.u2
def inQ3 (i : Fin (10 + X.w)) : Prop := 21 + Y.u1 + Y.u2 ≤ i.val ∧ i.val < 21 + Y.u1 + Y.u2 + Y.u3

/-- A tape of the split region. -/
def tape (n : ℕ) (h : n < 21) : Fin (10 + X.w) := ⟨n, by unfold WriterShape.w; have := Y.hw1; omega⟩

end RowPolyShape

/-! ## The three stage contracts -/

namespace RowPolySplit

end RowPolySplit

end
end NearCubicWires.PacketsConstruction
