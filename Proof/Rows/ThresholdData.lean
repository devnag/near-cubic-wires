import Proof.Rows.FourfoldPowerMeaning
import Proof.Rows.NativeFlagsMeaning

/-! One actual THR request supplies the same selected children to canonical
base construction and to physical coefficient production. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
namespace PCJ45bee56da9f34d5a_ThresholdData
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding SignedSortKey
open PCJ9eff70d512234a4c_Fixed
open PCJ45bee56da9f34d5a_FourfoldBaseData (Data)
noncomputable section

def data (a :DecompositionAlgorithm) (r :FourfoldRequest NormalizedThresholdThresholdCircuit)
 (four :r.circuits.length ≤ 4) (sel :ThresholdRows.Selection a r):Data where
 count:=r.circuits.length
 arity i:=(r.circuits.get i).top.support.card
 gates i:=ThresholdRows.children a (r.circuits.get i)
 selected:=sel
 count_le:=four

def base (a :DecompositionAlgorithm) (r :FourfoldRequest NormalizedThresholdThresholdCircuit)
 (four :r.circuits.length ≤ 4) (sel :ThresholdRows.Selection a r):Nat:=
 1+(data a r four sel).values.sum

theorem base_eq (a :DecompositionAlgorithm) (r :FourfoldRequest NormalizedThresholdThresholdCircuit)
 (four :r.circuits.length ≤ 4) (sel :ThresholdRows.Selection a r):
 (base a r four sel :Int)=equationListBase (ThresholdRows.equations a r sel) :=by
 rw [CloseoutRowsModeThresholdSparse.canonical_base]
 simp only [base,Data.values,data,List.sum_ofFn,Nat.add_comm]

theorem coefficients (a :DecompositionAlgorithm) (r :FourfoldRequest NormalizedThresholdThresholdCircuit)
 (four :r.circuits.length ≤ 4) (sel :ThresholdRows.Selection a r)
 (bits :Fin (thresholdFourfoldOccurrences r).length→Bool) (p w :Nat) (hp :0<p):
 PCJ45bee56da9f34d5a_FourfoldPowerData.stream (data a r four sel) (base a r four sel) p w 4=
 (PCJ45bee56da9f34d5a_ExpandedThresholdStream.terms a r sel bits).flatMap
  (fun t=>frame (binary w (FinalPrimeReduce.intResidue p t.1))) :=by
 rw [PCJ45bee56da9f34d5a_FourfoldPowerMeaning.blocks (data a r four sel) (base a r four sel) p w
  (fun i j=>bits (thresholdCircuitEmbedding r i j)) hp]
 rw [base_eq]
 rfl
end
end PCJ45bee56da9f34d5a_ThresholdData
