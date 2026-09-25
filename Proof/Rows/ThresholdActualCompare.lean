import Proof.Rows.ThresholdCompare

/-! The concrete native-flag and selected-TOP coefficient words are consumed
by one ordinary modular comparator with the exact LiveRows verdict. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
namespace PCJ45bee56da9f34d5a_ThresholdActualCompare
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.RepairSource.VerifierDecoding SignedSortKey
open PCJ9eff70d512234a4c_Fixed
open PCJ45bee56da9f34d5a_ExpandedThresholdStream
open PCJ45bee56da9f34d5a_ThresholdCompare
noncomputable section

def coefficients (a :DecompositionAlgorithm) (r :FourfoldRequest NormalizedThresholdThresholdCircuit)
 (four :r.circuits.length ≤ 4) (sel :ThresholdRows.Selection a r) (p w o :Nat):=
 PCJ45bee56da9f34d5a_FourfoldPowerData.stream (PCJ45bee56da9f34d5a_ThresholdData.data a r four sel)
  (PCJ45bee56da9f34d5a_ThresholdData.base a r four sel) p w 4++frame (binary w ((p-o)%p))

theorem run (a :DecompositionAlgorithm) (r :FourfoldRequest NormalizedThresholdThresholdCircuit)
 (four :r.circuits.length ≤ 4) (sel :ThresholdRows.Selection a r) (I :Finset (Fin r.q)) (x :BitInput r.q)
 {cutoff :Nat} (prime :PrimeIndex cutoff) (o :Fin prime.val) (w cap :Nat)
 (hpw :2*prime.val ≤ 2^w) (hcap :2*w+2 ≤ cap):
 let bits:=occurrenceResidualConstant (thresholdFourfoldOccurrences r) I x
 let Q:=(terms a r sel bits).length+1
 let gs:=PCJ45bee56da9f34d5a_NativeFlags.word (PCJ45bee56da9f34d5a_NativeFlagsMeaning.circuits r) I x
 let cs:=coefficients a r four sel prime.val w o.val
 let s:=state prime.val w (equation a r sel bits o.val) (input a r sel bits)
 Step FinalPrimeThresholdRow.whole (FinalPrimeThresholdRow.rowFuel w Q) startHeads
  (bank prime.val w cap Q gs cs (binary w 0) (binary w 0) false false)
  (finalHeads w Q)
  (bank prime.val w cap Q gs cs (FinalPrimeRow.residueWord s) s.2.1 s.2.2
   (decide (LiveRows.modularOffset (thresholdFourfoldOccurrences r) I x
    (ThresholdRows.equation a r sel) prime.val=o.val))) :=by
 dsimp only
 rw [PCJ45bee56da9f34d5a_ThresholdStreams.flags a r sel I x]
 unfold coefficients
 rw [PCJ45bee56da9f34d5a_ThresholdStreams.full_coefficients a r sel
  (occurrenceResidualConstant (thresholdFourfoldOccurrences r) I x) four prime.val w o.val
  (mem_primesUpTo.mp prime.property).1.pos o.isLt]
 rw [←modularOffset_consumer a r sel I x prime o]
 exact PCJ45bee56da9f34d5a_ThresholdCompare.run prime w cap _ _ hpw hcap
end
end PCJ45bee56da9f34d5a_ThresholdActualCompare
