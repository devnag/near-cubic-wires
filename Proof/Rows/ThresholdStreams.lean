import Proof.Rows.ThresholdData
import Proof.Rows.OffsetEmitter
import Proof.Rows.FinalNativeResidueEquation

/-! The two physically produced streams have exactly the comparator codec,
including the per-circuit target flags and unscaled final negative offset. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
namespace PCJ45bee56da9f34d5a_ThresholdStreams
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding SignedSortKey
open PCJ9eff70d512234a4c_Fixed
open PCJ45bee56da9f34d5a_ExpandedThresholdStream
noncomputable section

theorem neg_offset (p o :Nat) (hp :0<p) (ho :o<p):
 (p-o)%p=FinalPrimeReduce.intResidue p (-(o :Int)) :=by
 simpa [Nat.mod_eq_of_lt ho] using C10NativeResidueInput.signed_residue p o true hp

variable (a :DecompositionAlgorithm) (r :FourfoldRequest NormalizedThresholdThresholdCircuit)
 (sel :ThresholdRows.Selection a r) (bits :Fin (thresholdFourfoldOccurrences r).length→Bool)

theorem weights_list (o :Nat):
 C10NativeResidueEquation.weights (equation a r sel bits o)=(terms a r sel bits).map Prod.fst :=by
 have h :List.ofFn (fun i :Fin (terms a r sel bits).length=>(terms a r sel bits).get i)=terms a r sel bits:=by
  simpa only [List.get_eq_getElem] using (List.ofFn_getElem (xs:=terms a r sel bits))
 simpa only [C10NativeResidueEquation.weights,equation,List.map_ofFn,Function.comp_def] using congrArg (List.map Prod.fst) h

theorem weight_blocks (p w o :Nat):
 (terms a r sel bits).flatMap (fun t=>frame (binary w (FinalPrimeReduce.intResidue p t.1)))=
 FinalPrimeModular.blocks (FinalPrimeReduce.reducedWord p w (equation a r sel bits o)) 0
  (terms a r sel bits).length :=by
 rw [←C10NativeResidueEquation.weight_blocks]
 rw [weights_list]
 have h:=C10NativeResidueWeights.concatenated p w
  (C10NativeResidueEquation.weights (equation a r sel bits o))
 rw [weights_list,List.length_map,List.flatMap_map] at h
 exact h.symm

theorem full_coefficients (four :r.circuits.length ≤ 4) (p w o :Nat) (hp :0<p) (ho :o<p):
 PCJ45bee56da9f34d5a_FourfoldPowerData.stream (PCJ45bee56da9f34d5a_ThresholdData.data a r four sel)
  (PCJ45bee56da9f34d5a_ThresholdData.base a r four sel) p w 4++frame (binary w ((p-o)%p))=
 FinalPrimeModular.blocks (FinalPrimeReduce.reducedWord p w (equation a r sel bits o)) 0
  ((terms a r sel bits).length+1) :=by
 rw [PCJ45bee56da9f34d5a_ThresholdData.coefficients a r four sel bits p w hp,
  weight_blocks a r sel bits p w o,neg_offset p o hp ho]
 have hlast:binary w (FinalPrimeReduce.intResidue p (-(o :Int)))=
  FinalPrimeReduce.reducedWord p w (equation a r sel bits o) (terms a r sel bits).length:=by
   rw [FinalPrimeReduce.reducedWord,FinalPrimeReduce.coeffInt_last]
   rfl
 rw [hlast,C10NativeResidueAppend.blocks_snoc]

theorem flags (I :Finset (Fin r.q)) (x :BitInput r.q):
 PCJ45bee56da9f34d5a_NativeFlags.word (PCJ45bee56da9f34d5a_NativeFlagsMeaning.circuits r) I x=
 FinalPrimeReduce.gateList (input a r sel (occurrenceResidualConstant (thresholdFourfoldOccurrences r) I x)) :=by
 rw [PCJ45bee56da9f34d5a_NativeFlagsMeaning.word_eq a r sel]
 unfold FinalPrimeReduce.gateList input
 congr 1
 have h :List.ofFn (fun i :Fin (terms a r sel (occurrenceResidualConstant (thresholdFourfoldOccurrences r) I x)).length=>
  (terms a r sel (occurrenceResidualConstant (thresholdFourfoldOccurrences r) I x)).get i)=
  terms a r sel (occurrenceResidualConstant (thresholdFourfoldOccurrences r) I x):=by
   simpa only [List.get_eq_getElem] using (List.ofFn_getElem
    (xs:=terms a r sel (occurrenceResidualConstant (thresholdFourfoldOccurrences r) I x)))
 simpa only [List.map_ofFn,Function.comp_def] using (congrArg (List.map Prod.snd) h).symm
end
end PCJ45bee56da9f34d5a_ThresholdStreams
