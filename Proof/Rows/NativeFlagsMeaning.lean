import Proof.Rows.NativeFlags
import Proof.Rows.ExpandedThresholdStream

/-! The actual original-native traversal emits exactly the flags consumed by
the expanded canonical equation, including child targets and final offset. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
namespace PCJ45bee56da9f34d5a_NativeFlagsMeaning
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open PCJ9eff70d512234a4c_Fixed
open PCJ45bee56da9f34d5a_NativeCircuitCodec
open PCJ45bee56da9f34d5a_ExpandedThresholdStream
noncomputable section

def circuits (r : FourfoldRequest NormalizedThresholdThresholdCircuit) :=
 r.circuits.map (fun c=>(thrGates c,thrTop c))

theorem native_stream (r : FourfoldRequest NormalizedThresholdThresholdCircuit) :
 PCJ45bee56da9f34d5a_NativeFlagsLoop.stream (circuits r)=
 r.circuits.flatMap (fun c=>frame (PCJd4d1d9d7d1fa4313_Production.thrWord c)) :=by
 simp only [PCJ45bee56da9f34d5a_NativeFlagsLoop.stream,circuits,List.flatMap_map,
  PCJ45bee56da9f34d5a_NativeFlagsLoop.word,thrWord_eq]

theorem flag_terms (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
 (sel : ThresholdRows.Selection a r) (I : Finset (Fin r.q)) (x : BitInput r.q) :
 (terms a r sel (occurrenceResidualConstant (thresholdFourfoldOccurrences r) I x)).map Prod.snd=
 r.circuits.flatMap (fun c=>PCJ45bee56da9f34d5a_NativeCircuitFlags.flags (thrGates c) I x) :=by
 have hc : (List.ofFn (fun i : Fin r.circuits.length=>i)).map (fun i=>r.circuits.get i)=r.circuits :=by
  simp only [List.map_ofFn,Function.comp_def,List.get_eq_getElem,List.ofFn_getElem]
 rw [terms,List.map_flatMap]
 calc
  _ = (List.ofFn (fun i : Fin r.circuits.length=>i)).flatMap
    (fun i=>PCJ45bee56da9f34d5a_NativeCircuitFlags.flags (thrGates (r.circuits.get i)) I x) :=by
     apply List.flatMap_congr
     intro i _
     simp only [block,List.map_append,List.map_ofFn,List.map_cons,List.map_nil,Function.comp_def,
      PCJ45bee56da9f34d5a_NativeCircuitFlags.flags,thrGates,List.map_ofFn,
      occurrenceResidualConstant,thresholdCircuitEmbedding_get]
  _ = _ :=by
   simpa only [List.flatMap_map] using congrArg
    (fun cs=>cs.flatMap (fun c=>PCJ45bee56da9f34d5a_NativeCircuitFlags.flags (thrGates c) I x)) hc

theorem word_eq (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
 (sel : ThresholdRows.Selection a r) (I : Finset (Fin r.q)) (x : BitInput r.q) :
 PCJ45bee56da9f34d5a_NativeFlags.word (circuits r) I x=
 (terms a r sel (occurrenceResidualConstant (thresholdFourfoldOccurrences r) I x)).map Prod.snd++[true] :=by
 rw [flag_terms]
 simp only [PCJ45bee56da9f34d5a_NativeFlags.word,PCJ45bee56da9f34d5a_NativeFlagsLoop.output,List.take_length,
  circuits,List.flatMap_map]

end
end PCJ45bee56da9f34d5a_NativeFlagsMeaning
