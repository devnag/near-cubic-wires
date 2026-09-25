import Proof.Packets.PacketsConeRun

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.ConeRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces NearCubicWires.SupplierWalk
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.SupplierListSchedule
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore PCJ9eff70d512234a4c_Fixed.Materializer
noncomputable section

/-! ## Per request, key and mask -/

variable (a : DecompositionAlgorithm)

/-- The external budget at mask `j` of key `k`. -/
def budgetOf (K : KitShape a) : ∀ r : Request, rcKey a r → ℕ → ℕ
  | .terminal, k, _ => PEmpty.elim k
  | .sym r _ L target, _, j =>
      budget (symmetricFourfoldOccurrences r) (CyclicChoice.live (symmetricFourfoldOccurrences r) L)
        (symmetricListDenominator r target) (K.C (.sym r ‹_› L target)) (K.w (.sym r ‹_› L target))
        ((PacketsConstruction.symMasks r).getD j ∅)
  | .thr r _ L target, k, j =>
      budget (thresholdFourfoldOccurrences r) (CyclicChoice.live (thresholdFourfoldOccurrences r) L)
        (CloseoutFinalC10ThresholdRows.listDenominator a r target) (K.C (.thr r ‹_› L target))
        (K.w (.thr r ‹_› L target)) ((PacketsConstruction.thrMasks a r L target k).getD j ∅)

theorem request_run_sym (K : KitShape a) (hA : ConeBounds.RouteA a K)
    (r0 : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r0.circuits.length ≤ 4) (L target : ℕ)
    (k : RCFive.RowKeys.SymKey r0 L target) (hk : k ∈ rcKeys a (.sym r0 four L target))
    (hkey : ConeBounds.Keyed a (.sym r0 four L target)) (j : ℕ)
    (hj' : j < (PacketsConstruction.symMasks r0).length) :
    ∃ (H : Fin 742 → ℕ) (A : Fin 742 → List Bool),
      Step Theorem25Completion.WalkLiteralProducedMajority.machine
        (budget (symmetricFourfoldOccurrences r0) (CyclicChoice.live (symmetricFourfoldOccurrences r0) L)
          (symmetricListDenominator r0 target) (K.C (.sym r0 four L target)) (K.w (.sym r0 four L target))
          ((PacketsConstruction.symMasks r0)[j]'hj')) (fun _ => 0)
        (input (symmetricFourfoldOccurrences r0) (CyclicChoice.live (symmetricFourfoldOccurrences r0) L)
          (symmetricListDenominator r0 target) (K.C (.sym r0 four L target)) (K.w (.sym r0 four L target))
          ((PacketsConstruction.symMasks r0)[j]'hj') k.seed) H A ∧
      A 704 = PolyKit.vector (K.C (.sym r0 four L target)) (K.w (.sym r0 four L target))
        (MaskCoord.maskCoords (symmetricFourfoldOccurrences r0) (CyclicChoice.live (symmetricFourfoldOccurrences r0) L)
          (symmetricListDenominator r0 target) ((PacketsConstruction.symMasks r0)[j]'hj') k.seed) := by
  have hb := (ConeBounds.fit a K hA (.sym r0 four L target) k hk hkey).1
  have hfit := (ConeBounds.fit a K hA (.sym r0 four L target) k hk hkey).2.1
  have hvis := (ConeBounds.fit a K hA (.sym r0 four L target) k hk hkey).2.2.1
  have hcod := (ConeBounds.fit a K hA (.sym r0 four L target) k hk hkey).2.2.2
  exact family_run (symmetricFourfoldOccurrences r0) (CyclicChoice.live (symmetricFourfoldOccurrences r0) L)
    (symmetricListDenominator r0 target) (K.C (.sym r0 four L target)) (K.w (.sym r0 four L target))
    ((PacketsConstruction.symMasks r0)[j]'hj') k.seed hb hfit hvis hcod

theorem request_run_thr (K : KitShape a) (hA : ConeBounds.RouteA a K)
    (r0 : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r0.circuits.length ≤ 4) (L target : ℕ)
    (k : RCFive.RowKeys.ThrKey a r0 L target) (hk : k ∈ rcKeys a (.thr r0 four L target))
    (hkey : ConeBounds.Keyed a (.thr r0 four L target)) (j : ℕ)
    (hj' : j < (PacketsConstruction.thrMasks a r0 L target k).length) :
    ∃ (H : Fin 742 → ℕ) (A : Fin 742 → List Bool),
      Step Theorem25Completion.WalkLiteralProducedMajority.machine
        (budget (thresholdFourfoldOccurrences r0) (CyclicChoice.live (thresholdFourfoldOccurrences r0) L)
          (CloseoutFinalC10ThresholdRows.listDenominator a r0 target) (K.C (.thr r0 four L target))
          (K.w (.thr r0 four L target)) ((PacketsConstruction.thrMasks a r0 L target k)[j]'hj')) (fun _ => 0)
        (input (thresholdFourfoldOccurrences r0) (CyclicChoice.live (thresholdFourfoldOccurrences r0) L)
          (CloseoutFinalC10ThresholdRows.listDenominator a r0 target) (K.C (.thr r0 four L target))
          (K.w (.thr r0 four L target)) ((PacketsConstruction.thrMasks a r0 L target k)[j]'hj') k.seed) H A ∧
      A 704 = PolyKit.vector (K.C (.thr r0 four L target)) (K.w (.thr r0 four L target))
        (MaskCoord.maskCoords (thresholdFourfoldOccurrences r0)
          (CyclicChoice.live (thresholdFourfoldOccurrences r0) L)
          (CloseoutFinalC10ThresholdRows.listDenominator a r0 target)
          ((PacketsConstruction.thrMasks a r0 L target k)[j]'hj') k.seed) := by
  have hb := (ConeBounds.fit a K hA (.thr r0 four L target) k hk hkey).1
  have hfit := (ConeBounds.fit a K hA (.thr r0 four L target) k hk hkey).2.1
  have hvis := (ConeBounds.fit a K hA (.thr r0 four L target) k hk hkey).2.2.1
  have hcod := (ConeBounds.fit a K hA (.thr r0 four L target) k hk hkey).2.2.2
  exact family_run (thresholdFourfoldOccurrences r0) (CyclicChoice.live (thresholdFourfoldOccurrences r0) L)
    (CloseoutFinalC10ThresholdRows.listDenominator a r0 target) (K.C (.thr r0 four L target))
    (K.w (.thr r0 four L target)) ((PacketsConstruction.thrMasks a r0 L target k)[j]'hj') k.seed hb hfit hvis hcod

end
end NearCubicWires.PacketsConstruction.ConeRun
