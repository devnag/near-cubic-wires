import Proof.Packets.PacketsCoordLoop

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.Residual
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.SupplierListSchedule
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore PCJ9eff70d512234a4c_Fixed.Materializer
noncomputable section

/-- **Family level, keyed**: mask `M`'s kit vector has `pop + 1` entries of `2·R` cells each. -/
theorem coords_vector_length {q : ℕ} (occ : List (SupportedNormalizedGate q)) (I : Finset (Fin q)) (den C w : ℕ)
    (M : Finset (Fin occ.length)) (sample : LiveRows.Seed occ I den)
    (h : Theorem25Completion.WalkLiteralLoop.Bounds C w (rawDeg occ I) occ.length (LiveRows.bound occ I)
      (canonicalGradedDepth (LiveRows.bound occ I)) (ConeWindow.root (LiveRows.bound occ I))
      (Theorem25Completion.WalkLiteralProducedMajority.S C w) (Theorem25Completion.WalkLiteralProducedMajority.R C w)
      (executableGradedWindow (depth := canonicalGradedDepth (LiveRows.bound occ I)) (LiveRows.bound occ I)))
    (hfit : (occ.length + 1) ^ (rawDeg occ I * canonicalWalkLength den) ≤ 2 ^ w) :
    (PolyKit.vector C w (MaskCoord.maskCoords occ I den M sample)).length =
      (occ.length + 1) * (2 * PolyKit.reserve C w) := by
  unfold PolyKit.vector
  have hfits : ∀ P ∈ (MaskCoord.maskCoords occ I den M sample).map (PolyKit.masks C),
      PacketVector.Fits (PolyKit.reserve C w) P := by
    intro P hP
    rw [MaskCoord.coords_eq, List.map_ofFn, List.mem_ofFn] at hP
    obtain ⟨column, rfl⟩ := hP
    exact Theorem25Completion.WalkTranscriptColumn.majority_fits (n := 2 * Nat.clog 2 (den + 1)) C w (rawDeg occ I)
      _ _ _ M _ h sample column hfit
  rw [PacketVector.bank_length _ _ hfits, List.length_map, MaskCoord.maskCoords, List.length_ofFn]
  ring

/-- The terminal vector's length. -/
theorem terminal_length (C w pop : ℕ) :
    (PolyKit.vector C w (ConeDegenerate.terminalVec pop)).length = (pop + 1) * (2 * PolyKit.reserve C w) := by
  have hR := ConeBounds.reserve_ge C w
  have hC : C ≤ PolyKit.reserve C w := by unfold PolyKit.reserve; omega
  have hR1 : 1 ≤ PolyKit.reserve C w := by unfold PolyKit.reserve; omega
  have hR2 : 2 ≤ PolyKit.reserve C w := by unfold PolyKit.reserve; omega
  rw [ConeDegenerate.vector_terminal C w pop hC hR1]
  simp only [List.length_append, List.length_replicate, List.length_cons]
  rw [Nat.add_mul, Nat.one_mul]
  omega

variable (a : DecompositionAlgorithm)

theorem vec_length_sym (K : KitShape a) (hA : ConeBounds.RouteA a K)
    (r0 : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r0.circuits.length ≤ 4) (L target : ℕ)
    (k : RCFive.RowKeys.SymKey r0 L target) (hk : k ∈ rcKeys a (.sym r0 four L target))
    (hkey : ConeBounds.Keyed a (.sym r0 four L target)) (j : ℕ)
    (hj' : j < (PacketsConstruction.symMasks r0).length) :
    (vecOf a K (.sym r0 four L target) k j).length =
      ((Request.sym r0 four L target).family a).occurrences.length.succ *
        (2 * PolyKit.reserve (K.C (.sym r0 four L target)) (K.w (.sym r0 four L target))) := by
  have hb := (ConeBounds.fit a K hA (.sym r0 four L target) k hk hkey).1
  have hfit := (ConeBounds.fit a K hA (.sym r0 four L target) k hk hkey).2.1
  have e : (MaskCoord.maskCoordsList a (.sym r0 four L target) k).getD j [] =
      MaskCoord.maskCoords (symmetricFourfoldOccurrences r0) (CyclicChoice.live (symmetricFourfoldOccurrences r0) L)
        (symmetricListDenominator r0 target) ((PacketsConstruction.symMasks r0)[j]'hj') k.seed :=
    getD_map_lt _ _ _ _ hj'
  unfold vecOf
  rw [e]
  exact coords_vector_length (symmetricFourfoldOccurrences r0) (CyclicChoice.live (symmetricFourfoldOccurrences r0) L)
    (symmetricListDenominator r0 target) (K.C (.sym r0 four L target)) (K.w (.sym r0 four L target))
    ((PacketsConstruction.symMasks r0)[j]'hj') k.seed hb hfit

theorem vec_length_thr (K : KitShape a) (hA : ConeBounds.RouteA a K)
    (r0 : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r0.circuits.length ≤ 4) (L target : ℕ)
    (k : RCFive.RowKeys.ThrKey a r0 L target) (hk : k ∈ rcKeys a (.thr r0 four L target))
    (hkey : ConeBounds.Keyed a (.thr r0 four L target)) (j : ℕ)
    (hj' : j < (PacketsConstruction.thrMasks a r0 L target k).length) :
    (vecOf a K (.thr r0 four L target) k j).length =
      ((Request.thr r0 four L target).family a).occurrences.length.succ *
        (2 * PolyKit.reserve (K.C (.thr r0 four L target)) (K.w (.thr r0 four L target))) := by
  have hb := (ConeBounds.fit a K hA (.thr r0 four L target) k hk hkey).1
  have hfit := (ConeBounds.fit a K hA (.thr r0 four L target) k hk hkey).2.1
  have e : (MaskCoord.maskCoordsList a (.thr r0 four L target) k).getD j [] =
      MaskCoord.maskCoords (thresholdFourfoldOccurrences r0) (CyclicChoice.live (thresholdFourfoldOccurrences r0) L)
        (CloseoutFinalC10ThresholdRows.listDenominator a r0 target)
        ((PacketsConstruction.thrMasks a r0 L target k)[j]'hj') k.seed :=
    getD_map_lt _ _ _ _ hj'
  unfold vecOf
  rw [e]
  exact coords_vector_length (thresholdFourfoldOccurrences r0) (CyclicChoice.live (thresholdFourfoldOccurrences r0) L)
    (CloseoutFinalC10ThresholdRows.listDenominator a r0 target) (K.C (.thr r0 four L target))
    (K.w (.thr r0 four L target)) ((PacketsConstruction.thrMasks a r0 L target k)[j]'hj') k.seed hb hfit

theorem vec_length (K : KitShape a) (hA : ConeBounds.RouteA a K) (r : Request) (k : rcKey a r)
    (hk : k ∈ rcKeys a r) (j : ℕ) (hj : j < maskCount a r k) :
    (vecOf a K r k j).length = ((r.family a).occurrences.length + 1) *
      (2 * Theorem25Completion.CycleBounds.commonReserve (K.C r) (K.w r)) := by
  rcases Nat.eq_zero_or_pos (Bof a r) with hB | hB
  · have e : (MaskCoord.maskCoordsList a r k).getD j [] = ConeDegenerate.terminalVec (r.family a).occurrences.length := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
      exact ConeDegenerate.maskCoords_of_bound_zero a r k hB j hj
    unfold vecOf
    rw [e]
    exact terminal_length _ _ _
  · have hkey := ConeDegenerate.keyed_of_bound_pos a r hB
    cases r with
    | terminal => exact PEmpty.elim k
    | sym r0 four L target =>
      have e : maskCount a (.sym r0 four L target) k = (PacketsConstruction.symMasks r0).length := List.length_map _
      exact vec_length_sym a K hA r0 four L target k hk hkey j (e ▸ hj)
    | thr r0 four L target =>
      have e : maskCount a (.thr r0 four L target) k = (PacketsConstruction.thrMasks a r0 L target k).length :=
        List.length_map _
      exact vec_length_thr a K hA r0 four L target k hk hkey j (e ▸ hj)

/-- **The mask count is small**: SYM at most four circuits, THR below `2^walkLength ≤ smallSize`. -/
theorem maskCount_le (r : Request) (k : rcKey a r) : maskCount a r k ≤ r.smallSize a + 4 := by
  cases r with
  | terminal => exact PEmpty.elim k
  | sym r0 four L target =>
    have e : maskCount a (.sym r0 four L target) k = r0.circuits.length := by
      unfold maskCount MaskCoord.maskCoordsList PacketsConstruction.symMasks
      rw [List.length_map, List.length_ofFn]
    omega
  | thr r0 four L target =>
    have e : maskCount a (.thr r0 four L target) k = modulusDigitCount k.prime.val := by
      unfold maskCount MaskCoord.maskCoordsList PacketsConstruction.thrMasks
      rw [List.length_map, List.length_ofFn]
    have h1 := thr_digits_lt a r0 L target k
    have h2 := small_walk a (.thr r0 four L target)
    have h3 : canonicalWalkLength ((Request.thr r0 four L target).denominator a) =
        canonicalWalkLength (CloseoutFinalC10ThresholdRows.listDenominator a r0 target) := rfl
    rw [h3] at h2
    omega

end
end NearCubicWires.PacketsConstruction.Residual
