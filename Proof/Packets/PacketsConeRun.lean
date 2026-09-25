import Proof.Packets.PacketsConeDegenerate

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

/-! ## The words -/

theorem labelWord_eq : ∀ {n : ℕ} (f : Fin n → Fin 16),
    (List.ofFn f).flatMap (fun b => SignedSortKey.binary 4 b.val) = Theorem25Completion.WalkPoweredWord.word f
  | 0, _ => rfl
  | n + 1, f => by
    rw [List.ofFn_succ, List.flatMap_cons, labelWord_eq (fun i : Fin n => f i.succ)]
    rfl

theorem labels_eq : ∀ {n : ℕ} (g : Fin n → PoweredMargulisLabel),
    (List.ofFn g).flatMap MaskCoord.labelWord = Theorem25Completion.WalkSampleWord.labelsWord g
  | 0, _ => rfl
  | n + 1, g => by
    rw [List.ofFn_succ, List.flatMap_cons, labels_eq (fun i : Fin n => g i.succ)]
    unfold MaskCoord.labelWord
    rw [labelWord_eq]
    rfl

section Family
variable {q : ℕ} (occ : List (SupportedNormalizedGate q)) (I : Finset (Fin q)) (den : ℕ)

theorem vertex_zero (sample : LiveRows.Seed occ I den) :
    Theorem25Completion.WalkTimeLoop.vertex sample 0 = sample.start := by
  unfold Theorem25Completion.WalkTimeLoop.vertex
  have h : (⟨min 0 (2 * Nat.clog 2 (den + 1)), by omega⟩ : Fin (2 * Nat.clog 2 (den + 1) + 1)) = ⟨0, by omega⟩ :=
    Fin.ext (Nat.zero_min _)
  rw [h, MargulisWalkSample.vertex.eq_def]

theorem startX_eq (sample : LiveRows.Seed occ I den) :
    MaskCoord.startX occ I den sample = Theorem25Completion.WalkLiteralProduced.coordinate
      (canonicalGradedRank occ.length (LiveRows.bound occ I)) (Theorem25Completion.WalkTimeLoop.vertex sample 0).1 := by
  rw [vertex_zero]
  rfl

theorem startY_eq (sample : LiveRows.Seed occ I den) :
    MaskCoord.startY occ I den sample = Theorem25Completion.WalkLiteralProduced.coordinate
      (canonicalGradedRank occ.length (LiveRows.bound occ I)) (Theorem25Completion.WalkTimeLoop.vertex sample 0).2 := by
  rw [vertex_zero]
  rfl

theorem labelsWord_eq (sample : LiveRows.Seed occ I den) :
    MaskCoord.labelsWord occ I den sample =
      Theorem25Completion.WalkSampleWord.labelsWord (sampleTransitionLabels sample) := by
  unfold MaskCoord.labelsWord
  rw [← labels_eq]
  rfl

/-- **The external output IS the kit vector of mask `M`'s coordinates.** -/
theorem vector_eq (C w : ℕ) (M : Finset (Fin occ.length)) (sample : LiveRows.Seed occ I den) :
    PacketVector.bank (Theorem25Completion.WalkLiteralProducedMajority.R C w)
      (List.ofFn (fun column : Fin (occ.length + 1) =>
        (Normalized.structuralMaskedWalkListCoordinate M (canonicalGradedLabel occ.length (LiveRows.bound occ I))
          (executableGradedWindow (depth := canonicalGradedDepth (LiveRows.bound occ I)) (LiveRows.bound occ I))
          0 sample column).map (NormalizedFiniteTransport.maskNat C))) =
      PolyKit.vector C w (MaskCoord.maskCoords occ I den M sample) := by
  unfold PolyKit.vector
  rw [MaskCoord.coords_eq, List.map_ofFn]
  rfl

def input (C w : ℕ) (M : Finset (Fin occ.length)) (sample : LiveRows.Seed occ I den) : Fin 742 → List Bool :=
  Theorem25Completion.WalkLiteralProducedMajority.input C w (ConeWindow.root (LiveRows.bound occ I)) occ.length
    (LiveRows.bound occ I) (2 * Nat.clog 2 (den + 1)) (MaskCoord.maskBits occ M) (MaskCoord.startX occ I den sample)
    (MaskCoord.startY occ I den sample) (MaskCoord.labelsWord occ I den sample)

def budget (C w : ℕ) (M : Finset (Fin occ.length)) : ℕ :=
  Theorem25Completion.WalkLiteralProducedMajority.budget C w (ConeWindow.root (LiveRows.bound occ I)) occ.length
    (LiveRows.bound occ I) (canonicalGradedDepth (LiveRows.bound occ I)) (2 * Nat.clog 2 (den + 1))
    (MaskCoord.maskBits occ M)

theorem input_eq (C w : ℕ) (M : Finset (Fin occ.length)) (sample : LiveRows.Seed occ I den) :
    input occ I den C w M sample =
      Theorem25Completion.WalkLiteralProducedMajority.input C w (ConeWindow.root (LiveRows.bound occ I)) occ.length
        (LiveRows.bound occ I) (2 * Nat.clog 2 (den + 1)) (List.ofFn (fun i => decide (i ∈ M)))
        (Theorem25Completion.WalkLiteralProduced.coordinate (canonicalGradedRank occ.length (LiveRows.bound occ I))
          (Theorem25Completion.WalkTimeLoop.vertex sample 0).1)
        (Theorem25Completion.WalkLiteralProduced.coordinate (canonicalGradedRank occ.length (LiveRows.bound occ I))
          (Theorem25Completion.WalkTimeLoop.vertex sample 0).2)
        (Theorem25Completion.WalkSampleWord.labelsWord (sampleTransitionLabels sample) ++ []) := by
  rw [List.append_nil, ← startX_eq, ← startY_eq, ← labelsWord_eq]
  rfl

theorem family_run (C w : ℕ) (M : Finset (Fin occ.length)) (sample : LiveRows.Seed occ I den)
    (h : Theorem25Completion.WalkLiteralLoop.Bounds C w (rawDeg occ I) occ.length (LiveRows.bound occ I)
      (canonicalGradedDepth (LiveRows.bound occ I)) (ConeWindow.root (LiveRows.bound occ I))
      (Theorem25Completion.WalkLiteralProducedMajority.S C w) (Theorem25Completion.WalkLiteralProducedMajority.R C w)
      (executableGradedWindow (depth := canonicalGradedDepth (LiveRows.bound occ I)) (LiveRows.bound occ I)))
    (hfit : (occ.length + 1) ^ (rawDeg occ I * canonicalWalkLength den) ≤ 2 ^ w)
    (hVisits : canonicalWalkLength den ≤ 2 ^ w) (hCodes : 2 ^ canonicalWalkLength den ≤ 2 ^ w) :
    ∃ (H : Fin 742 → ℕ) (A : Fin 742 → List Bool),
      Step Theorem25Completion.WalkLiteralProducedMajority.machine (budget occ I den C w M) (fun _ => 0)
        (input occ I den C w M sample) H A ∧
      A 704 = PolyKit.vector C w (MaskCoord.maskCoords occ I den M sample) := by
  have hrun := Theorem25Completion.WalkLiteralProducedMajority.all_run (population := occ.length)
    (active := LiveRows.bound occ I) (depth := canonicalGradedDepth (LiveRows.bound occ I))
    (n := 2 * Nat.clog 2 (den + 1)) C w (rawDeg occ I) (ConeWindow.root (LiveRows.bound occ I)) M
    (executableGradedWindow (depth := canonicalGradedDepth (LiveRows.bound occ I)) (LiveRows.bound occ I))
    h rfl sample hfit hVisits hCodes []
  obtain ⟨H, A, hs, ho⟩ := hrun
  refine ⟨H, A, ?_, ?_⟩
  · rw [input_eq]
    exact hs
  · rw [ho]
    exact vector_eq occ I den C w M sample

end Family

end
end NearCubicWires.PacketsConstruction.ConeRun
