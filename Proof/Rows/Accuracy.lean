import Proof.Rows.Rows
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false
open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.BoundedNormalizedSupplier
open NearCubicWires.CanonicalBinary
open NearCubicWires.CompilerSemantics
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierAsymptotics
open NearCubicWires.SupplierCapacity
open NearCubicWires.SupplierListPolynomial
open NearCubicWires.SupplierListSchedule
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime
open NearCubicWires.SupplierPrinter
open NearCubicWires.SupplierRadix
open NearCubicWires.SupplierTouching
open NearCubicWires.SupplierToeplitz
open NearCubicWires.SupplierToeplitzCore
open NearCubicWires.SupplierWalk
open NearCubicWires.SupplierWalkBridge
open NearCubicWires.SupplierWindow
open NearCubicWires.ThresholdAlignedEnvelope
open NearCubicWires.ThresholdCompiler

open NearCubicWires.SupplierEstimator
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.CanonicalFourfoldRowProgram
open PCJ9eff70d512234a4c_Fixed
namespace PCJa94fb905a93646cd.Chosen
noncomputable section
open CloseoutFinalC10ThresholdRows C10ThresholdNaturalSum
section Threshold
variable (a : DecompositionAlgorithm)
  (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
def nativeNumerator (liveScale listDen cutoff : ℕ) : ℕ :=
  ∑ sel : ThresholdRows.Selection a r, ∑ prime : PrimeIndex cutoff,
    ∑ seed : NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale listDen,
      ∑ input : BitInput r.q,
        (selectionRow a r liveScale listDen input
          sel prime seed).toNat

def nativeDenominator (liveScale listDen cutoff : ℕ) : ℕ :=
  Fintype.card (PrimeIndex cutoff) *
    Fintype.card (NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale listDen) *
      2 ^ r.q

theorem selection_mismatch_le (spectrum : ExpanderSpectrumContract)
    (theta : PrimeThetaBoundContract) (liveScale target : ℕ) (input : BitInput r.q)
    (sel : ThresholdRows.Selection a r) :
    booleanMean
      (fun sample : PrimeIndex (primeCutoff a r target) ×
          NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale
            (listDenominator a r target) =>
        selectionRow a r liveScale (listDenominator a r target) input sel sample.1 sample.2 !=
          exactRow a r sel input) ≤
      1 / (primeDenominator a r target + 1 : ℕ) +
        1 / (primeDenominator a r target + 1 : ℕ) := by
  have hp := (certificate theta a r target).cardPositive
  have he := (normalizedOccurrenceListCertificate spectrum (thresholdFourfoldOccurrences r)
    liveScale (listDenominator a r target)).cardPositive
  let actual : Fin (thresholdFourfoldOccurrences r).length → Bool :=
    fun index => ((thresholdFourfoldOccurrences r).get index).eval input
  have hlist : booleanMean
      (fun sample : PrimeIndex (primeCutoff a r target) ×
          NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale
            (listDenominator a r target) =>
        selectionRow a r liveScale (listDenominator a r target) input sel sample.1 sample.2 !=
          modularEquationHolds (ThresholdRows.equation a r sel) sample.1 actual) ≤
        1 / (primeDenominator a r target + 1 : ℕ) := by
    apply booleanMean_product_le_of_fiber _ _ hp he
    intro prime
    calc
      _ ≤ (modulusDigitCount prime.val : ℝ) / (listDenominator a r target + 1 : ℕ) :=
        selectionRow_mismatch_reciprocal spectrum a r liveScale
          (listDenominator a r target) input sel prime
      _ ≤ (modulusDigitCount (primeCutoff a r target) : ℝ) /
          (listDenominator a r target + 1 : ℕ) := by
        gcongr
        exact_mod_cast Nat.succ_le_succ
          (Nat.log_mono_right (mem_primesUpTo.mp prime.property).2)
      _ ≤ _ := listUnionError_le a r target
  have hprime : booleanMean
      (fun sample : PrimeIndex (primeCutoff a r target) ×
          NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale
            (listDenominator a r target) =>
        modularEquationHolds (ThresholdRows.equation a r sel) sample.1 actual !=
          exactRow a r sel input) ≤ 1 / (primeDenominator a r target + 1 : ℕ) := by
    rw [booleanMean_product_left
      (fun prime : PrimeIndex (primeCutoff a r target) =>
        modularEquationHolds (ThresholdRows.equation a r sel) prime actual !=
          exactRow a r sel input) hp he]
    exact (prime_mismatch_le (certificate theta a r target) sel actual).trans
      (certificate_error_le theta a r target)
  exact (booleanMean_mismatch_triangle
    (fun sample : PrimeIndex (primeCutoff a r target) ×
        NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale
          (listDenominator a r target) =>
      selectionRow a r liveScale (listDenominator a r target) input sel sample.1 sample.2)
    (fun sample => modularEquationHolds (ThresholdRows.equation a r sel) sample.1 actual)
    (fun _ => exactRow a r sel input)).trans (add_le_add hlist hprime)

def pointEstimate (liveScale target : ℕ) (input : BitInput r.q) : ℝ :=
  ∑ sel : ThresholdRows.Selection a r,
    booleanMean (fun sample : PrimeIndex (primeCutoff a r target) ×
        NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale
          (listDenominator a r target) =>
      selectionRow a r liveScale (listDenominator a r target) input sel sample.1 sample.2)

theorem pointEstimate_error_le (spectrum : ExpanderSpectrumContract)
    (theta : PrimeThetaBoundContract) (liveScale target : ℕ) (input : BitInput r.q) :
    |pointEstimate a r liveScale target input -
        bitAsReal (conjunctionBit NormalizedThresholdThresholdCircuit.eval r.circuits input)| ≤
      1 / (target + 1 : ℕ) := by
  have he := (normalizedOccurrenceListCertificate spectrum (thresholdFourfoldOccurrences r)
    liveScale (listDenominator a r target)).cardPositive
  have hp := (certificate theta a r target).cardPositive
  have hcard : 0 < Fintype.card (PrimeIndex (primeCutoff a r target) ×
      NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale
        (listDenominator a r target)) := by
    rw [Fintype.card_prod]
    exact Nat.mul_pos hp he
  have hexact : (∑ sel : ThresholdRows.Selection a r, bitAsReal (exactRow a r sel input)) =
      bitAsReal (conjunctionBit NormalizedThresholdThresholdCircuit.eval r.circuits input) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) (exactRow_sum a r input)
    push_cast at h
    simpa only [SupplierList.bitAsReal_eq_toNat] using h
  rw [← hexact]
  unfold pointEstimate
  exact (sum_pointwise_error _ _
    (1 / (primeDenominator a r target + 1 : ℕ) +
      1 / (primeDenominator a r target + 1 : ℕ))
    (fun sel => (booleanMean_error_le hcard _ (exactRow a r sel input)).trans
      (selection_mismatch_le a r spectrum theta liveScale target input sel))).trans
    (reciprocalUnionBudget (Fintype.card (ThresholdRows.Selection a r)) target)

def estimate (liveScale target : ℕ) : ℝ :=
  SupplierList.realMean (pointEstimate a r liveScale target)

theorem estimate_error_le (spectrum : ExpanderSpectrumContract)
    (theta : PrimeThetaBoundContract) (liveScale target : ℕ) :
    |estimate a r liveScale target -
        conjunctionProbability NormalizedThresholdThresholdCircuit.eval r.circuits| ≤
      1 / (target + 1 : ℕ) :=
  realMean_error_le _ _ _ (pointEstimate_error_le a r spectrum theta liveScale target)

theorem estimate_eq_ratio (liveScale target : ℕ) :
    estimate a r liveScale target =
      (nativeNumerator a r liveScale (listDenominator a r target) (primeCutoff a r target) : ℝ) /
        nativeDenominator r liveScale (listDenominator a r target) (primeCutoff a r target) := by
  unfold estimate SupplierList.realMean pointEstimate booleanMean
    nativeNumerator nativeDenominator
  simp only [Fintype.card_prod, Fintype.sum_prod_type, Nat.cast_mul, Nat.cast_sum,
    SupplierList.bitAsReal_eq_toNat, ← Finset.sum_div, div_div]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sel _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro prime _
  rw [Finset.sum_comm]

end Threshold

theorem coordinate_eval {q : Nat} (occ : List (SupportedNormalizedGate q))
    (L den : Nat) (x : BitInput q) (mask : Finset (Fin occ.length))
    (sample : NormalizedOccurrenceListSeed occ L den)
    (candidate : Fin (occ.length + 1)) :
    evaluateStructuralGF2 (LiveRows.residualAssignment occ (CyclicChoice.live occ L) x)
      (LiveRows.coordinatePoly false occ (CyclicChoice.live occ L) den mask sample candidate) =
    canonicalOccurrenceListCoordinate occ L den
      (normalizedMaskedResidualActiveSet occ L x mask) sample candidate := by
  unfold LiveRows.coordinatePoly LiveRows.residualAssignment LiveRows.bound
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [evaluateStructuralMaskedWalkListCoordinate, executableWalkListCoordinate_eq_compiled]
  unfold canonicalOccurrenceListCoordinate normalizedMaskedResidualActiveSet
    occurrenceMaskedResidualActiveSet occurrenceResidualActiveSet
  congr 1
  funext level
  exact executableGradedWindow_eq_gradedWindow _ level

theorem symRow_eq (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (L den : Nat) (x : BitInput r.q)
    (sample : NormalizedOccurrenceListSeed (symmetricFourfoldOccurrences r) L den) :
    LiveRows.symRow r (CyclicChoice.live (symmetricFourfoldOccurrences r) L) den x sample =
      canonicalSymmetricFourfoldRow r L den x sample := by
  unfold LiveRows.symRow LiveRows.symPolynomial
  simp only [Bool.false_eq_true, ↓reduceIte, evaluateStructuralGF2_finiteConjunction]
  unfold canonicalSymmetricFourfoldRow
  apply finiteBoolConjunction_congr
  intro i
  rw [evaluateStructuralGF2_oneHotLookup]
  unfold canonicalSymmetricCircuitRow canonicalOccurrenceLookupRow
  congr 1
  funext candidate
  exact coordinate_eval (symmetricFourfoldOccurrences r) L den x
    (symmetricCircuitMask r i) sample candidate

theorem modularOffset_eq {q : Nat} (occ : List (SupportedNormalizedGate q))
    (L : Nat) (x : BitInput q) (equation : LabelledEquation (Fin occ.length)) (p : Nat) :
    LiveRows.modularOffset occ (CyclicChoice.live occ L) x equation p =
      modularResidualOffset occ L x equation p := by
  simp only [LiveRows.modularOffset, modularResidualOffset,
    occurrenceWeightedResidualConstant, bitInt_eq_toNat]

theorem thrRow_eq (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (L den : Nat) (x : BitInput r.q) (sel : ThresholdRows.Selection a r)
    {cutoff : Nat} (prime : PrimeIndex cutoff)
    (sample : NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) L den) :
    LiveRows.thrSelectionRow a r (CyclicChoice.live (thresholdFourfoldOccurrences r) L)
      den x sel prime sample = selectionRow a r L den x sel prime sample := by
  unfold LiveRows.thrSelectionRow LiveRows.thrPolynomial
  simp only [Bool.false_eq_true, ↓reduceIte, evaluateStructuralGF2_modularRadixRow]
  rw [modularOffset_eq]
  unfold selectionRow canonicalOccurrenceCoefficientRadixRow canonicalOccurrenceModularRadixRow
  congr 1
  funext digit candidate
  exact coordinate_eval (thresholdFourfoldOccurrences r) L den x
    (Finset.univ.filter (fun i =>
      (modularCoefficientResidue (ThresholdRows.equation a r sel) prime.val i).testBit digit.val))
    sample candidate

theorem symmetricAccuracy : PCJa94fb905a93646cd.SymmetricAccuracy := by
  intro sources L target r
  have hcard := (normalizedOccurrenceListCertificate (expanderOf sources)
    (symmetricFourfoldOccurrences r) L (symmetricListDenominator r target)).cardPositive
  letI : Nonempty (NormalizedOccurrenceListSeed (symmetricFourfoldOccurrences r) L
      (symmetricListDenominator r target)) := Fintype.card_pos_iff.mp hcard
  constructor
  · exact Nat.mul_pos hcard (by positivity)
  · let aggregation : FiniteRowAggregation (BitInput r.q)
        (NormalizedOccurrenceListSeed (symmetricFourfoldOccurrences r) L
          (symmetricListDenominator r target)) :=
      ⟨fun sample x => LiveRows.symRow r
        (CyclicChoice.live (symmetricFourfoldOccurrences r) L)
        (symmetricListDenominator r target) x sample⟩
    have h := aggregation.error_le_of_pointwise
      (conjunctionBit NormalizedSymmetricThresholdCircuit.eval r.circuits)
      (1 / (target + 1 : Nat)) (fun x => by
        change booleanMean (fun sample => LiveRows.symRow r
          (CyclicChoice.live (symmetricFourfoldOccurrences r) L)
          (symmetricListDenominator r target) x sample !=
          conjunctionBit NormalizedSymmetricThresholdCircuit.eval r.circuits x) ≤ _
        simp only [symRow_eq]
        exact (canonicalSymmetricFourfoldRow_mismatch_reciprocal (expanderOf sources)
          r L (symmetricListDenominator r target) x).trans (symmetricListError_le r target))
    simp only [aggregation, FiniteRowAggregation.mean, FiniteRowAggregation.acceptanceCount,
      FiniteRowAggregation.sampleCount, card_bitInput, LiveRows.symNumerator,
      LiveRows.symDenominator, Rat.cast_div, Rat.cast_natCast,
      LiveRows.Seed, LiveRows.bound, NormalizedOccurrenceListSeed,
      conjunctionProbability] at h ⊢
    exact h

theorem thresholdAccuracy : PCJa94fb905a93646cd.ThresholdAccuracy := by
  intro sources L target r
  let a := decompositionOf sources
  have hp := (certificate (primeOf sources) a r target).cardPositive
  have he := (normalizedOccurrenceListCertificate (expanderOf sources)
    (thresholdFourfoldOccurrences r) L (listDenominator a r target)).cardPositive
  constructor
  · exact Nat.mul_pos (Nat.mul_pos hp he) (by positivity)
  · have hnum : LiveRows.thrNumerator a r L target =
        nativeNumerator a r L (listDenominator a r target) (primeCutoff a r target) := by
      unfold LiveRows.thrNumerator nativeNumerator
      simp only [thrRow_eq, LiveRows.Seed, LiveRows.bound, NormalizedOccurrenceListSeed]
      rfl
    have hden : LiveRows.thrDenominator a r L target =
        nativeDenominator r L (listDenominator a r target) (primeCutoff a r target) := rfl
    change |(((LiveRows.thrNumerator a r L target : Rat) /
      LiveRows.thrDenominator a r L target : Rat) : Real) - _| ≤ _
    rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast, hnum, hden, ← estimate_eq_ratio]
    exact estimate_error_le a r (expanderOf sources) (primeOf sources) L target

end
end PCJa94fb905a93646cd.Chosen
