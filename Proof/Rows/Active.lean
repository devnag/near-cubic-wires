import Proof.Rows.Parent
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
def occurrenceResidualActiveSet {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q) :
    Finset (Fin occurrences.length) :=
  Finset.univ.filter fun index =>
    occurrenceResidualVariable occurrences
      (CyclicChoice.live occurrences liveScale) input index

theorem occurrenceResidualActiveSet_subset_touched {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q) :
    occurrenceResidualActiveSet occurrences liveScale input ⊆
      touchedOccurrences occurrences
        (CyclicChoice.live occurrences liveScale) := by
  intro index hactive
  have htrue :
      occurrenceResidualVariable occurrences
          (CyclicChoice.live occurrences liveScale) input index = true :=
    (Finset.mem_filter.mp hactive).2
  by_contra hnotTouched
  have hfalse :=
    occurrenceResidualVariable_eq_false_of_not_touched
      occurrences (CyclicChoice.live occurrences liveScale)
      input index hnotTouched
  rw [hfalse] at htrue
  contradiction

theorem occurrenceResidualActiveSet_card_le {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q) :
    (occurrenceResidualActiveSet occurrences liveScale input).card ≤
      touchingCost (occurrenceSupport occurrences)
        (CyclicChoice.live occurrences liveScale) := by
  calc
    (occurrenceResidualActiveSet occurrences liveScale input).card ≤
        (touchedOccurrences occurrences
          (CyclicChoice.live occurrences liveScale)).card :=
      Finset.card_le_card
        (occurrenceResidualActiveSet_subset_touched
          occurrences liveScale input)
    _ = touchingCost (occurrenceSupport occurrences)
          (CyclicChoice.live occurrences liveScale) :=
      touchedOccurrences_card occurrences
        (CyclicChoice.live occurrences liveScale)

def occurrenceMaskedResidualActiveSet {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length)) :
    Finset (Fin occurrences.length) :=
  occurrenceResidualActiveSet occurrences liveScale input ∩ mask

theorem occurrenceMaskedResidualActiveSet_card_le {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length)) :
    (occurrenceMaskedResidualActiveSet occurrences liveScale input mask).card ≤
      touchingCost (occurrenceSupport occurrences)
        (CyclicChoice.live occurrences liveScale) := by
  exact (Finset.card_le_card Finset.inter_subset_left).trans
    (occurrenceResidualActiveSet_card_le occurrences liveScale input)

theorem occurrenceMaskedResidualActiveSet_card_eq_sum {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length)) :
    (occurrenceMaskedResidualActiveSet occurrences liveScale input mask).card =
      ∑ index ∈ mask,
        (occurrenceResidualVariable occurrences
          (CyclicChoice.live occurrences liveScale) input index).toNat := by
  have hinter :
      occurrenceMaskedResidualActiveSet occurrences liveScale input mask =
        mask.filter fun index =>
          occurrenceResidualVariable occurrences
            (CyclicChoice.live occurrences liveScale) input index := by
    ext index
    simp [occurrenceMaskedResidualActiveSet,
      occurrenceResidualActiveSet, and_comm]
  rw [hinter, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro index _
  cases occurrenceResidualVariable occurrences
      (CyclicChoice.live occurrences liveScale) input index <;> rfl

def occurrenceResidualConstantCount {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length)) : ℕ :=
  ∑ index ∈ mask,
    (occurrenceResidualConstant occurrences
      (CyclicChoice.live occurrences liveScale) input index).toNat

def occurrenceWeightedResidualConstant {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length))
    (weight : Fin occurrences.length → ℤ) : ℤ :=
  ∑ index ∈ mask, weight index *
    bitInt (occurrenceResidualConstant occurrences
      (CyclicChoice.live occurrences liveScale) input index)

def occurrenceWeightedResidualVariable {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length))
    (weight : Fin occurrences.length → ℤ) : ℤ :=
  ∑ index ∈ mask, weight index *
    bitInt (occurrenceResidualVariable occurrences
      (CyclicChoice.live occurrences liveScale) input index)

theorem occurrenceWeightedResidual_reconstruction {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length))
    (weight : Fin occurrences.length → ℤ) :
    occurrenceWeightedResidualConstant occurrences liveScale input mask weight +
        occurrenceWeightedResidualVariable occurrences liveScale input mask
          weight =
      ∑ index ∈ mask, weight index *
        bitInt ((occurrences.get index).eval input) := by
  unfold occurrenceWeightedResidualConstant
    occurrenceWeightedResidualVariable
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _
  have hnat :=
    residual_sum_reconstruction (occurrences.get index).gate
      (CyclicChoice.live occurrences liveScale) input
  have hint :
      bitInt (occurrenceResidualConstant occurrences
          (CyclicChoice.live occurrences liveScale) input index) +
        bitInt (occurrenceResidualVariable occurrences
          (CyclicChoice.live occurrences liveScale) input index) =
        bitInt ((occurrences.get index).eval input) := by
    simp only [bitInt_eq_toNat, occurrenceResidualConstant,
      occurrenceResidualVariable]
    exact_mod_cast hnat
  rw [← hint]
  ring

theorem occurrenceResidualCount_reconstruction {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length)) :
    occurrenceResidualConstantCount occurrences liveScale input mask +
        (occurrenceMaskedResidualActiveSet occurrences
          liveScale input mask).card =
      ∑ index ∈ mask, ((occurrences.get index).eval input).toNat := by
  rw [occurrenceMaskedResidualActiveSet_card_eq_sum]
  unfold occurrenceResidualConstantCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _
  exact residual_sum_reconstruction
    (occurrences.get index).gate
    (CyclicChoice.live occurrences liveScale) input

def normalizedMaskedResidualActiveSet {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length)) :
    BoundedActiveSet occurrences.length
      (touchingCost (occurrenceSupport occurrences)
        (CyclicChoice.live occurrences liveScale)) :=
  ⟨occurrenceMaskedResidualActiveSet occurrences liveScale input mask,
    occurrenceMaskedResidualActiveSet_card_le
      occurrences liveScale input mask⟩

def occurrenceCoefficientBitActiveSet {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length))
    (coefficient : Fin occurrences.length → ℕ) (bit : ℕ) :
    Finset (Fin occurrences.length) :=
  occurrenceResidualActiveSet occurrences liveScale input ∩
    (mask.filter fun index => (coefficient index).testBit bit)

theorem occurrenceCoefficientBitActiveSet_card_le {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length))
    (coefficient : Fin occurrences.length → ℕ) (bit : ℕ) :
    (occurrenceCoefficientBitActiveSet occurrences liveScale input
      mask coefficient bit).card ≤
        touchingCost (occurrenceSupport occurrences)
          (CyclicChoice.live occurrences liveScale) := by
  exact (Finset.card_le_card Finset.inter_subset_left).trans
    (occurrenceResidualActiveSet_card_le occurrences liveScale input)

theorem occurrenceCoefficientBitActiveSet_card_eq_sum {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length))
    (coefficient : Fin occurrences.length → ℕ) (bit : ℕ) :
    (occurrenceCoefficientBitActiveSet occurrences liveScale input
        mask coefficient bit).card =
      ∑ index ∈ mask,
        (occurrenceResidualVariable occurrences
            (CyclicChoice.live occurrences liveScale) input index &&
          (coefficient index).testBit bit).toNat := by
  have hinter :
      occurrenceCoefficientBitActiveSet occurrences liveScale input
          mask coefficient bit =
        mask.filter fun index =>
          occurrenceResidualVariable occurrences
              (CyclicChoice.live occurrences liveScale) input index &&
            (coefficient index).testBit bit := by
    ext index
    simp [occurrenceCoefficientBitActiveSet,
      occurrenceResidualActiveSet, and_left_comm]
  rw [hinter, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro index _
  cases occurrenceResidualVariable occurrences
      (CyclicChoice.live occurrences liveScale) input index <;>
    cases (coefficient index).testBit bit <;>
    rfl

def normalizedCoefficientBitActiveSet {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length))
    (coefficient : Fin occurrences.length → ℕ) (bit : ℕ) :
    BoundedActiveSet occurrences.length
      (touchingCost (occurrenceSupport occurrences)
        (CyclicChoice.live occurrences liveScale)) :=
  ⟨occurrenceCoefficientBitActiveSet occurrences liveScale input
      mask coefficient bit,
    occurrenceCoefficientBitActiveSet_card_le
      occurrences liveScale input mask coefficient bit⟩

theorem symmetricCircuitResidualCount_reconstruction
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale : ℕ) (input : BitInput request.q)
    (circuitIndex : Fin request.circuits.length) :
    occurrenceResidualConstantCount
          (symmetricFourfoldOccurrences request) liveScale input
          (symmetricCircuitMask request circuitIndex) +
        (occurrenceMaskedResidualActiveSet
          (symmetricFourfoldOccurrences request) liveScale input
          (symmetricCircuitMask request circuitIndex)).card =
      ((request.circuits.get circuitIndex).acceptedBottomCount input).val := by
  rw [occurrenceResidualCount_reconstruction]
  exact symmetricCircuitSegment_eval_sum request circuitIndex input

abbrev NormalizedOccurrenceListSeed {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ) :=
  MargulisWalkSample
    (2 ^ toeplitzWalkSideBits
      (canonicalGradedRank occurrences.length
        (touchingCost (occurrenceSupport occurrences)
          (CyclicChoice.live occurrences liveScale))))
    (canonicalWalkLength denominator)

noncomputable def normalizedOccurrenceListCertificate
    (spectrum : ExpanderSpectrumContract)
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ) :
    AmplifiedListCertificate
      (BoundedActiveSet occurrences.length
        (touchingCost (occurrenceSupport occurrences)
          (CyclicChoice.live occurrences liveScale)))
      (NormalizedOccurrenceListSeed occurrences liveScale denominator) :=
  tunedCanonicalGradedToeplitzPoweredWalkListCertificate spectrum
    occurrences.length
    (touchingCost (occurrenceSupport occurrences)
      (CyclicChoice.live occurrences liveScale))
    denominator

theorem normalizedOccurrenceListFailure_le
    (spectrum : ExpanderSpectrumContract)
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ) :
    (normalizedOccurrenceListCertificate spectrum occurrences
      liveScale denominator).failure ≤
        1 / (denominator + 1 : ℕ) :=
  tunedCanonicalGradedToeplitzPoweredWalkListCertificate_failure_le
    spectrum occurrences.length
      (touchingCost (occurrenceSupport occurrences)
        (CyclicChoice.live occurrences liveScale))
      denominator

noncomputable def canonicalOccurrenceListCoordinate
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (active : BoundedActiveSet occurrences.length
      (touchingCost (occurrenceSupport occurrences)
        (CyclicChoice.live occurrences liveScale)))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (candidate : Fin (occurrences.length + 1)) : Bool :=
  compiledWalkListCoordinate
    (depth := canonicalGradedDepth
      (touchingCost (occurrenceSupport occurrences)
        (CyclicChoice.live occurrences liveScale)))
    active.1
    (canonicalGradedLabel occurrences.length
      (touchingCost (occurrenceSupport occurrences)
        (CyclicChoice.live occurrences liveScale)))
    (gradedWindow
      (depth := canonicalGradedDepth
        (touchingCost (occurrenceSupport occurrences)
          (CyclicChoice.live occurrences liveScale)))
      (touchingCost (occurrenceSupport occurrences)
        (CyclicChoice.live occurrences liveScale)))
    gradedTerminalWindow sample candidate

theorem compiledCanonicalOccurrenceListCoordinate_eq_of_certificate
    (spectrum : ExpanderSpectrumContract)
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (active : BoundedActiveSet occurrences.length
      (touchingCost (occurrenceSupport occurrences)
        (CyclicChoice.live occurrences liveScale)))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (candidate : Fin (occurrences.length + 1))
    (hsucceeds :
      (normalizedOccurrenceListCertificate spectrum occurrences
        liveScale denominator).succeeds
          active sample = true) :
    canonicalOccurrenceListCoordinate occurrences liveScale denominator
        active sample candidate =
      decide (candidate.val =
        active.1.card) := by
  unfold canonicalOccurrenceListCoordinate
  apply compiledWalkListCoordinate_eq_of_succeeds
    (canonicalWalkLength_odd denominator)
    active
    (canonicalGradedLabel occurrences.length
      (touchingCost (occurrenceSupport occurrences)
        (CyclicChoice.live occurrences liveScale)))
    (gradedWindow
      (depth := canonicalGradedDepth
        (touchingCost (occurrenceSupport occurrences)
          (CyclicChoice.live occurrences liveScale)))
      (touchingCost (occurrenceSupport occurrences)
        (CyclicChoice.live occurrences liveScale)))
    gradedTerminalWindow sample candidate
  apply Bool.eq_false_of_not_eq_true'
  simpa only [normalizedOccurrenceListCertificate,
    tunedCanonicalGradedToeplitzPoweredWalkListCertificate,
    gradedToeplitzPoweredWalkListCertificate,
    toeplitzPoweredWalkListCertificate,
    concretePoweredWalkListCertificate] using hsucceeds

end
end PCJa94fb905a93646cd.Chosen
