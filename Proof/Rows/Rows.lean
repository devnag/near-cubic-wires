import Proof.Rows.Active
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
noncomputable def canonicalOccurrenceLookupRow
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (active : BoundedActiveSet occurrences.length
      (touchingCost (occurrenceSupport occurrences)
        (CyclicChoice.live occurrences liveScale)))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (lookup : Fin (occurrences.length + 1) → Bool) : Bool :=
  oneHotLookupRow lookup fun candidate =>
    canonicalOccurrenceListCoordinate occurrences liveScale denominator
      active sample candidate

theorem canonicalOccurrenceLookupRow_eq_of_certificate
    (spectrum : ExpanderSpectrumContract)
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (active : BoundedActiveSet occurrences.length
      (touchingCost (occurrenceSupport occurrences)
        (CyclicChoice.live occurrences liveScale)))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (lookup : Fin (occurrences.length + 1) → Bool)
    (hsucceeds :
      (normalizedOccurrenceListCertificate spectrum occurrences
        liveScale denominator).succeeds active sample = true) :
    canonicalOccurrenceLookupRow occurrences liveScale denominator
        active sample lookup =
      lookup (boundedActiveCard active) := by
  unfold canonicalOccurrenceLookupRow
  apply oneHotLookupRow_eq_of_oneHot lookup _
    (boundedActiveCard active)
  intro candidate
  rw [compiledCanonicalOccurrenceListCoordinate_eq_of_certificate
    spectrum occurrences liveScale denominator active sample
      candidate hsucceeds]
  apply decide_eq_decide.mpr
  constructor
  · intro hvalue
    apply Fin.ext
    exact hvalue
  · intro hequal
    exact congrArg Fin.val hequal

theorem canonicalOccurrenceShiftedLookupRow_eq_of_certificate
    (spectrum : ExpanderSpectrumContract)
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (active : BoundedActiveSet occurrences.length
      (touchingCost (occurrenceSupport occurrences)
        (CyclicChoice.live occurrences liveScale)))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (offset total : ℕ)
    (lookup : Fin (occurrences.length + 1) → Bool)
    (htotal : offset + active.1.card = total)
    (htotalBound : total < occurrences.length + 1)
    (hsucceeds :
      (normalizedOccurrenceListCertificate spectrum occurrences
        liveScale denominator).succeeds active sample = true) :
    canonicalOccurrenceLookupRow occurrences liveScale denominator
        active sample (shiftedFiniteLookup offset lookup) =
      lookup ⟨total, htotalBound⟩ := by
  rw [canonicalOccurrenceLookupRow_eq_of_certificate spectrum
    occurrences liveScale denominator active sample
      (shiftedFiniteLookup offset lookup) hsucceeds]
  apply shiftedFiniteLookup_eq lookup (boundedActiveCard active)
  simpa [boundedActiveCard] using htotal

noncomputable def canonicalSymmetricCircuitRow
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput request.q)
    (circuitIndex : Fin request.circuits.length)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale denominator) : Bool :=
  canonicalOccurrenceLookupRow
    (symmetricFourfoldOccurrences request) liveScale denominator
    (normalizedMaskedResidualActiveSet
      (symmetricFourfoldOccurrences request) liveScale input
      (symmetricCircuitMask request circuitIndex))
    sample
    (shiftedFiniteLookup
      (occurrenceResidualConstantCount
        (symmetricFourfoldOccurrences request) liveScale input
        (symmetricCircuitMask request circuitIndex))
      (symmetricCircuitTopLookup request circuitIndex))

theorem canonicalSymmetricCircuitRow_eq_of_certificate
    (spectrum : ExpanderSpectrumContract)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput request.q)
    (circuitIndex : Fin request.circuits.length)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale denominator)
    (hsucceeds :
      (normalizedOccurrenceListCertificate spectrum
        (symmetricFourfoldOccurrences request) liveScale denominator).succeeds
          (normalizedMaskedResidualActiveSet
            (symmetricFourfoldOccurrences request) liveScale input
            (symmetricCircuitMask request circuitIndex)) sample = true) :
    canonicalSymmetricCircuitRow request liveScale denominator input
        circuitIndex sample =
      (request.circuits.get circuitIndex).eval input := by
  unfold canonicalSymmetricCircuitRow
  rw [canonicalOccurrenceShiftedLookupRow_eq_of_certificate spectrum
    (symmetricFourfoldOccurrences request) liveScale denominator
    (normalizedMaskedResidualActiveSet
      (symmetricFourfoldOccurrences request) liveScale input
      (symmetricCircuitMask request circuitIndex))
    sample
    (occurrenceResidualConstantCount
      (symmetricFourfoldOccurrences request) liveScale input
      (symmetricCircuitMask request circuitIndex))
    ((request.circuits.get circuitIndex).acceptedBottomCount input).val
    (symmetricCircuitTopLookup request circuitIndex)
    (symmetricCircuitResidualCount_reconstruction
      request liveScale input circuitIndex)
    (symmetricAcceptedCountInOccurrences request circuitIndex input).isLt
    hsucceeds]
  exact symmetricCircuitTopLookup_accepted request circuitIndex input

noncomputable def canonicalSymmetricFourfoldRow
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput request.q)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale denominator) : Bool :=
  finiteBoolConjunction fun circuitIndex : Fin request.circuits.length =>
    canonicalSymmetricCircuitRow request liveScale denominator input
      circuitIndex sample

theorem canonicalSymmetricFourfoldRow_eq_of_certificate
    (spectrum : ExpanderSpectrumContract)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput request.q)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale denominator)
    (hsucceeds : ∀ circuitIndex : Fin request.circuits.length,
      (normalizedOccurrenceListCertificate spectrum
        (symmetricFourfoldOccurrences request) liveScale denominator).succeeds
          (normalizedMaskedResidualActiveSet
            (symmetricFourfoldOccurrences request) liveScale input
            (symmetricCircuitMask request circuitIndex)) sample = true) :
    canonicalSymmetricFourfoldRow request liveScale denominator input sample =
      conjunctionBit NormalizedSymmetricThresholdCircuit.eval
        request.circuits input := by
  unfold canonicalSymmetricFourfoldRow
  calc
    finiteBoolConjunction
        (fun circuitIndex : Fin request.circuits.length =>
          canonicalSymmetricCircuitRow request liveScale denominator input
            circuitIndex sample) =
        finiteBoolConjunction
          (fun circuitIndex : Fin request.circuits.length =>
            (request.circuits.get circuitIndex).eval input) := by
      apply finiteBoolConjunction_congr
      intro circuitIndex
      exact canonicalSymmetricCircuitRow_eq_of_certificate spectrum request
        liveScale denominator input circuitIndex sample
          (hsucceeds circuitIndex)
    _ = conjunctionBit NormalizedSymmetricThresholdCircuit.eval
          request.circuits input :=
      finiteBoolConjunction_get_eq_conjunctionBit
        NormalizedSymmetricThresholdCircuit.eval request.circuits input

theorem canonicalSymmetricFourfoldRow_mismatch_reciprocal
    (spectrum : ExpanderSpectrumContract)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput request.q) :
    booleanMean
        (fun sample : NormalizedOccurrenceListSeed
            (symmetricFourfoldOccurrences request) liveScale denominator =>
          canonicalSymmetricFourfoldRow request liveScale denominator
              input sample !=
            conjunctionBit NormalizedSymmetricThresholdCircuit.eval
              request.circuits input) ≤
      request.circuits.length / (denominator + 1 : ℕ) := by
  let certificate :=
    normalizedOccurrenceListCertificate spectrum
      (symmetricFourfoldOccurrences request) liveScale denominator
  calc
    _ ≤ Fintype.card (Fin request.circuits.length) * certificate.failure := by
      apply booleanMean_unionBound_uniform
        (fun sample : NormalizedOccurrenceListSeed
            (symmetricFourfoldOccurrences request) liveScale denominator =>
          canonicalSymmetricFourfoldRow request liveScale denominator
              input sample !=
            conjunctionBit NormalizedSymmetricThresholdCircuit.eval
              request.circuits input)
        (fun circuitIndex sample =>
          !(certificate.succeeds
            (normalizedMaskedResidualActiveSet
              (symmetricFourfoldOccurrences request) liveScale input
              (symmetricCircuitMask request circuitIndex)) sample))
        certificate.failure
      · intro sample hmismatch
        by_contra hnone
        have hall : ∀ circuitIndex : Fin request.circuits.length,
            certificate.succeeds
              (normalizedMaskedResidualActiveSet
                (symmetricFourfoldOccurrences request) liveScale input
                (symmetricCircuitMask request circuitIndex)) sample = true := by
          intro circuitIndex
          cases hvalue : certificate.succeeds
              (normalizedMaskedResidualActiveSet
                (symmetricFourfoldOccurrences request) liveScale input
                (symmetricCircuitMask request circuitIndex)) sample
          · exfalso
            apply hnone
            exact ⟨circuitIndex, by simp [hvalue]⟩
          · rfl
        have hequal :=
          canonicalSymmetricFourfoldRow_eq_of_certificate spectrum request
            liveScale denominator input sample hall
        rw [hequal] at hmismatch
        simp at hmismatch
      · intro circuitIndex
        exact certificate.pointwise
          (normalizedMaskedResidualActiveSet
            (symmetricFourfoldOccurrences request) liveScale input
            (symmetricCircuitMask request circuitIndex))
    _ ≤ Fintype.card (Fin request.circuits.length) *
          (1 / (denominator + 1 : ℕ)) := by
      gcongr
      exact normalizedOccurrenceListFailure_le spectrum
        (symmetricFourfoldOccurrences request) liveScale denominator
    _ = request.circuits.length / (denominator + 1 : ℕ) := by
      simp only [Fintype.card_fin]
      ring

theorem coefficientBitRadixValue_eq
    {q digits : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length))
    (coefficient : Fin occurrences.length → ℕ)
    (hcoefficient : ∀ index, coefficient index < 2 ^ digits) :
    radixValue 2
        (boundedActivePopulation fun digit : Fin digits =>
          normalizedCoefficientBitActiveSet occurrences liveScale input
            mask coefficient digit.val) =
      ∑ index ∈ mask, coefficient index *
        (occurrenceResidualVariable occurrences
          (CyclicChoice.live occurrences liveScale) input index).toNat := by
  let residual : Fin occurrences.length → Bool :=
    fun index =>
      decide (index ∈ mask) &&
        occurrenceResidualVariable occurrences
          (CyclicChoice.live occurrences liveScale) input index
  let digit : Fin occurrences.length → Fin digits → ℕ :=
    fun index place => ((coefficient index).testBit place.val).toNat
  have hreconstruct : ∀ index,
      coefficient index =
        ∑ place : Fin digits, 2 ^ place.val * digit index place := by
    intro index
    calc
      coefficient index =
          ∑ place : Fin digits,
            ((coefficient index).testBit place.val).toNat *
              2 ^ place.val :=
        (testBit_toNat_sum_eq (hcoefficient index)).symm
      _ = ∑ place : Fin digits,
            2 ^ place.val * digit index place := by
        apply Finset.sum_congr rfl
        intro place _
        dsimp [digit]
        ring
  have hscore :=
    radixScore_eq_digitPopulations 2 coefficient digit residual hreconstruct
  symm
  calc
    (∑ index ∈ mask, coefficient index *
        (occurrenceResidualVariable occurrences
          (CyclicChoice.live occurrences liveScale) input index).toNat) =
        ∑ index : Fin occurrences.length,
          coefficient index * (residual index).toNat := by
      calc
        _ = ∑ index ∈
              (Finset.univ.filter fun index : Fin occurrences.length =>
                index ∈ mask),
              coefficient index *
                (occurrenceResidualVariable occurrences
                  (CyclicChoice.live occurrences liveScale) input
                    index).toNat := by
          simp
        _ = ∑ index : Fin occurrences.length,
              if index ∈ mask then
                coefficient index *
                  (occurrenceResidualVariable occurrences
                    (CyclicChoice.live occurrences liveScale) input
                      index).toNat
              else 0 :=
          Finset.sum_filter _ _
        _ = ∑ index : Fin occurrences.length,
              coefficient index * (residual index).toNat := by
          apply Finset.sum_congr rfl
          intro index _
          by_cases hmember : index ∈ mask
          · simp [residual, hmember]
          · simp [residual, hmember]
    _ = ∑ place : Fin digits, 2 ^ place.val *
          digitPopulation digit residual place :=
      hscore
    _ = radixValue 2
        (boundedActivePopulation fun place : Fin digits =>
          normalizedCoefficientBitActiveSet occurrences liveScale input
            mask coefficient place.val) := by
      unfold radixValue boundedActivePopulation boundedActiveCard
      apply Finset.sum_congr rfl
      intro place _
      congr 1
      change digitPopulation digit residual place =
        (occurrenceCoefficientBitActiveSet occurrences liveScale input
          mask coefficient place.val).card
      rw [occurrenceCoefficientBitActiveSet_card_eq_sum]
      unfold digitPopulation
      calc
        (∑ index : Fin occurrences.length,
            digit index place * (residual index).toNat) =
            ∑ index ∈
              (Finset.univ.filter fun index : Fin occurrences.length =>
                index ∈ mask),
              (occurrenceResidualVariable occurrences
                    (CyclicChoice.live occurrences liveScale) input index &&
                (coefficient index).testBit place.val).toNat := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro index _
          by_cases hmember : index ∈ mask
          · cases hresidual :
                occurrenceResidualVariable occurrences
                  (CyclicChoice.live occurrences liveScale) input index <;>
              cases hbit : (coefficient index).testBit place.val <;>
              simp [digit, residual, hmember, hresidual, hbit]
          · simp [digit, residual, hmember]
        _ = ∑ index ∈ mask,
              (occurrenceResidualVariable occurrences
                    (CyclicChoice.live occurrences liveScale) input index &&
                (coefficient index).testBit place.val).toNat := by
          simp

def modularResidualOffset
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q)
    (equation : LabelledEquation (Fin occurrences.length))
    (modulus : ℕ) : ℕ :=
  ((occurrenceWeightedResidualConstant occurrences liveScale input
      Finset.univ equation.weights - equation.target) %
        (modulus : ℤ)).toNat

theorem modularResidualEquation_spec
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q)
    (equation : LabelledEquation (Fin occurrences.length))
    (modulus : ℕ) (hmodulus : 0 < modulus) :
    ((modularResidualOffset occurrences liveScale input equation modulus +
          ∑ index ∈ (Finset.univ : Finset (Fin occurrences.length)),
            modularCoefficientResidue equation modulus index *
              (occurrenceResidualVariable occurrences
                (CyclicChoice.live occurrences liveScale) input index).toNat) %
        modulus = 0) ↔
      equation.HoldsModulo (modulus : ℤ)
        (fun index => (occurrences.get index).eval input) := by
  let variableBit : Fin occurrences.length → Bool :=
    fun index =>
      occurrenceResidualVariable occurrences
        (CyclicChoice.live occurrences liveScale) input index
  let constantDifference : ℤ :=
    occurrenceWeightedResidualConstant occurrences liveScale input
      Finset.univ equation.weights - equation.target
  let variableScore : ℤ :=
    occurrenceWeightedResidualVariable occurrences liveScale input
      Finset.univ equation.weights
  have hmodulusInt : (0 : ℤ) < modulus := by exact_mod_cast hmodulus
  have hcoefficient :
      ∀ index : Fin occurrences.length,
        ((modularCoefficientResidue equation modulus index : ℕ) : ℤ) ≡
          equation.weights index [ZMOD (modulus : ℤ)] := by
    intro index
    unfold modularCoefficientResidue
    rw [Int.toNat_of_nonneg
      (Int.emod_nonneg _ (ne_of_gt hmodulusInt))]
    exact Int.mod_modEq _ _
  have hvariable :
      ((∑ index ∈ (Finset.univ : Finset (Fin occurrences.length)),
          modularCoefficientResidue equation modulus index *
            (variableBit index).toNat : ℕ) : ℤ) ≡
        variableScore [ZMOD (modulus : ℤ)] := by
    unfold variableScore occurrenceWeightedResidualVariable
    push_cast
    apply Int.ModEq.sum
    intro index _
    apply Int.ModEq.mul
    · exact hcoefficient index
    · simp [variableBit, bitInt_eq_toNat]
  have hoffset :
      ((modularResidualOffset occurrences liveScale input equation modulus :
          ℕ) : ℤ) ≡ constantDifference [ZMOD (modulus : ℤ)] := by
    unfold modularResidualOffset constantDifference
    rw [Int.toNat_of_nonneg
      (Int.emod_nonneg _ (ne_of_gt hmodulusInt))]
    exact Int.mod_modEq _ _
  have hcombined :
      (((modularResidualOffset occurrences liveScale input equation modulus +
          ∑ index ∈ (Finset.univ : Finset (Fin occurrences.length)),
            modularCoefficientResidue equation modulus index *
              (variableBit index).toNat : ℕ) : ℕ) : ℤ) ≡
        constantDifference + variableScore [ZMOD (modulus : ℤ)] := by
    change
      ((modularResidualOffset occurrences liveScale input equation modulus :
          ℕ) : ℤ) +
        ((∑ index ∈ (Finset.univ : Finset (Fin occurrences.length)),
          modularCoefficientResidue equation modulus index *
            (variableBit index).toNat : ℕ) : ℤ) ≡
        constantDifference + variableScore [ZMOD (modulus : ℤ)]
    exact hoffset.add hvariable
  have hreconstruct :
      constantDifference + variableScore =
        equation.difference
          (fun index => (occurrences.get index).eval input) := by
    have hresidual :=
      occurrenceWeightedResidual_reconstruction occurrences liveScale input
        Finset.univ equation.weights
    unfold constantDifference variableScore
      LabelledEquation.difference LabelledEquation.score
    linarith
  rw [show (∑ index ∈ (Finset.univ : Finset (Fin occurrences.length)),
      modularCoefficientResidue equation modulus index *
        (occurrenceResidualVariable occurrences
          (CyclicChoice.live occurrences liveScale) input index).toNat) =
      ∑ index ∈ (Finset.univ : Finset (Fin occurrences.length)),
        modularCoefficientResidue equation modulus index *
          (variableBit index).toNat by rfl]
  unfold LabelledEquation.HoldsModulo
  rw [← hreconstruct]
  have hemod := hcombined.eq
  rw [show
      (modularResidualOffset occurrences liveScale input equation modulus +
        ∑ index ∈ (Finset.univ : Finset (Fin occurrences.length)),
          modularCoefficientResidue equation modulus index *
            (variableBit index).toNat) % modulus = 0 ↔
        (((modularResidualOffset occurrences liveScale input equation modulus +
          ∑ index ∈ (Finset.univ : Finset (Fin occurrences.length)),
            modularCoefficientResidue equation modulus index *
              (variableBit index).toNat : ℕ) : ℕ) : ℤ) %
            (modulus : ℤ) = 0 by norm_cast]
  exact hemod ▸ Iff.rfl

noncomputable def canonicalOccurrenceModularRadixRow
    {q digits : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (active : Fin digits →
      BoundedActiveSet occurrences.length
        (touchingCost (occurrenceSupport occurrences)
          (CyclicChoice.live occurrences liveScale)))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (modulus offset base : ℕ) : Bool :=
  modularRadixRow modulus offset base fun digit candidate =>
    canonicalOccurrenceListCoordinate occurrences liveScale denominator
      (active digit) sample candidate

theorem canonicalOccurrenceModularRadixRow_eq_of_certificate
    {q digits : ℕ}
    (spectrum : ExpanderSpectrumContract)
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (active : Fin digits →
      BoundedActiveSet occurrences.length
        (touchingCost (occurrenceSupport occurrences)
          (CyclicChoice.live occurrences liveScale)))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (modulus offset base : ℕ)
    (hsucceeds : ∀ digit,
      (normalizedOccurrenceListCertificate spectrum occurrences
        liveScale denominator).succeeds (active digit) sample = true) :
    canonicalOccurrenceModularRadixRow occurrences liveScale denominator
        active sample modulus offset base =
      modularTupleAccepts modulus offset base
        (boundedActivePopulation active) := by
  unfold canonicalOccurrenceModularRadixRow
  apply modularRadixRow_eq_of_oneHot modulus offset base _
    (boundedActivePopulation active)
  intro digit candidate
  rw [compiledCanonicalOccurrenceListCoordinate_eq_of_certificate
    spectrum occurrences liveScale denominator (active digit)
      sample candidate (hsucceeds digit)]
  apply decide_eq_decide.mpr
  constructor
  · intro hvalue
    apply Fin.ext
    exact hvalue
  · intro hequal
    exact congrArg Fin.val hequal

theorem canonicalOccurrenceModularRadixRow_mismatch_le
    {q digits : ℕ}
    (spectrum : ExpanderSpectrumContract)
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (active : Fin digits →
      BoundedActiveSet occurrences.length
        (touchingCost (occurrenceSupport occurrences)
          (CyclicChoice.live occurrences liveScale)))
    (modulus offset base : ℕ) :
    booleanMean
        (fun sample : NormalizedOccurrenceListSeed
            occurrences liveScale denominator =>
          canonicalOccurrenceModularRadixRow occurrences liveScale denominator
              active sample modulus offset base !=
            modularTupleAccepts modulus offset base
              (boundedActivePopulation active)) ≤
      Fintype.card (Fin digits) *
        (normalizedOccurrenceListCertificate spectrum occurrences
          liveScale denominator).failure := by
  let certificate :=
    normalizedOccurrenceListCertificate spectrum occurrences
      liveScale denominator
  apply booleanMean_unionBound_uniform
    (fun sample : NormalizedOccurrenceListSeed
        occurrences liveScale denominator =>
      canonicalOccurrenceModularRadixRow occurrences liveScale denominator
          active sample modulus offset base !=
        modularTupleAccepts modulus offset base
          (boundedActivePopulation active))
    (fun digit sample => !(certificate.succeeds (active digit) sample))
    certificate.failure
  · intro sample hmismatch
    by_contra hnone
    have hall : ∀ digit,
        certificate.succeeds (active digit) sample = true := by
      intro digit
      cases hvalue : certificate.succeeds (active digit) sample
      · exfalso
        apply hnone
        exact ⟨digit, by simp [hvalue]⟩
      · rfl
    have hequal :=
      canonicalOccurrenceModularRadixRow_eq_of_certificate
        spectrum occurrences liveScale denominator active sample
          modulus offset base hall
    rw [hequal] at hmismatch
    simp at hmismatch
  · intro digit
    exact certificate.pointwise (active digit)

theorem canonicalOccurrenceModularRadixRow_mismatch_reciprocal
    {q digits : ℕ}
    (spectrum : ExpanderSpectrumContract)
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (active : Fin digits →
      BoundedActiveSet occurrences.length
        (touchingCost (occurrenceSupport occurrences)
          (CyclicChoice.live occurrences liveScale)))
    (modulus offset base : ℕ) :
    booleanMean
        (fun sample : NormalizedOccurrenceListSeed
            occurrences liveScale denominator =>
          canonicalOccurrenceModularRadixRow occurrences liveScale denominator
              active sample modulus offset base !=
            modularTupleAccepts modulus offset base
              (boundedActivePopulation active)) ≤
      (digits : ℝ) / (denominator + 1 : ℕ) := by
  calc
    _ ≤ Fintype.card (Fin digits) *
        (normalizedOccurrenceListCertificate spectrum occurrences
          liveScale denominator).failure :=
      canonicalOccurrenceModularRadixRow_mismatch_le spectrum occurrences
        liveScale denominator active modulus offset base
    _ ≤ (digits : ℝ) * (1 / (denominator + 1 : ℕ)) := by
      rw [Fintype.card_fin]
      gcongr
      exact normalizedOccurrenceListFailure_le spectrum occurrences
        liveScale denominator
    _ = (digits : ℝ) / (denominator + 1 : ℕ) := by ring

noncomputable def canonicalOccurrenceCoefficientRadixRow
    {q digits : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length))
    (coefficient : Fin occurrences.length → ℕ)
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (modulus offset : ℕ) : Bool :=
  canonicalOccurrenceModularRadixRow occurrences liveScale denominator
    (fun digit : Fin digits =>
      normalizedCoefficientBitActiveSet occurrences liveScale input
        mask coefficient digit.val)
    sample modulus offset 2

theorem canonicalOccurrenceCoefficientRadixRow_mismatch_reciprocal
    {q digits : ℕ}
    (spectrum : ExpanderSpectrumContract)
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length))
    (coefficient : Fin occurrences.length → ℕ)
    (modulus offset : ℕ)
    (hcoefficient : ∀ index, coefficient index < 2 ^ digits) :
    booleanMean
        (fun sample : NormalizedOccurrenceListSeed
            occurrences liveScale denominator =>
          canonicalOccurrenceCoefficientRadixRow (digits := digits)
              occurrences liveScale
              denominator input mask coefficient sample modulus offset !=
            decide ((offset +
              ∑ index ∈ mask, coefficient index *
                (occurrenceResidualVariable occurrences
                  (CyclicChoice.live occurrences liveScale) input
                    index).toNat) % modulus = 0)) ≤
      (digits : ℝ) / (denominator + 1 : ℕ) := by
  have hbound :=
    canonicalOccurrenceModularRadixRow_mismatch_reciprocal spectrum
      occurrences liveScale denominator
      (fun digit : Fin digits =>
        normalizedCoefficientBitActiveSet occurrences liveScale input
          mask coefficient digit.val)
      modulus offset 2
  have hvalue :=
    coefficientBitRadixValue_eq occurrences liveScale input
      mask coefficient hcoefficient
  simpa [canonicalOccurrenceCoefficientRadixRow,
    modularTupleAccepts, hvalue] using hbound
def selectionRow (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput r.q)
    (sel : ThresholdRows.Selection a r) {cutoff : ℕ} (prime : PrimeIndex cutoff)
    (sample : NormalizedOccurrenceListSeed
      (thresholdFourfoldOccurrences r) liveScale denominator) : Bool :=
  canonicalOccurrenceCoefficientRadixRow
    (digits := modulusDigitCount prime.val)
    (thresholdFourfoldOccurrences r) liveScale denominator input
    Finset.univ
    (modularCoefficientResidue (ThresholdRows.equation a r sel) prime.val)
    sample prime.val
    (modularResidualOffset (thresholdFourfoldOccurrences r) liveScale input
      (ThresholdRows.equation a r sel) prime.val)

theorem selectionRow_mismatch_reciprocal (spectrum : ExpanderSpectrumContract)
    (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput r.q)
    (sel : ThresholdRows.Selection a r) {cutoff : ℕ}
    (prime : PrimeIndex cutoff) :
    booleanMean
        (fun sample : NormalizedOccurrenceListSeed
            (thresholdFourfoldOccurrences r) liveScale denominator =>
          selectionRow a r liveScale denominator input sel prime sample !=
            modularEquationHolds (ThresholdRows.equation a r sel) prime
              (fun index =>
                ((thresholdFourfoldOccurrences r).get index).eval input)) ≤
      (modulusDigitCount prime.val : ℝ) / (denominator + 1 : ℕ) := by
  have hprimePositive : 0 < prime.val :=
    (mem_primesUpTo.mp prime.property).1.pos
  have hbound :=
    canonicalOccurrenceCoefficientRadixRow_mismatch_reciprocal spectrum
      (thresholdFourfoldOccurrences r) liveScale denominator input
      Finset.univ
      (modularCoefficientResidue (ThresholdRows.equation a r sel) prime.val)
      prime.val
      (modularResidualOffset (thresholdFourfoldOccurrences r) liveScale input
        (ThresholdRows.equation a r sel) prime.val)
      (fun index =>
        modularCoefficientResidue_lt (ThresholdRows.equation a r sel)
          prime.val hprimePositive index)
  have htarget :
      decide
          ((modularResidualOffset (thresholdFourfoldOccurrences r) liveScale
                input (ThresholdRows.equation a r sel) prime.val +
              ∑ index ∈
                  (Finset.univ :
                    Finset (Fin (thresholdFourfoldOccurrences r).length)),
                modularCoefficientResidue (ThresholdRows.equation a r sel)
                    prime.val index *
                  (occurrenceResidualVariable (thresholdFourfoldOccurrences r)
                    (CyclicChoice.live (thresholdFourfoldOccurrences r)
                      liveScale)
                    input index).toNat) %
            prime.val = 0) =
        modularEquationHolds (ThresholdRows.equation a r sel) prime
          (fun index =>
            ((thresholdFourfoldOccurrences r).get index).eval input) := by
    apply Bool.eq_iff_iff.mpr
    unfold modularEquationHolds
    simp only [decide_eq_true_eq]
    exact modularResidualEquation_spec (thresholdFourfoldOccurrences r)
      liveScale input (ThresholdRows.equation a r sel) prime.val
      hprimePositive
  simpa [selectionRow, htarget, modulusDigitCount] using hbound

end
end PCJa94fb905a93646cd.Chosen
