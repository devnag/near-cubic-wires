import Proof.Assembly.Semantics
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires ComponentwisePolynomial RepairOrdinary SourceInterfaces RepairSource
open RepairSource.CloseoutFinal SupplierPipeline SupplierEstimator CloseoutRowsOriginalSchedule
open CloseoutRowsEstimatorCoefficients CloseoutFinalC10ModeNativeStageFields
open CloseoutFinalC10SupplierCalls C10SupplierAccuracyChain
open PCJ9eff70d512234a4c_Fixed

namespace PCJa94fb905a93646cd

abbrev SymmetricAccuracy : Prop :=
  ∀ (sources : EightSources) (L target : Nat)
    (r : FourfoldRequest NormalizedSymmetricThresholdCircuit),
    0 < LiveRows.symDenominator r L target ∧
    |(((LiveRows.symNumerator r L target : Rat) /
        LiveRows.symDenominator r L target : Rat) : Real) -
      conjunctionProbability NormalizedSymmetricThresholdCircuit.eval r.circuits| ≤
        1 / (target + 1 : Nat)

abbrev ThresholdAccuracy : Prop :=
  ∀ (sources : EightSources) (L target : Nat)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit),
    0 < LiveRows.thrDenominator (decompositionOf sources) r L target ∧
    |(((LiveRows.thrNumerator (decompositionOf sources) r L target : Rat) /
        LiveRows.thrDenominator (decompositionOf sources) r L target : Rat) : Real) -
      conjunctionProbability NormalizedThresholdThresholdCircuit.eval r.circuits| ≤
        1 / (target + 1 : Nat)

noncomputable def estimate (sym : SymmetricAccuracy) (thr : ThresholdAccuracy)
    (sources : EightSources) (L target : Nat)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (mode : Bool) (atoms : List (C10TotalDecode.Atom pcpp))
    (hmode : ∀ atom ∈ atoms, C10NaturalModeAtoms.ModeAtom mode atom) :
    FractionEstimate (conjunctionProbability C10TotalDecode.evaluate atoms) target where
  num := (LiveRows.fraction sources L target mode atoms).1
  den := (LiveRows.fraction sources L target mode atoms).2
  positive := by
    cases mode with
    | false =>
      simpa only [LiveRows.fraction, Bool.false_eq_true, ↓reduceIte] using
        (thr sources L target ⟨q, atoms.map C10NaturalModeAtoms.nativeThresholdAtom⟩).1
    | true =>
      simpa only [LiveRows.fraction, ↓reduceIte] using
        (sym sources L target ⟨q, atoms.map C10NaturalModeAtoms.nativeSymmetricAtom⟩).1
  accurate := by
    cases mode with
    | false =>
      have h := (thr sources L target ⟨q, atoms.map C10NaturalModeAtoms.nativeThresholdAtom⟩).2
      rw [C10NaturalModeAtoms.conjunctionProbability_nativeThreshold atoms hmode] at h
      simpa only [LiveRows.fraction, Bool.false_eq_true, ↓reduceIte] using h
    | true =>
      have h := (sym sources L target ⟨q, atoms.map C10NaturalModeAtoms.nativeSymmetricAtom⟩).2
      rw [C10NaturalModeAtoms.conjunctionProbability_nativeSymmetric atoms hmode] at h
      simpa only [LiveRows.fraction, ↓reduceIte] using h

theorem parent (sym : SymmetricAccuracy) (thr : ThresholdAccuracy) :
    PCJ9eff70d512234a4c_Fixed.Certificate := by
  intro sources liveScale target q circuit pcpp mode ph P b denBits limits order entries
    hperm hmode hrecords hmass hcoeff htarget htpos hden hwidth
  have hcoeffOrder : ∀ m ∈ order,
      CompetitorMonomialProducts.positive m.coefficient < 2^b ∧
      CompetitorMonomialProducts.negative m.coefficient < 2^b ∧
      m.coefficient.den < 2^b :=
    fun m hm => hcoeff m (hperm.mem_iff.mpr hm)
  have hnonneg : 0 ≤ PCJ9eff70d512234a4c_Fixed.failure target := by
    unfold PCJ9eff70d512234a4c_Fixed.failure
    positivity
  have hnumeric : ∀ m ∈ order,
      (LiveRows.fraction sources liveScale target mode m.factors).1 < 2^b ∧
      (LiveRows.fraction sources liveScale target mode m.factors).2 < 2^b ∧
      0 < (LiveRows.fraction sources liveScale target mode m.factors).2 := by
    intro m hm
    let E := estimate sym thr sources liveScale target mode m.factors (hmode m hm)
    have hfit := E.numeric_fit (booleanMean_le_one _) htpos denBits b (hden m hm) hwidth
    exact ⟨hfit.1, hfit.2, E.positive⟩
  refine ⟨hnonneg, ?_, ?_, ?_, ?_⟩
  · intro m hm
    exact (estimate sym thr sources liveScale target mode m.factors
      (hmode m (hperm.mem_iff.mp hm))).accurate
  · have hepsilon : (0 : Real) <
        ((CompetitorRationalGap.estimationTolerance (constantsOf sources)
          (CompetitorRationalGap.zeta (constantsOf sources)) : Rat) : Real) := by
      exact_mod_cast (CompetitorRationalGap.full_error_budget (constantsOf sources)).1
    have hmassR : ((P.coefficientMass : Rat) : Real) ≤
        ((C10FamilyMass.siteMassBound limits.coefficientMassCap ph : Rat) : Real) := by
      exact_mod_cast hmass
    have hhalf := recip_mul_le_half hepsilon
      (show (0 : Real) ≤ ((target+1 : Nat) : Real) by positivity)
      (accuracyTarget_spec (constantsOf sources) limits ph (target+1)
        (htarget.trans (Nat.le_succ target)))
    exact (mul_le_mul_of_nonneg_left hmassR hnonneg).trans (hhalf.trans (by linarith))
  · refine ⟨order, hperm, ?_⟩
    apply hrecords.imp
    intro m e hrecord
    rcases hrecord with ⟨hc, hn, hd⟩
    constructor
    · rw [hc]
      exact coefficientEstimate_value m.coefficient
    · rw [hn, hd]
      rfl
  · clear hperm hmass hcoeff htarget hnonneg hmode hden
    revert hcoeffOrder hnumeric
    induction hrecords with
    | nil => simp
    | @cons m e ms es hr hrest ih =>
      intro hcOrder hnOrder z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · rcases hr with ⟨hc, hn, hd⟩
        obtain ⟨hp, hm, hcd⟩ := hcOrder m (by simp)
        obtain ⟨hnum, hden, hpos⟩ := hnOrder m (by simp)
        constructor
        · rw [hc]; exact hp
        · rw [hc]; exact hm
        · rw [hc]; exact hcd
        · rw [hc]; exact m.coefficient.pos
        · rw [hn]; exact hnum
        · rw [hd]; exact hden
        · rw [hd]; exact hpos
      · exact ih (fun m hm => hcOrder m (List.mem_cons_of_mem _ hm))
          (fun m hm => hnOrder m (List.mem_cons_of_mem _ hm)) z hz

end PCJa94fb905a93646cd
