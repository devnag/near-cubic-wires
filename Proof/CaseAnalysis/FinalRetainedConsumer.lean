import Proof.CaseAnalysis.FinalGuardedStageConsumer
import Proof.CaseAnalysis.FinalRetainedPhaseFold

/-!
The retained C10 consumer uses the selected phase fold, actual clause driver,
and source-fixed head-aware tail. Accuracy is required only for monomials in
the actual phase. Entry and clause transitions keep their physical tapes,
heads and budgets explicit. No whole-worker run or Runtime is inferred.
-/
namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedConsumer
open NearCubicWires LocalBitMultitape ExtDecompositionBatch ComponentwisePolynomial
open RepairRepresentation SourceInterfaces RepairSource.CompetitorRationalGap
open RepairSource.CloseoutFinal RepairSource.VerifierDecoding
open CloseoutRowsOriginalSchedule CloseoutRowsEstimatorCoefficients.Stream
open CloseoutFinalC10Realizes CloseoutFinalC10WorkerFold
open RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section


/-- Exactly the tail's required literal public words and private blank cells. -/
theorem parked (widths : Phase → Nat) (estimates : Phase → CompetitorValidity.Estimate)
    (A : Fin 475 → List Bool)
    (hrec : ∀ ph, A (C10TailVerdict.scratchT ph)=recordWord (widths ph) (estimates ph) 1 1)
    (hwidth : ∀ ph j, A (C10TailSlotsUniform.widthSlotT ph j)=C10BodyWidths.widthWord (widths ph) j)
    (hblank : ∀ i : Fin 475, (15 ≤ i.val ∧ i.val < 102) ∨ 221 ≤ i.val → A i=[]) :
    C10TailVerdictUniform.ParkedThree' (widths .penalty) (widths .moment) (widths .clause)
      (estimates .penalty) (estimates .moment) (estimates .clause) (fun _ => 0) A := by
  have hb (i : Fin 475) (hi : 221 ≤ i.val) : A i=[] := hblank i (Or.inr hi)
  have phase (ph : Phase) : C10TailFeedDockUniform.PhaseParked ph (widths ph) (estimates ph) (fun _ => 0) A := by
    refine ⟨?_, rfl, fun _ => rfl, ?_, fun _ => rfl, ?_, fun _ => rfl, ?_,
      fun _ => rfl, ?_, fun _ => rfl, ?_, ?_, fun _ => rfl, ?_⟩
    · rw [C10TailVerdict.feedSlots_scratch]; exact hrec ph
    · intro j; exact hb _ (C10TailCompose.feedSlots_ge _ _ (C10TailVerdict.cmp_ge j))
    · intro j; exact hb _ (C10TailCompose.feedSlots_ge _ _ (C10TailVerdict.normA_ge j))
    · intro j; exact hb _ (C10TailCompose.feedSlots_ge _ _ (C10TailVerdict.normB_ge j))
    · intro j; exact hb _ (C10TailCompose.feedSlots_ge _ _ (C10TailVerdict.word_ge j))
    · exact (congrArg A (C10TailSlotsUniform.feedSlots_width (C10TailUniformSlots.phaseIndex ph) ph 0)).trans (hwidth ph 0)
    · exact (congrArg A (C10TailSlotsUniform.feedSlots_width (C10TailUniformSlots.phaseIndex ph) ph 1)).trans (hwidth ph 1)
    · intro j
      exact (congrArg A (C10TailSlotsUniform.feedSlots_private (C10TailUniformSlots.phaseIndex ph) ph j)).trans
        (hblank _ (Or.inl (C10TailSlotsUniform.privateSlotT_range ph j)))
  exact ⟨phase .penalty,phase .moment,phase .clause,hb _ (by decide),rfl,hb _ (by decide),rfl⟩

/-- The actual fixed tail at the selected retained layout. It preserves all
  phase records and widths and exports the decision at its actual final head. -/
theorem tail_run (sources : RepairSource.EightSources)
    (L B : Nat) (hL : 301 ≤ L) (hFresh : L+1154<B)
    (widths : Phase → Nat) (estimates : Phase → CompetitorValidity.Estimate)
    (H : Fin B → Nat) (A : Fin B → List Bool)
    (hvalid : ∀ ph, (estimates ph).Valid (widths ph))
    (hthreshold : ∀ ph, C10ThresholdWidths.thresholdWidth (constantsOf sources) ≤ widths ph)
    (hhead : ∀ i,H (CloseoutFinalC10RetainedPhaseFold.tailSlots L B hL hFresh i)=0)
    (hrec : ∀ ph, A (CloseoutFinalC10RetainedPhaseFold.tailSlots L B hL hFresh (C10TailVerdict.scratchT ph))=
      recordWord (widths ph) (estimates ph) 1 1)
    (hwidth : ∀ ph j, A (CloseoutFinalC10RetainedPhaseFold.tailSlots L B hL hFresh (C10TailSlotsUniform.widthSlotT ph j))=
      C10BodyWidths.widthWord (widths ph) j)
    (hblank : ∀ i : Fin 475, (15 ≤ i.val ∧ i.val < 102) ∨ 221 ≤ i.val →
      A (CloseoutFinalC10RetainedPhaseFold.tailSlots L B hL hFresh i)=[]) :
    let slots := CloseoutFinalC10RetainedPhaseFold.tailSlots L B hL hFresh
    ∃ H' A', Step (RecoveryFocus.machine slots (C10TailComposeUniform.tailMachine sources))
      (C10TailVerdictUniform.tbud (max (widths .penalty) (max (widths .moment) (widths .clause)))) H A H' A' ∧
      (readTapeBit (A' (slots C10TailVerdict.tailFlag)) (H' (slots C10TailVerdict.tailFlag))=true ↔
        (((estimates .penalty).value : Rat) : Real) ≤ C10Verdict.bound (constantsOf sources) .penalty ∧
        (((estimates .moment).value : Rat) : Real) ≤ C10Verdict.bound (constantsOf sources) .moment ∧
        C10Verdict.bound (constantsOf sources) .clause ≤ (((estimates .clause).value : Rat) : Real)) ∧
      (∀ ph, A' (slots (C10TailVerdict.scratchT ph))=A (slots (C10TailVerdict.scratchT ph))) ∧
      (∀ ph j, A' (slots (C10TailSlotsUniform.widthSlotT ph j))=A (slots (C10TailSlotsUniform.widthSlotT ph j))) ∧
      (∀ i, (∀ j, slots j ≠ i) → A' i=A i) := by
  classical
  let slots := CloseoutFinalC10RetainedPhaseFold.tailSlots L B hL hFresh
  have inj : Function.Injective slots := by
    intro i j he
    have hv := congrArg Fin.val he
    apply Fin.ext
    dsimp only [slots,CloseoutFinalC10RetainedPhaseFold.tailSlots] at hv
    split_ifs at hv <;> omega
  have hp := parked widths estimates (A ∘ slots) hrec hwidth hblank
  have hw := C10TailVerdictUniform.tailWidths'_of (constantsOf sources)
    (hthreshold .penalty) (hthreshold .moment) (hthreshold .clause)
  obtain ⟨TH,TA,hs,htest,hframe,hflag⟩ := C10TailComposeUniform.tail_spec_head sources
    (widths .penalty) (widths .moment) (widths .clause)
    (estimates .penalty) (estimates .moment) (estimates .clause)
    (hvalid .penalty) (hvalid .moment) (hvalid .clause) hw (fun _ => 0) (A ∘ slots) hp
  refine ⟨dockH slots H TH, install slots A TA, hs.dock slots inj H A hhead (by intro i;rfl), ?_, ?_, ?_, ?_⟩
  · rw [dockH_slot slots inj, hflag, install_slot slots inj]
    exact htest.trans (and_congr (C10TailComposeVerdict.bound_penalty (constantsOf sources) _)
      (and_congr (C10TailComposeVerdict.bound_moment (constantsOf sources) _)
        (C10TailComposeVerdict.bound_clause (constantsOf sources) _)))
  · intro ph
    exact (install_slot slots inj A TA _).trans (hframe _ (C10TailSlotsUniform.scratch_public ph))
  · intro ph j
    exact (install_slot slots inj A TA _).trans (hframe _ (C10TailSlotsUniform.width_public ph j))
  · intro i hi
    exact install_other slots A TA i hi

end
end NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedConsumer
