import Proof.CaseAnalysis.FinalSiteRoundPorts
import Proof.CaseAnalysis.RowsEstimatorParityCounter

/-! The physical record/count append segment of a C.10 site round.

The local record is an explicit produced-input precondition. The same fixed
four-tape machine appends its six fields to an arbitrary existing stream and
increments the existing unary record count. It returns the record cursor and
the same padded reset log, so a second operation reuses both tapes literally.
The copy's 40*b+56 includes its cursor restore; the counter pays 2*n+2; their
composition pays one bridge step. No empty-scratch restoration is assumed.

This segment starts/ends with the stream at its append cursor and the count
at head 1. The enclosing hsite starts/ends with ALL heads at 0. Its seek/rewind
and actual record producer are still separate typed obligations; this file
does not assert hsite or supply those operands for free.
-/

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10SiteRoundPortAppend

open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound
open RepairSource.VerifierDecoding
open CloseoutRowsEstimatorCoefficients

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (out : List Bool) : Fin 4 → ℕ := ![0, out.length, 0, 1]

def data (payload out : List Bool) (logSize count : ℕ) : Fin 4 → List Bool :=
  ![payload, out, List.replicate logSize false, CompareMachine.word count]

def countSlot (_ : Fin 1) : Fin 4 := 3

theorem countSlot_injective : Function.Injective countSlot := by decide

noncomputable def machine := Composition.machine
  (TapeEmbedding.machine 1 CloseoutRowsEstimator.AppendCopy.machine)
  (RecoveryFocus.machine countSlot CloseoutRowsEstimatorParity.Counter.machine)

def budget (width count : ℕ) : ℕ := (40 * width + 56) + 1 + (2 * count + 2)

theorem count_heads (out : List Bool) :
    dockH countSlot (heads out) (fun _ : Fin 1 => 1) = heads out := by
  apply dockH_existing
  intro j
  rfl

theorem install_count (payload out : List Bool) (logSize oldCount newCount : ℕ) :
    install countSlot (data payload out logSize oldCount)
      (fun _ : Fin 1 => CompareMachine.word newCount) = data payload out logSize newCount := by
  funext i
  fin_cases i
  · exact install_other countSlot _ _ 0 (by intro j; fin_cases j; decide)
  · exact install_other countSlot _ _ 1 (by intro j; fin_cases j; decide)
  · exact install_other countSlot _ _ 2 (by intro j; fin_cases j; decide)
  · exact install_slot countSlot countSlot_injective _ _ 0

/-- A complete physical append of one supplied record and its unary count. -/
theorem append_step (width numerator denominator padding logSize count : ℕ)
    (coefficient : CompetitorValidity.Estimate) (out : List Bool)
    (hlog : 20 * width + 27 ≤ logSize) :
    let payload := ZeroPadding.pad padding (Stream.recordWord width coefficient numerator denominator)
    let next := out ++ Stream.recordWord width coefficient numerator denominator
    Step machine (budget width count) (heads out) (data payload out logSize count)
      (heads next) (data payload next logSize (count + 1)) := by
  dsimp only
  obtain ⟨r, hr, hh, ht, hs⟩ := CloseoutRowsEstimator.AppendPadded.run
    width coefficient numerator denominator padding logSize out hlog
  have raw : Step CloseoutRowsEstimator.AppendCopy.machine (40 * width + 56)
      ![0, out.length, 0]
      ![ZeroPadding.pad padding (Stream.recordWord width coefficient numerator denominator),
        out, List.replicate logSize false]
      ![0, (out ++ Stream.recordWord width coefficient numerator denominator).length, 0]
      ![ZeroPadding.pad padding (Stream.recordWord width coefficient numerator denominator),
        out ++ Stream.recordWord width coefficient numerator denominator,
        List.replicate logSize false] := ⟨r, hr, hh, ht, hs⟩
  have embedded := raw.embed (fun _ : Fin 1 => 1) (fun _ : Fin 1 => CompareMachine.word count)
  have first : Step (TapeEmbedding.machine 1 CloseoutRowsEstimator.AppendCopy.machine)
      (40 * width + 56) (heads out)
      (data (ZeroPadding.pad padding (Stream.recordWord width coefficient numerator denominator))
        out logSize count)
      (heads (out ++ Stream.recordWord width coefficient numerator denominator))
      (data (ZeroPadding.pad padding (Stream.recordWord width coefficient numerator denominator))
        (out ++ Stream.recordWord width coefficient numerator denominator) logSize count) := by
    refine (embedded.congr_in ?_ ?_).congr ?_ ?_
    all_goals funext i; fin_cases i <;> rfl
  have counted := (CloseoutRowsEstimatorParity.Counter.increment_run count).focus
    countSlot countSlot_injective
    (heads (out ++ Stream.recordWord width coefficient numerator denominator))
    (data (ZeroPadding.pad padding (Stream.recordWord width coefficient numerator denominator))
      (out ++ Stream.recordWord width coefficient numerator denominator) logSize count)
  have second := (counted.congr_in (count_heads _) (install_count _ _ _ _ _)).congr
    (count_heads _) (install_count _ _ _ _ _)
  exact first.seq second

def twiceBudget (width count : ℕ) : ℕ := budget width count + 1 + budget width (count + 1)

theorem twiceBudget_eq (width count : ℕ) :
    twiceBudget width count = 80 * width + 4 * count + 121 := by
  unfold twiceBudget budget
  omega


end NearCubicWires.RepairOrdinary.CloseoutFinalC10SiteRoundPortAppend
