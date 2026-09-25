import Proof.Packets.SrcRes284Pen
import Proof.SourceAssembly.AdmissionSource
import Proof.Packets.BudgetTableOnset

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires NearCubicWires.ComponentwisePolynomial LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown
open NearCubicWires.SourceParent
namespace NearCubicWires.SourceStart.Res284
open NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceSteps
noncomputable section

theorem clog_pow_le (w D : ℕ) : Nat.clog 2 ((w + 2)^D) ≤ D * (w + 2) := by
  apply Nat.clog_le_of_le_pow
  have h : w + 2 ≤ 2^(w+2) := (Nat.lt_two_pow_self (n := w + 2)).le
  calc (w + 2)^D ≤ (2^(w+2))^D := Nat.pow_le_pow_left h D
    _ = 2^(D * (w + 2)) := by rw [← pow_mul, Nat.mul_comm]

variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
  (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
  (hp : P1Independent.CappedLegalAdmission.passed sources p
    (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
    (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)

/-- **`h284`: the penalty entry's residue on 284 fits the query cache.** -/
theorem res284_le_capC
    (oracle : BooleanCircuit
      ((SelectedRecoveryIntegration.outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth n))
    (hcut : CloseoutWitnessPolicy.inputCutoff sources ≤ n)
    (hw : 2 * p.clauseDegree + 6 ≤ C10PartsSchedule.widthAt sources k n)
    (j : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (hj : j.val = 284) :
    (penaltyA0 sources p den hden k r scratch n x bits hp j).length ≤
      SourcePhase.capC sources k (PolynomialClock.ordinaryClock k) x oracle := by
  rw [penalty_284_len sources p den hden k r scratch n x bits hp j hj]
  have hc := clog_pow_le (C10PartsSchedule.widthAt sources k n) p.clauseDegree
  have hA : (req sources k (PolynomialClock.ordinaryClock k) x oracle).arity = C10PartsSchedule.widthAt sources k n :=
    Admission.req_arity sources k (PolynomialClock.ordinaryClock k) x oracle hcut
  have hcw : RepairSource.CloseoutLanguage.clauseWidth p.clauseDegree (C10PartsSchedule.widthAt sources k n) =
      Nat.clog 2 ((C10PartsSchedule.widthAt sources k n + 2)^p.clauseDegree) := rfl
  rw [hcw]
  unfold SourcePhase.capC PCPPQueryCachedBounds.capacity PCPPQueryCachedBounds.coefficient PCPPQueryCachedBounds.degree
  generalize hW : C10PartsSchedule.widthAt sources k n = w at hA hc hw ⊢
  generalize hM : (req sources k (PolynomialClock.ordinaryClock k) x oracle).circuit.size +
    (req sources k (PolynomialClock.ordinaryClock k) x oracle).arity = m
  have hwm : w ≤ m := by rw [← hM]; omega
  have h1 : (w + 1)^2 ≤ (m + 1)^(2 * max 10 (CloseoutLanguage.selectedPCPP sources).degree) :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have h2 : (m + 1)^(2 * max 10 (CloseoutLanguage.selectedPCPP sources).degree) ≤
      (10000 * ((CloseoutLanguage.selectedPCPP sources).coefficient + 131084)^2 + 1) *
        (m + 1)^(2 * max 10 (CloseoutLanguage.selectedPCPP sources).degree) :=
    Nat.le_mul_of_pos_left _ (by positivity)
  have h3 : 2 * (p.clauseDegree * (w + 2)) + 7 ≤ (w + 1)^2 := by nlinarith
  omega

/-- **The two windows hold past one onset.** -/
theorem res284_onset (D : ℕ) :
    ∃ n0, ∀ n, n0 ≤ n → CloseoutWitnessPolicy.inputCutoff sources ≤ n ∧ 2 * D + 6 ≤ C10PartsSchedule.widthAt sources k n := by
  obtain ⟨n1, h1⟩ := SourceBudget.widthAt_ge_eventually sources k (2 * D + 6)
  exact ⟨max n1 (CloseoutWitnessPolicy.inputCutoff sources), fun n hn =>
    ⟨le_of_max_le_right hn, h1 n (le_of_max_le_left hn)⟩⟩

end
end NearCubicWires.SourceStart.Res284

