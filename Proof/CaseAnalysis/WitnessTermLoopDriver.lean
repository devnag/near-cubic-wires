import Proof.CaseAnalysis.WitnessTermLoopData
import Proof.CaseAnalysis.WitnessTermRoundAll

/-! The actual canonical term count drives the complete term controller.
The accumulator state below is only proof bookkeeping extracted from its
same receipt; no second interpreter or coefficient pass is executed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermLoop
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section


def machine {s : ℕ} (circuit : Machine 1703 s) :=
  RepeatMachine.machine (TermRound.machine circuit) (fun _ bits=>bits 724)
def budget (cost count : ℕ) := count*(cost+3)+3

private theorem iterate_invariant {α : Type} (next : ℕ → α → Bool×α) (Inv : ℕ → α → Prop)
    (total : ℕ)
    (step : ∀ j<total,∀ x,Inv j x → (next j x).1=true → Inv (j+1) (next j x).2)
    (n pos : ℕ) (x : α) (hx : Inv pos x) (hbound : pos+n ≤ total)
    (hgood : (RepeatMachine.iterate (CountedReject.advance next) n (pos,x)).1=true) :
    (RepeatMachine.iterate (CountedReject.advance next) n (pos,x)).2.1=pos+n ∧
      Inv (pos+n) (RepeatMachine.iterate (CountedReject.advance next) n (pos,x)).2.2 := by
  induction n generalizing pos x with
  | zero => simpa only [RepeatMachine.iterate,Nat.add_zero] using And.intro (rfl : pos=pos) hx
  | succ n ih =>
    cases hp : (next pos x).1 with
    | false => simp only [RepeatMachine.iterate,CountedReject.advance,hp,Bool.false_eq_true,↓reduceIte] at hgood
    | true =>
      simp only [RepeatMachine.iterate,CountedReject.advance,hp,↓reduceIte] at hgood ⊢
      have hnext := step pos (by omega) x hx hp
      have h := ih (pos+1) (next pos x).2 hnext (by omega) hgood
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.TermLoop
