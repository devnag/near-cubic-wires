import Proof.Packets.WalkTranscriptColumnController

/-! First-plus-remaining composition: consume the already extracted zero
column once, then run the retained population-counted worker on columns
one through population.  The first consumer cannot touch the count master. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true
namespace Theorem25Completion.WalkTranscriptColumnController
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
noncomputable section

def first {s : Nat} (consumer : Machine 471 s) :=
  RecoveryFocus.machine slots (TapeEmbedding.machine 1 consumer)
def firstThenRemaining {s t : Nat} (consumer : Machine 471 s) (worker : Machine 471 t) :=
  Composition.machine (first consumer) (machine worker)

private theorem worker_away_driver (i : Fin 471) : slots (i.castAdd 1)≠29 := by
  intro he
  have hv:=congrArg slots he
  rw [slots_twice] at hv
  have hi:=i.isLt
  have hn:=congrArg Fin.val hv
  change i.val=471 at hn
  omega

private theorem first_heads (H : Fin 471→Nat) (j : Fin 472) :
    (Fin.addCases (m:=471) (n:=1) (motive:=fun _=>Nat) H (fun _=>0)) j=
      Function.update (heads H) 29 0 (slots j) := by
  refine Fin.addCases (m:=471) (n:=1) (fun i=>?_) (fun i=>?_) j
  · rw [Function.update_of_ne (worker_away_driver i)]
    simp only [heads,slots_twice,Fin.addCases_left]
  · fin_cases i;rfl

theorem first_run {s : Nat} (consumer : Machine 471 s) (fuel R M : Nat)
    (H K : Fin 471→Nat) (A B : Fin 471→List Bool)
    (run : Step consumer fuel H A K B) :
    Step (first consumer) fuel (Function.update (heads H) 29 0) (tapes R M A)
      (Function.update (heads K) 29 0) (tapes R M B) := by
  have framed:=run.embed (fun _ : Fin 1=>0) (fun _=>ZeroPadding.pad R (CompareMachine.word M))
  apply PhysicalFocusBoundary.focus framed slots slots_injective
    (Function.update (heads H) 29 0) (Function.update (heads K) 29 0) (tapes R M A) (tapes R M B)
  · exact first_heads H
  · intro j;simp only [tapes,slots_twice]
  · exact first_heads K
  · intro j;simp only [tapes,slots_twice]
  · intro i away;exact False.elim (away (slots i) (slots_twice i))

end
end Theorem25Completion.WalkTranscriptColumnController
