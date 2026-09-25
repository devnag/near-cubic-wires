import Proof.Packets.WalkTranscriptColumnArena

/-! Use the existing cold population word as the remaining-candidate driver.
A fixed tape permutation moves worker port 29 (the output bank) to the new
last tape and exposes the actual old master at 29 only to RepeatMachine.
The master is raised physically once and is returned to head one. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkTranscriptColumnController
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
noncomputable section

def slots (i : Fin 472) : Fin 472 := if i=29 then 471 else if i=471 then 29 else i

theorem slots_twice (i : Fin 472) : slots (slots i)=i := by
  by_cases h : i=29
  · subst i;rfl
  by_cases k : i=471
  · subst i;rfl
  · simp [slots,h,k]

theorem slots_injective : Function.Injective slots := by
  intro i j he
  have h:=congrArg slots he
  simpa only [slots_twice] using h

def heads (H : Fin 471 → Nat) : Fin 472 → Nat :=
  fun i=>(Fin.addCases (m:=471) (n:=1) (motive:=fun _=>Nat) H (fun _=>1)) (slots i)
def tapes (R M : Nat) (A : Fin 471 → List Bool) : Fin 472 → List Bool :=
  fun i=>(Fin.addCases (m:=471) (n:=1) (motive:=fun _=>List Bool) A
    (fun _=>ZeroPadding.pad R (CompareMachine.word M))) (slots i)

theorem driver_heads (H : Fin 471 → Nat) : heads H 29=1 := rfl
theorem result_tapes (R M : Nat) (A : Fin 471 → List Bool) : tapes R M A 471=A 29 := rfl

def remaining {s : Nat} (worker : Machine 471 s) :=
  RecoveryFocus.machine slots (RepeatMachine.machine worker (fun _ _=>true))
def machine {s : Nat} (worker : Machine 471 s) :=
  Composition.machine (PhysicalIndexReload.move (29 : Fin 472) .right) (remaining worker)
def budget (M E : Nat) := M*(E+3)+5

private theorem padded_tapes (R M : Nat) (A : Fin 471 → List Bool) :
    (fun i=>ZeroPadding.pad
      ((Fin.addCases (m:=471) (n:=1) (motive:=fun _=>Nat) (fun _=>0) (fun _=>R)) i)
      ((Fin.addCases (m:=471) (n:=1) (motive:=fun _=>List Bool) A (fun _=>CompareMachine.word M)) i))=
    Fin.addCases A (fun _ : Fin 1=>ZeroPadding.pad R (CompareMachine.word M)) := by
  funext i
  refine Fin.addCases (m:=471) (n:=1) (fun j=>?_) (fun j=>?_) i
  · simp only [Fin.addCases_left,ZeroPadding.pad_zero]
  · simp only [Fin.addCases_right]

/-- This compositional adapter consumes the actual padded N-1 word.  Its
body premise is discharged by the concrete column/majority/reset worker. -/
theorem remaining_run {s : Nat} (worker : Machine 471 s) (R M E : Nat)
    (H : Nat → Fin 471 → Nat) (A : Nat → Fin 471 → List Bool)
    (step : ∀i,i<M→Step worker E (H i) (A i) (H (i+1)) (A (i+1))) :
    Step (remaining worker) (M*(E+3)+3) (heads (H 0)) (tapes R M (A 0))
      (heads (H M)) (tapes R M (A M)) := by
  have localRun := (PhysicalRepeatStep.run worker M E H A step).pad
    (Fin.addCases (m:=471) (n:=1) (motive:=fun _=>Nat) (fun _=>0) (fun _=>R))
  rw [padded_tapes,padded_tapes] at localRun
  apply PhysicalFocusBoundary.focus localRun slots slots_injective
    (heads (H 0)) (heads (H M)) (tapes R M (A 0)) (tapes R M (A M))
  · intro j;simp only [heads,slots_twice]
  · intro j;simp only [tapes,slots_twice]
  · intro j;simp only [heads,slots_twice]
  · intro j;simp only [tapes,slots_twice]
  · intro i away;exact False.elim (away (slots i) (slots_twice i))

/-- The retained master's initial head zero is changed by a real move.
No counter copy, free driver, or worker/driver tape alias is required. -/
theorem run {s : Nat} (worker : Machine 471 s) (R M E : Nat)
    (H : Nat → Fin 471 → Nat) (A : Nat → Fin 471 → List Bool)
    (step : ∀i,i<M→Step worker E (H i) (A i) (H (i+1)) (A (i+1))) :
    Step (machine worker) (budget M E)
      (Function.update (heads (H 0)) 29 0) (tapes R M (A 0))
      (heads (H M)) (tapes R M (A M)) := by
  have first := PhysicalIndexReload.move_run (29 : Fin 472) .right
    (Function.update (heads (H 0)) 29 0) (tapes R M (A 0))
  have restore : Function.update (Function.update (heads (H 0)) 29 0) 29
      (HeadMove.right.apply (Function.update (heads (H 0)) 29 0 29))=heads (H 0) := by
    funext i
    by_cases hi : i=29
    · subst i;simp only [Function.update_self,HeadMove.apply];exact (driver_heads (H 0)).symm
    · simp only [Function.update_of_ne hi]
  rw [restore] at first
  have whole := first.seq (remaining_run worker R M E H A step)
  simpa only [machine,budget,show 1+1+(M*(E+3)+3)=M*(E+3)+5 by omega] using whole

end
end Theorem25Completion.WalkTranscriptColumnController
