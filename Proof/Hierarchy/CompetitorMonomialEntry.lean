import Proof.Hierarchy.CompetitorMonomialColdClear

/-! Whole bulk monomial producer from blank work tapes and physical record,
width/capacity/count inputs. One paid outer rewind resets both global
cursors only after the entire stream has been emitted. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMonomialEntry
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding CompetitorMonomialStream CompetitorReusableDecision CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def outerSlots (j : Fin 88) : Fin 89 := j.castAdd 1
def extendTapes (tapes : Fin 88 → List Bool) (n : ℕ) : Fin 89 → List Bool :=
  Fin.addCases (m := 88) (n := 1) (motive := fun _ => List Bool) tapes (fun _ => CompareMachine.word n)
noncomputable def bootProgram := RecoveryFocus.machine outerSlots (clearProgram workSlot)
def loopHeads : Fin 89 → ℕ := fun i => if i.val=88 then 1 else 0
def enter : Machine 89 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun _ => none,fun i => if i.val=88 then .right else .stay⟩ else none
noncomputable def tailProgram := Composition.machine enter loopProgram
noncomputable def program := Composition.machine bootProgram tailProgram
def budget (t n : ℕ) := loopBudget t n+2*capacity t+7

theorem outer_injective : Function.Injective outerSlots := by
  intro i j h
  exact Fin.ext (congrArg (fun a : Fin 89 => a.val) h)

theorem enter_run (tapes : Fin 89 → List Bool) :
    ∃ r : ExecutionReceipt 89 2,run enter 1 tapes=some r ∧ r.final=⟨1,loopHeads,tapes⟩ ∧ r.steps=1 := by
  have hstep : step enter (initialConfiguration enter tapes)=some (⟨1,loopHeads,tapes⟩ : Configuration 89 2) := by
    simp [step,enter,initialConfiguration]
    apply configuration_ext
    · rfl
    · funext i
      by_cases hi : i.val=88 <;> simp [applyAction,loopHeads,hi,HeadMove.apply]
    · rfl
  exact (Timed.single (by rfl) hstep).run (by rfl)

noncomputable def machine := Rewind.machine program
def readyBudget (t n : ℕ) := 2*budget t n+2

end NearCubicWires.RepairOrdinary.CompetitorMonomialEntry
