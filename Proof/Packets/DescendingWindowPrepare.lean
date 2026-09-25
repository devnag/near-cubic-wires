import Proof.CaseAnalysis.RowsMetadataCopy
import Proof.MachineModel.OrdinaryTransitionTapeZero
import Proof.Packets.DescendingWindowCounters

/-! The descending window's real per-degree setup: erase its old unary
coordinate, copy the retained degree, zero the framed complement, and
advance the retained inner count. Every local cursor returns to zero. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindowPrepare
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairOrdinary.SignedSortKey

def data (u : Nat) (left : List Bool) (b d C : Nat) : Fin 5→List Bool :=
  ![left,ZeroPadding.pad C (frame (binary u b)),ZeroPadding.pad C (CompareMachine.word d),
    List.replicate C true,List.replicate (C+1) false]
def clearSlots : Fin 3→Fin 5 := ![0,3,4]
def copySlots : Fin 4→Fin 5 := ![2,0,3,4]
def zeroSlots : Fin 2→Fin 5 := ![1,4]
def advanceSlots : Fin 1→Fin 5 := ![2]
noncomputable def clear := RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 1)
noncomputable def copy := RecoveryFocus.machine copySlots RecoveryBoundedTapeCopy.machine
noncomputable def zero := RecoveryFocus.machine zeroSlots TransitionTapeZero.machine
noncomputable def increment := Composition.machine
  (Composition.machine (Completion.PhysicalDriverMoves.machine 1 .right) VectorCounter.increment)
  (Completion.PhysicalDriverMoves.machine 1 .left)
noncomputable def advance := RecoveryFocus.machine advanceSlots increment
noncomputable def machine := Composition.machine (Composition.machine (Composition.machine clear copy) zero) advance

theorem increment_run (d C : Nat) : Step increment (2*d+6)
    (fun _=>0) (fun _=>ZeroPadding.pad C (CompareMachine.word d))
    (fun _=>0) (fun _=>ZeroPadding.pad C (CompareMachine.word (d+1))) := by
  have up := Completion.PhysicalDriverMoves.run .right (fun _ : Fin 1=>0)
    (fun _=>ZeroPadding.pad C (CompareMachine.word d))
  have middle := VectorCounter.increment_padded d C
  have down := Completion.PhysicalDriverMoves.run .left (fun _ : Fin 1=>1)
    (fun _=>ZeroPadding.pad C (CompareMachine.word (d+1)))
  have whole := (up.seq middle).seq down
  convert whole using 1 <;> first | rfl | omega

theorem clear_run (u : Nat) (left : List Bool) (b d C : Nat) (hl : left.length≤C) :
    Step clear (2*C+4) (fun _=>0) (data u left b d C)
      (fun _=>0) (data u (List.replicate C false) b d C) := by
  have localRun := Step.of_ready (RecoveryScratchErase.erase_ready C (C+1) (fun _ : Fin 1=>left)
    (by intro i;exact hl))
  simp only [max_self] at localRun
  apply PhysicalFocusBoundary.focus localRun clearSlots (by decide)
    (fun _=>0) (fun _=>0) _ _
  · intro i;rfl
  · intro i;fin_cases i <;> rfl
  · intro i;rfl
  · intro i;fin_cases i <;> rfl
  · intro i away;fin_cases i
    · exact False.elim (away 0 rfl)
    · exact ⟨rfl,rfl⟩
    · exact ⟨rfl,rfl⟩
    · exact False.elim (away 1 rfl)
    · exact False.elim (away 2 rfl)

theorem copy_run (u b d C : Nat) (hd : d+1≤C) :
    Step copy (2*C+4) (fun _=>0) (data u (List.replicate C false) b d C)
      (fun _=>0) (data u (ZeroPadding.pad C (CompareMachine.word d)) b d C) := by
  have localRun := Step.of_ready (CloseoutRowsMetadataCopy.copy_ready
    (ZeroPadding.pad C (CompareMachine.word d)) C (by simp [CompareMachine.word,hd]))
  apply PhysicalFocusBoundary.focus localRun copySlots (by decide)
    (fun _=>0) (fun _=>0) _ _
  · intro i;rfl
  · intro i;fin_cases i <;> rfl
  · intro i;rfl
  · intro i;fin_cases i <;> simp [copySlots,data,CloseoutRowsMetadataCopy.output,ZeroPadding.pad,CompareMachine.word]
    omega
  · intro i away;fin_cases i
    · exact False.elim (away 1 rfl)
    · exact ⟨rfl,rfl⟩
    · exact False.elim (away 0 rfl)
    · exact False.elim (away 2 rfl)
    · exact False.elim (away 3 rfl)

theorem binary_zero (u : Nat) : binary u 0=List.replicate u false := by
  induction u with
  | zero=>rfl
  | succ u ih=>simpa [binary,List.replicate_succ] using congrArg (List.cons false) ih

theorem zero_run (u : Nat) (left : List Bool) (b d C : Nat) (hu : 2*u≤C) :
    Step zero (4*u+4) (fun _=>0) (data u left b d C)
      (fun _=>0) (data u left 0 d C) := by
  have localRun := Step.of_ready (TransitionTapeZero.zero_ready (binary u b) (C+1) (by simp;omega))
  simp only [binary_length] at localRun
  rw [←binary_zero u] at localRun
  have padded := localRun.pad (![C,0] : Fin 2→Nat)
  apply PhysicalFocusBoundary.focus padded zeroSlots (by decide)
    (fun _=>0) (fun _=>0) _ _
  · intro i;rfl
  · intro i;fin_cases i
    · rfl
    · exact ZeroPadding.pad_zero _
  · intro i;rfl
  · intro i;fin_cases i
    · rfl
    · exact ZeroPadding.pad_zero _
  · intro i away;fin_cases i
    · exact ⟨rfl,rfl⟩
    · exact False.elim (away 0 rfl)
    · exact ⟨rfl,rfl⟩
    · exact ⟨rfl,rfl⟩
    · exact False.elim (away 1 rfl)

theorem advance_run (u : Nat) (left : List Bool) (b d C : Nat) :
    Step advance (2*d+6) (fun _=>0) (data u left b d C)
      (fun _=>0) (data u left b (d+1) C) := by
  apply PhysicalFocusBoundary.focus (increment_run d C) advanceSlots (by decide)
    (fun _=>0) (fun _=>0) _ _
  · intro i;rfl
  · intro i;fin_cases i;rfl
  · intro i;rfl
  · intro i;fin_cases i;rfl
  · intro i away;fin_cases i
    · exact ⟨rfl,rfl⟩
    · exact ⟨rfl,rfl⟩
    · exact False.elim (away 0 rfl)
    · exact ⟨rfl,rfl⟩
    · exact ⟨rfl,rfl⟩

theorem run (u : Nat) (left : List Bool) (b d C : Nat) (hl : left.length≤C)
    (hd : d+1≤C) (hu : 2*u≤C) :
    Step machine (4*C+4*u+2*d+21) (fun _=>0) (data u left b d C)
      (fun _=>0) (data u (ZeroPadding.pad C (CompareMachine.word d)) 0 (d+1) C) := by
  have whole := (((clear_run u left b d C hl).seq (copy_run u b d C hd)).seq
    (zero_run u (ZeroPadding.pad C (CompareMachine.word d)) b d C hu)).seq
    (advance_run u (ZeroPadding.pad C (CompareMachine.word d)) 0 d C)
  convert whole using 1 <;> first | rfl | omega

end PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindowPrepare
