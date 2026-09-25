import Proof.Packets.IdentityCodeLoop
import Proof.Packets.PhysicalCounterCopy
import Proof.Packets.WindowSeedClear
import Proof.Packets.NativeIndexedCost

/-! Closed reusable identity cache producer. It physically clears its two
private tapes, copies the retained actual count, emits every descending code,
and returns the output cursor. Blank and previously backed private tapes use
the same entry theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.IdentityCodeCache
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def H (indexHead pos : Nat) : Fin 6→Nat := ![indexHead,pos,1,1,0,0]
def A (R N : Nat) (index out : List Bool) : Fin 6→List Bool :=
  ![index,out,ZeroPadding.pad R (CompareMachine.word N),UnaryTemplate.tape R,
    List.replicate R true,List.replicate (R+3) false]
def zero (R : Nat) := List.replicate R false
def clearSlots : Fin 4→Fin 6 := ![0,1,4,5]
def backSlots : Fin 2→Fin 6 := ![3,1]
def clear := RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 2)
def up := PhysicalIndexReload.move (0 : Fin 6) .right
def down := PhysicalIndexReload.move (0 : Fin 6) .left
def copy := PhysicalCounterCopy.machine (t:=6) 3 2 0
def loop := TapeEmbedding.machine 3 IdentityCodeLoop.machine
def back := RecoveryFocus.machine backSlots Completion.PhysicalBoundedLeftRewind.machine
def machine := Composition.machine clear (Composition.machine up (Composition.machine copy
  (Composition.machine loop (Composition.machine back down))))
def budget (R N : Nat) := 6*R+IdentityCodeLoop.budget N+23

theorem clear_run (R N : Nat) (index out : List Bool)
    (hi : index.length≤R) (ho : out.length≤R) :
    Step clear (2*R+4) (H 0 0) (A R N index out) (H 0 0) (A R N (zero R) (zero R)) := by
  have h:=Step.of_ready (RecoveryScratchErase.erase_ready R (R+3)
    (![index,out] : Fin 2→List Bool) (by intro i;fin_cases i <;>assumption))
  have he:max (R+3) (R+1)=R+3:=by omega
  rw [he] at h
  apply PhysicalFocusBoundary.focus h clearSlots (by decide)
    (H 0 0) (H 0 0) (A R N index out) (A R N (zero R) (zero R))
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i away;fin_cases i <;>first | exact ⟨rfl,rfl⟩ | exact False.elim (away 0 rfl) | exact False.elim (away 1 rfl)

theorem up_run (R N : Nat) (index out : List Bool) :
    Step up 1 (H 0 0) (A R N index out) (H 1 0) (A R N index out) := by
  have h:=PhysicalIndexReload.move_run (0 : Fin 6) .right (H 0 0) (A R N index out)
  exact h.congr (by funext i;fin_cases i <;>rfl) rfl

theorem down_run (R N : Nat) (index out : List Bool) :
    Step down 1 (H 1 0) (A R N index out) (H 0 0) (A R N index out) := by
  have h:=PhysicalIndexReload.move_run (0 : Fin 6) .left (H 1 0) (A R N index out)
  exact h.congr (by funext i;fin_cases i <;>rfl) rfl

theorem copy_run (R N : Nat) (hcap : N+1≤R) :
    Step copy (2*R+10) (H 1 0) (A R N (zero R) (zero R))
      (H 1 0) (A R N (ZeroPadding.pad R (CompareMachine.word N)) (zero R)) := by
  have h:=PhysicalCounterCopy.run R (3 : Fin 6) 2 0 (by decide) (by decide) (by decide)
    (H 1 0) (A R N (zero R) (zero R)) rfl rfl rfl rfl
    (by simp [A,CompareMachine.word,ZeroPadding.pad_length,hcap]) (by simp [A,zero])
  exact h.congr rfl (by funext i;fin_cases i <;>rfl)

theorem loop_run (R N : Nat) (hcap : N+1≤R) :
    Step loop (IdentityCodeLoop.budget N)
      (H 1 0) (A R N (ZeroPadding.pad R (CompareMachine.word N)) (zero R))
      (H 1 (IdentityCodeLoop.stream N).length)
      (A R N (zero R) (ZeroPadding.pad R (IdentityCodeLoop.stream N))) := by
  have h:=((IdentityCodeLoop.run R N [] hcap).pad (![0,R,R] : Fin 3→Nat)).embed
    (![1,0,0] : Fin 3→Nat)
    (![UnaryTemplate.tape R,List.replicate R true,List.replicate (R+3) false] : Fin 3→List Bool)
  have hz : ZeroPadding.pad R (CompareMachine.word 0)=zero R := by
    change ZeroPadding.pad R (List.replicate 1 false)=List.replicate R false
    rw [Rewind.Workspace.pad_zeros,Nat.max_eq_left (by omega)]
  have hn : ZeroPadding.pad R []=zero R := by simp [ZeroPadding.pad,zero]
  convert h using 1 <;>first | rfl |
    (funext i;fin_cases i <;>simp [H,A,IdentityCodeLoop.H,IdentityCodeLoop.A,
      Fin.addCases,ZeroPadding.pad_zero,hz,hn])

theorem back_run (R N : Nat) (hstream : (IdentityCodeLoop.stream N).length≤R) :
    Step back (2*R+2) (H 1 (IdentityCodeLoop.stream N).length)
      (A R N (zero R) (ZeroPadding.pad R (IdentityCodeLoop.stream N)))
      (H 1 0) (A R N (zero R) (ZeroPadding.pad R (IdentityCodeLoop.stream N))) := by
  obtain ⟨r,rr,rf,_⟩:=Completion.PhysicalBoundedLeftRewind.run R
    (IdentityCodeLoop.stream N).length (ZeroPadding.pad R (IdentityCodeLoop.stream N)) hstream
  have h:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  apply PhysicalFocusBoundary.focus h backSlots (by decide)
    (H 1 (IdentityCodeLoop.stream N).length) (H 1 0)
    (A R N (zero R) (ZeroPadding.pad R (IdentityCodeLoop.stream N)))
    (A R N (zero R) (ZeroPadding.pad R (IdentityCodeLoop.stream N)))
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i away;fin_cases i <;>first | exact ⟨rfl,rfl⟩ | exact False.elim (away 1 rfl)

theorem run (R N : Nat) (index out : List Bool)
    (hi : index.length≤R) (ho : out.length≤R) (hcap : N+1≤R)
    (hstream : (IdentityCodeLoop.stream N).length≤R) :
    Step machine (budget R N) (H 0 0) (A R N index out)
      (H 0 0) (A R N (zero R) (ZeroPadding.pad R (IdentityCodeLoop.stream N))) := by
  have all:=(clear_run R N index out hi ho).seq ((up_run R N _ _).seq
    ((copy_run R N hcap).seq ((loop_run R N hcap).seq
      ((back_run R N hstream).seq (down_run R N _ _)))))
  have fuel : (2*R+4)+1+(1+1+((2*R+10)+1+(IdentityCodeLoop.budget N+1+((2*R+2)+1+1))))=
      budget R N := by unfold budget;omega
  simpa only [machine,fuel] using all

end
end PCJ9eff70d512234a4c_Fixed.Materializer.IdentityCodeCache
