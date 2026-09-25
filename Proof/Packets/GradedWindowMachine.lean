import Proof.Packets.GradedHalveLoop
import Proof.Packets.UnaryThird
import Proof.Packets.RawUnaryOffset
import Proof.Packets.PhysicalIndexReload

set_option autoImplicit false
set_option maxHeartbeats 850000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.GradedWindow
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def H (levelHead quotientHead : Nat) (i : Fin 13) : Nat :=
  if i=6 then levelHead else if i=7 then quotientHead else if i=12 then 1 else 0
def A (R root level value quotient out : Nat) (i : Fin 13) : List Bool :=
  if i=0 then ZeroPadding.pad R (List.replicate value true)
  else if i=7 then ZeroPadding.pad R (CompareMachine.word quotient)
  else if i=9 then ZeroPadding.pad R (CompareMachine.word out)
  else (![[],List.replicate R false,List.replicate R false,
    List.replicate R false,List.replicate (R+1) false,List.replicate R true,
    ZeroPadding.pad R (CompareMachine.word level),[],List.replicate R false,[],List.replicate R false,
    ZeroPadding.pad R (List.replicate root true),UnaryTemplate.tape R] : Fin 13→List Bool) i
def copyRoot := PhysicalCopyInto.machine (12 : Fin 13) 11 0
def thirdSlots : Fin 3→Fin 13 := ![6,7,8]
def third := RecoveryFocus.machine thirdSlots UnaryThird.returned
def floor := Composition.machine (PhysicalIndexReload.move (6 : Fin 13) .left)
  (Composition.machine third (PhysicalIndexReload.move (6 : Fin 13) .right))
def halfSlots : Fin 7→Fin 13 := ![0,1,2,3,4,5,7]
def halves := RecoveryFocus.machine halfSlots GradedHalveLoop.machine
def offsetSlots : Fin 3→Fin 13 := ![0,9,10]
def offset := RecoveryFocus.machine offsetSlots (RawUnaryOffset.returned 64)
def clearValue := PhysicalCopyInto.machine (12 : Fin 13) 1 0
def clearQuotient := PhysicalCopyInto.machine (12 : Fin 13) 1 7

theorem zero_count (R : Nat) (hr : 1≤R) : ZeroPadding.pad R (CompareMachine.word 0)=List.replicate R false := by
  simp only [ZeroPadding.pad,CompareMachine.word,List.replicate_zero,List.length_singleton]
  calc
    [false]++List.replicate (R-1) false=List.replicate (1+(R-1)) false := by
      rw [List.replicate_add];rfl
    _=List.replicate R false := by congr 1;omega

theorem copy_root (R root level : Nat) (hr : root≤R) :
    Step copyRoot (2*R+2) (H 1 0) (A R root level 0 0 0) (H 1 0) (A R root level root 0 0) := by
  have h:=PhysicalCopyInto.run R (12 : Fin 13) 11 0 (by decide) (by decide) (by decide)
    (H 1 0) (A R root level 0 0 0) rfl rfl rfl rfl
    (by simp [A,ZeroPadding.pad_length,Nat.max_eq_left hr]) (by simp [A,ZeroPadding.pad_length])
  exact h.congr rfl (by funext i;fin_cases i <;>simp [A,Function.update])

theorem third_run (R root level value out : Nat) (hr : level+2≤R) :
    Step third (2*level+6) (H 0 0) (A R root level value 0 out)
      (H 0 0) (A R root level value (level/3) out) := by
  apply PhysicalFocusBoundary.focus (UnaryThird.ready R level hr) thirdSlots (by decide)
    (H 0 0) (H 0 0) _ _
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i
    · rfl
    · change ZeroPadding.pad R []=ZeroPadding.pad R (CompareMachine.word 0)
      rw [zero_count R (by omega)];rfl
    · rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i away;fin_cases i <;>first | exact ⟨rfl,rfl⟩ | exact False.elim (away 1 rfl)

theorem floor_run (R root level value out : Nat) (hr : level+2≤R) :
    Step floor (2*level+10) (H 1 0) (A R root level value 0 out)
      (H 1 0) (A R root level value (level/3) out) := by
  have first:=PhysicalIndexReload.move_run (6 : Fin 13) .left (H 1 0) (A R root level value 0 out)
  have first':Step (PhysicalIndexReload.move (6 : Fin 13) .left) 1
      (H 1 0) (A R root level value 0 out) (H 0 0) (A R root level value 0 out) :=
    first.congr (by funext i;fin_cases i <;>rfl) rfl
  have last:=PhysicalIndexReload.move_run (6 : Fin 13) .right (H 0 0) (A R root level value (level/3) out)
  have last':Step (PhysicalIndexReload.move (6 : Fin 13) .right) 1
      (H 0 0) (A R root level value (level/3) out) (H 1 0) (A R root level value (level/3) out) :=
    last.congr (by funext i;fin_cases i <;>rfl) rfl
  have h:=first'.seq ((third_run R root level value out hr).seq last')
  have hf:1+1+((2*level+6)+1+1)=2*level+10:=by omega
  rw [hf] at h;exact h

theorem halves_run (R root level value Q out : Nat) (hr : value+1≤R) :
    Step halves (GradedHalveLoop.budget R Q) (H 1 1) (A R root level value Q out)
      (H 1 1) (A R root level (GradedHalveRound.halve^[Q] value) Q out) := by
  have h:=(GradedHalveLoop.run R value Q hr).pad (![0,0,0,0,0,0,R] : Fin 7→Nat)
  apply PhysicalFocusBoundary.focus h halfSlots (by decide) (H 1 1) (H 1 1) _ _
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>simp [halfSlots,GradedHalveLoop.data,GradedHalveRound.layout,A] <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>simp [halfSlots,GradedHalveLoop.data,GradedHalveRound.layout,A] <;>rfl
  · intro i away;fin_cases i <;>first | exact ⟨rfl,rfl⟩ | exact False.elim (away 0 rfl)

theorem offset_run (R root level value Q : Nat) (hr : value+67≤R) :
    Step offset (2*value+136) (H 1 0) (A R root level value Q 0)
      (H 1 0) (A R root level value Q (64+value)) := by
  have h:=RawUnaryOffset.ready 64 R value hr
  have hf : 2*value+2*64+8=2*value+136 := by omega
  rw [hf] at h
  apply PhysicalFocusBoundary.focus h offsetSlots (by decide) (H 1 0) (H 1 0) _ _
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i
    · rfl
    · change ZeroPadding.pad R []=ZeroPadding.pad R (CompareMachine.word 0)
      rw [zero_count R (by omega)];rfl
    · rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i away;fin_cases i <;>first | exact ⟨rfl,rfl⟩ | exact False.elim (away 1 rfl)

theorem clear_value (R root level value Q out : Nat) (hr : value≤R) :
    Step clearValue (2*R+2) (H 1 0) (A R root level value Q out)
      (H 1 0) (A R root level 0 Q out) := by
  have h:=PhysicalCopyInto.run R (12 : Fin 13) 1 0 (by decide) (by decide) (by decide)
    (H 1 0) (A R root level value Q out) rfl rfl rfl rfl
    (by simp [A]) (by simp [A,ZeroPadding.pad_length,Nat.max_eq_left hr])
  exact h.congr rfl (by funext i;fin_cases i <;>simp [A,Function.update,ZeroPadding.pad])

theorem clear_quotient (R root level value Q out : Nat) (hr : Q+1≤R) :
    Step clearQuotient (2*R+2) (H 1 0) (A R root level value Q out)
      (H 1 0) (A R root level value 0 out) := by
  have h:=PhysicalCopyInto.run R (12 : Fin 13) 1 7 (by decide) (by decide) (by decide)
    (H 1 0) (A R root level value Q out) rfl rfl rfl rfl
    (by simp [A]) (by simp [A,ZeroPadding.pad_length,CompareMachine.word];omega)
  exact h.congr rfl (by funext i;fin_cases i <;>simp [A,Function.update,zero_count R (by omega)])

end
end PCJ9eff70d512234a4c_Fixed.Materializer.GradedWindow
