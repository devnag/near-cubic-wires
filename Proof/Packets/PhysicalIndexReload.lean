import Proof.Packets.PhysicalCopyInto
import Proof.Packets.VectorCounterDecrement

/-! Reload a physical unary index from a resident padded word. The index
cursor is lowered from1 to0, R bits are copied, and the cursor is restored. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalIndexReload
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def slot {t : Nat} (target : Fin t) : Fin 1→Fin t := fun _=>target
def move {t : Nat} (target : Fin t) (d : HeadMove) :=
  RecoveryFocus.machine (slot target) (Completion.PhysicalDriverMoves.machine 1 d)
def machine {t : Nat} (width source target : Fin t) := Composition.machine (move target .left)
  (Composition.machine (PhysicalCopyInto.machine width source target) (move target .right))

theorem move_run {t : Nat} (target : Fin t) (d : HeadMove) (H : Fin t→Nat) (A : Fin t→List Bool) :
    Step (move target d) 1 H A (Function.update H target (d.apply (H target))) A := by
  have h:=Completion.PhysicalDriverMoves.run d (fun _ : Fin 1=>H target) (fun _=>A target)
  apply PhysicalFocusBoundary.focus h (slot target) (by intro i j _;exact Subsingleton.elim i j)
    H (Function.update H target (d.apply (H target))) A A
  · intro i;rfl
  · intro i;rfl
  · intro i;simp [slot,Function.update]
  · intro i;rfl
  · intro i away
    have hn : i≠target := by intro he;subst i;exact away 0 rfl
    exact ⟨by simp [Function.update,hn],rfl⟩

theorem run {t : Nat} (R : Nat) (width source target : Fin t)
    (hws : width≠source) (hwt : width≠target) (hst : source≠target)
    (H : Fin t→Nat) (A : Fin t→List Bool)
    (hw : H width=1) (hs : H source=0) (ht : H target=1)
    (hword : A width=UnaryTemplate.tape R) (hsl : (A source).length=R) (htl : (A target).length=R) :
    Step (machine width source target) (2*R+6) H A H (Function.update A target (A source)) := by
  have first:=move_run target .left H A
  simp only [ht,HeadMove.apply] at first
  have second:=PhysicalCopyInto.run R width source target hws hwt hst
    (Function.update H target 0) A
    (by simpa [Function.update,hwt] using hw) (by simpa [Function.update,hst] using hs)
    (by simp) hword hsl htl
  have third:=move_run target .right (Function.update H target 0) (Function.update A target (A source))
  simp only [Function.update_self,HeadMove.apply] at third
  have endH : Function.update (Function.update H target 0) target 1=H := by
    funext i
    by_cases hi : i=target
    · subst i;simp [ht]
    · simp [Function.update,hi]
  have h:=first.seq (second.seq (third.congr endH rfl))
  have fuel : 1+1+((2*R+2)+1+1)=2*R+6 := by omega
  rw [fuel] at h
  exact h

theorem padded_unary_index (C R : Nat) (h : C+2≤R) :
    ZeroPadding.pad R (UnaryTemplate.tape C)=ZeroPadding.pad R (CompareMachine.word C) :=
  VectorCounter.padded_template_word C R h

end
end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalIndexReload
