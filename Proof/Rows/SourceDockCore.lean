import Proof.MachineModel.Runs

/-! Source-generator wiring lemmas over the original Step/focus/padding
definitions. These names are separate from the full batch-layout module. -/
set_option autoImplicit false
set_option warningAsError true
namespace Completion.SourceDock
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound

theorem heads_existing {t u : Nat} (slots : Fin t→Fin u) (ambient : Fin u→Nat)
    (local' : Fin t→Nat) (h:∀j,ambient (slots j)=local' j) : dockH slots ambient local'=ambient := by
  classical
  funext i
  unfold dockH
  cases hp:RecoveryFocus.pick slots i with
  | none=>rfl
  | some j=>rw [←RecoveryFocus.slot_of_pick slots hp,h j]

theorem dock {t u s : Nat} {p : Machine t s} {n : Nat} {hin hout : Fin t→Nat}
    {tin tout : Fin t→List Bool} (h:Step p n hin tin hout tout)
    (slots : Fin t→Fin u) (hi:Function.Injective slots)
    (H : Fin u→Nat) (A : Fin u→List Bool)
    (hH:∀j,H (slots j)=hin j) (hA:∀j,A (slots j)=tin j) :
    Step (RecoveryFocus.machine slots p) n H A (dockH slots H hout) (install slots A tout) := by
  have hf:=h.focus slots hi H A
  rw [heads_existing slots H hin hH,install_existing slots A tin hA] at hf
  exact hf

theorem pad_template (cap k : Nat) (h:k+2≤cap) :
    ZeroPadding.pad cap (RepairSource.VerifierDecoding.CompareMachine.word k)=
      ZeroPadding.pad cap (UnaryTemplate.tape k) := by
  have hw:(RepairSource.VerifierDecoding.CompareMachine.word k).length=k+1:=by
    simp [RepairSource.VerifierDecoding.CompareMachine.word]
  have ht:UnaryTemplate.tape k=RepairSource.VerifierDecoding.CompareMachine.word k++[false]:=by
    simp [UnaryTemplate.tape,RepairSource.VerifierDecoding.CompareMachine.word]
  rw [ht]
  simp only [ZeroPadding.pad,hw,List.length_append,List.length_singleton,List.append_assoc]
  congr 1
  have he:cap-(k+1)=1+(cap-(k+1+1)):=by omega
  rw [he,List.replicate_add]
  rfl

end Completion.SourceDock
