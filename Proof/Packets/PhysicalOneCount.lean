import Proof.Packets.MaskConstant
import Proof.Rows.PhysicalDriverMoves

/-! Generate the one-monomial count in a physically allocated zero bank,
returning the actual count cursor to zero. -/
set_option autoImplicit false
set_option maxHeartbeats 220000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalOneCount
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

noncomputable def machine := Composition.machine (MaskConstant.countMachine true)
  (Completion.PhysicalDriverMoves.machine 1 .left)

theorem run (R : Nat) :
    Step machine 4 (fun _=>0) (fun _=>List.replicate R false)
      (fun _=>0) (fun _=>ZeroPadding.pad R (CompareMachine.word 1)) := by
  obtain ⟨r,hr,hf,_⟩:=MaskConstant.count_run true
  have first:=(Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)).pad
    (fun _ : Fin 1=>R)
  have second:=Completion.PhysicalDriverMoves.run .left (fun _ : Fin 1=>1)
    (fun _=>ZeroPadding.pad R (CompareMachine.word 1))
  have h:=first.seq second
  simpa [machine,MaskConstant.countCfg,ZeroPadding.pad,HeadMove.apply] using h

def slots {t : Nat} (target : Fin t) : Fin 1→Fin t := fun _=>target
noncomputable def into {t : Nat} (target : Fin t) := RecoveryFocus.machine (slots target) machine

theorem into_run {t : Nat} (R : Nat) (target : Fin t) (H : Fin t→Nat) (A : Fin t→List Bool)
    (hh : H target=0) (ha : A target=List.replicate R false) :
    Step (into target) 4 H A H (Function.update A target (ZeroPadding.pad R (CompareMachine.word 1))) := by
  apply PhysicalFocusBoundary.focus (run R) (slots target) (by intro i j _;exact Subsingleton.elim i j)
    H H A (Function.update A target (ZeroPadding.pad R (CompareMachine.word 1)))
  · intro i;exact hh.symm
  · intro i;exact ha.symm
  · intro i;exact hh.symm
  · intro i;simp [slots]
  · intro i away
    have hn : i≠target := by intro he;subst i;exact away 0 rfl
    exact ⟨rfl,by simp [Function.update,hn]⟩

end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalOneCount
