import Proof.CaseAnalysis.RowsModeWindowEmit
import Proof.MachineModel.Layout

/-! Both scalar coefficient scans execute in the retained numeric bank,
leaving the live polynomial cursor and elementary masters unchanged. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowScalar
open LocalBitMultitape RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open CloseoutRowsModeWindowLayout
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=RecoveryFocus.machine guardSlots CloseoutRowsModeWindowGuard.machine
def coefficient (offset b degree target : Nat):=
  (degree.choose target%2==1)&&((offset+b-1).choose b%2==1)

theorem scalar_heads (out : List Bool) (i : Fin 8) : heads out (guardSlots i)=0:=by
  fin_cases i <;> rfl

theorem scalar_install (v u M a offset b scratch scratch' degree target C : Nat)
    (nonzero guard nonzero' guard' : Bool) (out : List Bool) :
    install guardSlots (data v u M a offset b scratch degree target C nonzero guard out)
      (scalars u offset b scratch' degree target C nonzero' guard')=
      data v u M a offset b scratch' degree target C nonzero' guard' out:=by
  funext i
  cases hp:RecoveryFocus.pick guardSlots i with
  | some j=>
    simp only [install,hp]
    rw [←RecoveryFocus.slot_of_pick guardSlots hp,guard_slot]
  | none=>
    simp only [install,hp]
    have hn : ∀ j,guardSlots j≠i:=by
      intro j hj
      have h:=RecoveryFocus.pick_slot guardSlots (by decide) j
      rw [hj,hp] at h
      contradiction
    unfold data
    simp only [Fin.addCases]
    split
    · rfl
    · rename_i h
      have h0:=hn 0;have h1:=hn 1;have h2:=hn 2;have h3:=hn 3
      have h4:=hn 4;have h6:=hn 6;have h7:=hn 7
      change (52 : Fin 60)≠i at h0
      change (53 : Fin 60)≠i at h1
      change (54 : Fin 60)≠i at h2
      change (55 : Fin 60)≠i at h3
      change (56 : Fin 60)≠i at h4
      change (57 : Fin 60)≠i at h6
      change (58 : Fin 60)≠i at h7
      simp only [ne_eq,Fin.ext_iff] at h0 h1 h2 h3 h4 h6 h7
      have hi : i=59:=Fin.ext (by omega)
      subst i
      rfl

theorem scalar_run (v u M a offset b scratch degree target C : Nat)
    (nonzero guard : Bool) (out : List Bool)
    (hfit : offset+b<2^u) (hd : degree<2^u) (ht : target<2^u) (hC : 2*u≤C) :
    Step machine (16*u+21) (heads out)
      (data v u M a offset b scratch degree target C nonzero guard out)
      (heads out)
      (data v u M a offset b (CloseoutRowsModeShift.top u offset b) degree target C
        (decide (offset+b≠0)) (coefficient offset b degree target) out):=by
  have localRun:=(CloseoutRowsModeWindowGuard.guard_run u offset b scratch degree target (C+1)
    nonzero guard hfit hd ht (by omega)).pad (scalarCaps C)
  have joined:=localRun.dock guardSlots (by decide) (heads out)
    (data v u M a offset b scratch degree target C nonzero guard out)
    (scalar_heads out) (guard_slot _ _ _ _ _ _ _ _ _ _ _ _ _)
  exact joined.congr (dockH_existing guardSlots (heads out) (fun _=>0) (scalar_heads out))
    (scalar_install _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)

noncomputable def summand:=Composition.machine machine CloseoutRowsModeWindowEmit.machine

theorem summand_run (v u M a offset b scratch degree target C : Nat)
    (nonzero guard : Bool) (out : List Bool)
    (hfit : offset+b<2^u) (hd : degree<2^u) (ht : target<2^u) (hscalar : 2*u≤C)
    (hMv : M≤2^v) (hmeta : 2*v+a+3≤C) (hC : CloseoutRowsModeElementary.budget v a M+1≤C) :
    Step summand (16*u+28+CloseoutRowsModeElementaryReusable.budget v a M C) (heads out)
      (data v u M a offset b scratch degree target C nonzero guard out)
      (heads (out++CloseoutRowsModeWindowEmit.word v a M (coefficient offset b degree target)))
      (data v u M a offset b (CloseoutRowsModeShift.top u offset b) degree target C
        (decide (offset+b≠0)) (coefficient offset b degree target)
        (out++CloseoutRowsModeWindowEmit.word v a M (coefficient offset b degree target))):=by
  have whole:=(scalar_run v u M a offset b scratch degree target C nonzero guard out hfit hd ht hscalar).seq
    (CloseoutRowsModeWindowEmit.emit_run v u M a offset b (CloseoutRowsModeShift.top u offset b) degree target C
      (decide (offset+b≠0)) (coefficient offset b degree target) out hMv hmeta hC)
  have time : 16*u+21+1+(CloseoutRowsModeElementaryReusable.budget v a M C+6)=
      16*u+28+CloseoutRowsModeElementaryReusable.budget v a M C:=by omega
  rw [time] at whole
  exact whole

end NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowScalar
