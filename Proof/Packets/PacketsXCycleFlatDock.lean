import Proof.Packets.PacketsXCycleFlatTyped

/-! Literal join from the reusable arithmetic bank to the native family
stream. Existing padded scalar and R+3 log words are consumed in place. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace Theorem25Completion.CycleFlatDock
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed
noncomputable section

def slots : Fin 8→Fin 35 := ![24,26,29,34,27,30,32,33]
theorem slots_injective : Function.Injective slots := by decide
def caps (R : Nat) : Fin 8→Nat := ![R,0,0,0,0,R+3,0,R+3]
def machine := RecoveryFocus.machine slots CycleFlatSerialize.transaction

def heads (out : List Bool) (i : Fin 35) : Nat := if i=31 then 1 else if i=34 then out.length else 0
def bank (B R : Nat) (left : List Bool) (leftN : Nat) (rows : List (List Bool))
    (out : List Bool) (i : Fin 35) : List Bool :=
  if i=13 then ZeroPadding.pad R (UnaryTemplate.tape (2*B+3))
  else if i=24 then ZeroPadding.pad R (UnaryTemplate.tape B)
  else if i=25 then ZeroPadding.pad R left
  else if i=26 then ZeroPadding.pad R rows.flatten
  else if i=27 then ZeroPadding.pad R (CompareMachine.word rows.length)
  else if i=28 then ZeroPadding.pad R (CompareMachine.word leftN)
  else if i=30 then List.replicate (R+3) false
  else if i=31 then UnaryTemplate.tape R
  else if i=32 then List.replicate R true
  else if i=33 then List.replicate (R+3) false
  else if i=34 then out else List.replicate R false

theorem pad_zeros (C D : Nat) (h : D≤C) :
    ZeroPadding.pad C (List.replicate D false)=List.replicate C false := by
  simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add]
  congr 1
  omega

theorem zero_count (R : Nat) (h : 1≤R) :
    ZeroPadding.pad R (CompareMachine.word 0)=List.replicate R false :=
  pad_zeros R 1 h

variable (B R : Nat) (left : List Bool) (leftN : Nat) (rows : List (List Bool)) (out : List Bool)

theorem input_heads (i : Fin 8) : heads out (slots i)=CycleFlatSerialize.transactionHeads out i := by
  fin_cases i <;>rfl

theorem input_tapes (i : Fin 8) : bank B R left leftN rows out (slots i)=
    ZeroPadding.pad (caps R i) (CycleFlatSerialize.transactionInput B R rows out i) := by
  fin_cases i
  · change ZeroPadding.pad R (UnaryTemplate.tape B)=ZeroPadding.pad R (ZeroPadding.pad 0 (UnaryTemplate.tape B))
    rw [ZeroPadding.pad_zero]
  · symm
    exact ZeroPadding.pad_zero _
  · change List.replicate R false=ZeroPadding.pad 0 (ZeroPadding.pad R (List.replicate R false))
    rw [ZeroPadding.pad_zero,pad_zeros R R le_rfl]
  · change out=ZeroPadding.pad 0 (ZeroPadding.pad 0 out)
    rw [ZeroPadding.pad_zero,ZeroPadding.pad_zero]
  · symm
    exact ZeroPadding.pad_zero _
  · change List.replicate (R+3) false=ZeroPadding.pad (R+3) (List.replicate (R) false)
    exact (pad_zeros _ _ (by omega)).symm
  · symm
    exact ZeroPadding.pad_zero _
  · change List.replicate (R+3) false=ZeroPadding.pad (R+3) (List.replicate (R+1) false)
    exact (pad_zeros _ _ (by omega)).symm

theorem output_heads : dockH slots (heads out) (CycleFlatSerialize.transactionHeads (out++CycleFlatSerialize.word rows))=
    heads (out++CycleFlatSerialize.word rows) := by
  funext i
  fin_cases i
  · rw [dockH_other _ _ _ _ (by decide)]
    rfl
  · rw [dockH_other _ _ _ _ (by decide)]
    rfl
  · rw [dockH_other _ _ _ _ (by decide)]
    rfl
  · rw [dockH_other _ _ _ _ (by decide)]
    rfl
  · rw [dockH_other _ _ _ _ (by decide)]
    rfl
  · rw [dockH_other _ _ _ _ (by decide)]
    rfl
  · rw [dockH_other _ _ _ _ (by decide)]
    rfl
  · rw [dockH_other _ _ _ _ (by decide)]
    rfl
  · rw [dockH_other _ _ _ _ (by decide)]
    rfl
  · rw [dockH_other _ _ _ _ (by decide)]
    rfl
  · rw [dockH_other _ _ _ _ (by decide)]
    rfl
  · rw [dockH_other _ _ _ _ (by decide)]
    rfl
  · rw [dockH_other _ _ _ _ (by decide)]
    rfl
  · rw [dockH_other _ _ _ _ (by decide)]
    rfl
  · rw [dockH_other _ _ _ _ (by decide)]
    rfl
  · rw [dockH_other _ _ _ _ (by decide)]
    rfl
  · rw [dockH_other _ _ _ _ (by decide)]
    rfl
  · rw [dockH_other _ _ _ _ (by decide)]
    rfl
  · rw [dockH_other _ _ _ _ (by decide)]
    rfl
  · rw [dockH_other _ _ _ _ (by decide)]
    rfl
  · rw [dockH_other _ _ _ _ (by decide)]
    rfl
  · rw [dockH_other _ _ _ _ (by decide)]
    rfl
  · rw [dockH_other _ _ _ _ (by decide)]
    rfl
  · rw [dockH_other _ _ _ _ (by decide)]
    rfl
  · change dockH slots (heads out) (CycleFlatSerialize.transactionHeads (out++CycleFlatSerialize.word rows)) (slots 0)=_
    rw [dockH_slot _ slots_injective]
    rfl
  · rw [dockH_other _ _ _ _ (by decide)]
    rfl
  · change dockH slots (heads out) (CycleFlatSerialize.transactionHeads (out++CycleFlatSerialize.word rows)) (slots 1)=_
    rw [dockH_slot _ slots_injective]
    rfl
  · change dockH slots (heads out) (CycleFlatSerialize.transactionHeads (out++CycleFlatSerialize.word rows)) (slots 4)=_
    rw [dockH_slot _ slots_injective]
    rfl
  · rw [dockH_other _ _ _ _ (by decide)]
    rfl
  · change dockH slots (heads out) (CycleFlatSerialize.transactionHeads (out++CycleFlatSerialize.word rows)) (slots 2)=_
    rw [dockH_slot _ slots_injective]
    rfl
  · change dockH slots (heads out) (CycleFlatSerialize.transactionHeads (out++CycleFlatSerialize.word rows)) (slots 5)=_
    rw [dockH_slot _ slots_injective]
    rfl
  · rw [dockH_other _ _ _ _ (by decide)]
    rfl
  · change dockH slots (heads out) (CycleFlatSerialize.transactionHeads (out++CycleFlatSerialize.word rows)) (slots 6)=_
    rw [dockH_slot _ slots_injective]
    rfl
  · change dockH slots (heads out) (CycleFlatSerialize.transactionHeads (out++CycleFlatSerialize.word rows)) (slots 7)=_
    rw [dockH_slot _ slots_injective]
    rfl
  · change dockH slots (heads out) (CycleFlatSerialize.transactionHeads (out++CycleFlatSerialize.word rows)) (slots 3)=_
    rw [dockH_slot _ slots_injective]
    rfl

theorem output_tapes (hR : 1≤R) :
    install slots (bank B R left leftN rows out)
      (fun i=>ZeroPadding.pad (caps R i) (CycleFlatSerialize.cleanBank B R (out++CycleFlatSerialize.word rows) i))=
      bank B R left leftN [] (out++CycleFlatSerialize.word rows) := by
  funext i
  fin_cases i
  · rw [install_other _ _ _ _ (by decide)]
    rfl
  · rw [install_other _ _ _ _ (by decide)]
    rfl
  · rw [install_other _ _ _ _ (by decide)]
    rfl
  · rw [install_other _ _ _ _ (by decide)]
    rfl
  · rw [install_other _ _ _ _ (by decide)]
    rfl
  · rw [install_other _ _ _ _ (by decide)]
    rfl
  · rw [install_other _ _ _ _ (by decide)]
    rfl
  · rw [install_other _ _ _ _ (by decide)]
    rfl
  · rw [install_other _ _ _ _ (by decide)]
    rfl
  · rw [install_other _ _ _ _ (by decide)]
    rfl
  · rw [install_other _ _ _ _ (by decide)]
    rfl
  · rw [install_other _ _ _ _ (by decide)]
    rfl
  · rw [install_other _ _ _ _ (by decide)]
    rfl
  · rw [install_other _ _ _ _ (by decide)]
    rfl
  · rw [install_other _ _ _ _ (by decide)]
    rfl
  · rw [install_other _ _ _ _ (by decide)]
    rfl
  · rw [install_other _ _ _ _ (by decide)]
    rfl
  · rw [install_other _ _ _ _ (by decide)]
    rfl
  · rw [install_other _ _ _ _ (by decide)]
    rfl
  · rw [install_other _ _ _ _ (by decide)]
    rfl
  · rw [install_other _ _ _ _ (by decide)]
    rfl
  · rw [install_other _ _ _ _ (by decide)]
    rfl
  · rw [install_other _ _ _ _ (by decide)]
    rfl
  · rw [install_other _ _ _ _ (by decide)]
    rfl
  · change install slots (bank B R left leftN rows out)
      (fun i=>ZeroPadding.pad (caps R i) (CycleFlatSerialize.cleanBank B R (out++CycleFlatSerialize.word rows) i)) (slots 0)=_
    rw [install_slot _ slots_injective]
    rfl
  · rw [install_other _ _ _ _ (by decide)]
    rfl
  · change install slots (bank B R left leftN rows out)
      (fun i=>ZeroPadding.pad (caps R i) (CycleFlatSerialize.cleanBank B R (out++CycleFlatSerialize.word rows) i)) (slots 1)=_
    rw [install_slot _ slots_injective]
    exact ZeroPadding.pad_zero _
  · change install slots (bank B R left leftN rows out)
      (fun i=>ZeroPadding.pad (caps R i) (CycleFlatSerialize.cleanBank B R (out++CycleFlatSerialize.word rows) i)) (slots 4)=_
    rw [install_slot _ slots_injective]
    change ZeroPadding.pad 0 (List.replicate R false)=ZeroPadding.pad R (CompareMachine.word 0)
    rw [ZeroPadding.pad_zero,zero_count R hR]
  · rw [install_other _ _ _ _ (by decide)]
    rfl
  · change install slots (bank B R left leftN rows out)
      (fun i=>ZeroPadding.pad (caps R i) (CycleFlatSerialize.cleanBank B R (out++CycleFlatSerialize.word rows) i)) (slots 2)=_
    rw [install_slot _ slots_injective]
    exact ZeroPadding.pad_zero _
  · change install slots (bank B R left leftN rows out)
      (fun i=>ZeroPadding.pad (caps R i) (CycleFlatSerialize.cleanBank B R (out++CycleFlatSerialize.word rows) i)) (slots 5)=_
    rw [install_slot _ slots_injective]
    exact pad_zeros (R+3) R (by omega)
  · rw [install_other _ _ _ _ (by decide)]
    rfl
  · change install slots (bank B R left leftN rows out)
      (fun i=>ZeroPadding.pad (caps R i) (CycleFlatSerialize.cleanBank B R (out++CycleFlatSerialize.word rows) i)) (slots 6)=_
    rw [install_slot _ slots_injective]
    exact ZeroPadding.pad_zero _
  · change install slots (bank B R left leftN rows out)
      (fun i=>ZeroPadding.pad (caps R i) (CycleFlatSerialize.cleanBank B R (out++CycleFlatSerialize.word rows) i)) (slots 7)=_
    rw [install_slot _ slots_injective]
    exact pad_zeros (R+3) (R+1) (by omega)
  · change install slots (bank B R left leftN rows out)
      (fun i=>ZeroPadding.pad (caps R i) (CycleFlatSerialize.cleanBank B R (out++CycleFlatSerialize.word rows) i)) (slots 3)=_
    rw [install_slot _ slots_injective]
    exact ZeroPadding.pad_zero _

/-- Consume the actual arithmetic result in place, append its native packet,
and restore the right accumulator to its empty padded representation. -/
theorem run (hB : B+3≤R) (hR : CycleFlatSerialize.budget B rows+1≤R)
    (hw : ∀ row∈rows,row.length=B) :
    Step machine (CycleFlatSerialize.transactionBudget B R rows)
      (heads out) (bank B R left leftN rows out)
      (heads (out++CycleFlatSerialize.word rows))
      (bank B R left leftN [] (out++CycleFlatSerialize.word rows)) := by
  have h := (CycleFlatSerialize.transaction_run B R rows out hB hR hw).pad (caps R)
  have hf := CycleNormalize.dock_step h slots slots_injective _ _ (input_heads out)
    (input_tapes B R left leftN rows out)
  exact hf.congr (output_heads rows out) (output_tapes B R left leftN rows out (by omega))

end
end Theorem25Completion.CycleFlatDock
