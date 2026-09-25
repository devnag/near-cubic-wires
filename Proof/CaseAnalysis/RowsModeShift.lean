import Proof.CaseAnalysis.RowsModeShiftMeaning
import Proof.Hierarchy.HierarchyBinaryKernel

/-! Compute the shifted binomial guard from the original offset and shift
fields by actual addition, predecessor and Lucas scans. No binomial scalar
or saturating-zero branch is supplied to the program. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeShift
open LocalBitMultitape RecoveryRootRound SignedSortKey ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def data (w offset b scratch C : Nat) (nonzero guard : Bool) : Fin 6→List Bool:=
  ![frame (binary w offset),frame (binary w b),frame (binary w scratch),[nonzero],[guard],List.replicate C false]
def addSlots : Fin 4→Fin 6:=![0,1,2,5]
def predSlots : Fin 3→Fin 6:=![2,3,5]
def paritySlots : Fin 4→Fin 6:=![2,1,4,5]
noncomputable def add:=RecoveryFocus.machine addSlots BoundaryAdvance.machine
noncomputable def pred:=RecoveryFocus.machine predSlots RecoveryListPredecessor.machine
noncomputable def parity:=RecoveryFocus.machine paritySlots CloseoutRowsModeParityReusable.machine
noncomputable def machine:=Composition.machine (Composition.machine add pred) parity

theorem add_step (w offset b scratch C : Nat) (nonzero guard : Bool)
    (hfit : offset+b<2^w) (hC : 2*w+1≤C) :
    Step add (4*w+4) (fun _=>0) (data w offset b scratch C nonzero guard)
      (fun _=>0) (data w offset b (offset+b) C nonzero guard):=by
  have localRun:=HierarchyBinary.add_ready w offset b C (frame (binary w scratch)) hfit (by simp)
  rw [max_eq_left hC] at localRun
  have focused:=localRun.focus addSlots (by decide) (data w offset b scratch C nonzero guard)
    (by intro i;fin_cases i <;> rfl)
  apply (Step.of_ready focused).congr rfl
  funext i;fin_cases i
  all_goals first
    | exact install_slot _ (by decide) _ _ 0
    | exact install_slot _ (by decide) _ _ 1
    | exact install_slot _ (by decide) _ _ 2
    | exact install_slot _ (by decide) _ _ 3
    | exact install_other _ _ _ _ (by decide)

theorem pred_step (w offset b C : Nat) (nonzero guard : Bool)
    (hfit : offset+b<2^w) (hC : 2*w+1≤C) :
    Step pred (4*w+4) (fun _=>0) (data w offset b (offset+b) C nonzero guard)
      (fun _=>0) (data w offset b (top w offset b) C (decide (offset+b≠0)) guard):=by
  have localRun:=RecoveryListPredecessor.predecessor_ready (binary w (offset+b)) nonzero C
  simp only [binary_length,max_eq_left hC,top_binary,binary_value w (offset+b) hfit] at localRun
  have focused:=localRun.focus predSlots (by decide) (data w offset b (offset+b) C nonzero guard)
    (by intro i;fin_cases i <;> rfl)
  apply (Step.of_ready focused).congr rfl
  funext i;fin_cases i
  all_goals first
    | exact install_slot _ (by decide) _ _ 0
    | exact install_slot _ (by decide) _ _ 1
    | exact install_slot _ (by decide) _ _ 2
    | exact install_other _ _ _ _ (by decide)

theorem parity_step (w offset b C : Nat) (nonzero guard : Bool)
    (hfit : offset+b<2^w) (hC : 2*w+1≤C) :
    Step parity (4*w+4) (fun _=>0) (data w offset b (top w offset b) C nonzero guard)
      (fun _=>0) (data w offset b (top w offset b) C nonzero
        (guard&&((offset+b-1).choose b%2==1))):=by
  have localRun:=CloseoutRowsModeParityReusable.parity_ready w (top w offset b) b C guard
    (top_fit w offset b) (by omega) hC
  rw [coefficient w offset b hfit] at localRun
  have focused:=localRun.focus paritySlots (by decide) (data w offset b (top w offset b) C nonzero guard)
    (by intro i;fin_cases i <;> rfl)
  apply (Step.of_ready focused).congr rfl
  funext i;fin_cases i
  all_goals first
    | exact install_slot _ (by decide) _ _ 0
    | exact install_slot _ (by decide) _ _ 1
    | exact install_slot _ (by decide) _ _ 2
    | exact install_slot _ (by decide) _ _ 3
    | exact install_other _ _ _ _ (by decide)

theorem shift_run (w offset b scratch C : Nat) (nonzero guard : Bool)
    (hfit : offset+b<2^w) (hC : 2*w+1≤C) :
    Step machine (12*w+14) (fun _=>0) (data w offset b scratch C nonzero guard)
      (fun _=>0) (data w offset b (top w offset b) C (decide (offset+b≠0))
        (guard&&((offset+b-1).choose b%2==1))):=by
  have whole:=((add_step w offset b scratch C nonzero guard hfit hC).seq
    (pred_step w offset b C nonzero guard hfit hC)).seq
    (parity_step w offset b C (decide (offset+b≠0)) guard hfit hC)
  have time:(4*w+4+1+(4*w+4))+1+(4*w+4)=12*w+14:=by omega
  rw [time] at whole
  exact whole

end NearCubicWires.RepairOrdinary.CloseoutRowsModeShift
