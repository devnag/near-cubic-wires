import Proof.SourceAssembly.PoolDonorCompatible
import Proof.Rows.TopFrameReentry

/-! Actual native gate frame to signed fields, with paid scratch reuse. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 550000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_NativeGateLoadReady
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
noncomputable section
attribute [local irreducible] PoolEntryLoad.machine

def caps (H : Nat) (i : Fin 9) := if i=6 then 0 else H
def extra (H : Nat) : Fin 2→List Bool := ![List.replicate H true,List.replicate (H+1) false]
def bank {q : Nat} (g : ExactThresholdGate q) (fields : List Bool) (H : Nat) : Fin 11→List Bool :=
 ![ZeroPadding.pad H (frame (PoolEntryLoad.word g)),List.replicate H false,List.replicate H false,
   List.replicate H false,List.replicate H false,fields,CompareMachine.word q,
   List.replicate H false,List.replicate H false,List.replicate H true,List.replicate (H+1) false]
def dirty {q : Nat} (g : ExactThresholdGate q) (H : Nat) : Fin 11→List Bool :=
 Fin.addCases (m:=9) (n:=2) (motive:=fun _=>List Bool)
  (fun i=>ZeroPadding.pad (caps H i) (Fin.addCases (PoolEntryLoad.output g 0) (fun _ : Fin 1=>List.replicate H false) i))
  (extra H)
def heads {q : Nat} (g : ExactThresholdGate q) : Fin 11→Nat := fun i=>if i=1 then (PoolEntryLoad.word g).length else 0
def slots : Fin 8→Fin 11 := ![1,2,3,4,7,8,9,10]
def load := TapeEmbedding.machine 2 PoolEntryLoad.machine
def clear := RecoveryFocus.machine slots (PCJ45bee56da9f34d5a_HeaderRewind.clear 6)
def machine := Composition.machine load clear

theorem load_run {q : Nat} (g : ExactThresholdGate q) (H : Nat) (hH : PoolEntryLoad.rawBudget g≤H) :
 Step load (PoolEntryLoad.budget g) (fun _=>0) (bank g (List.replicate H false) H)
   (heads g) (dirty g H) := by
 have h:=((PoolEntryLoad.load_run g 0 H hH).pad (caps H)).embed (fun _ : Fin 2=>0) (extra H)
 refine (h.congr_in ?_ ?_).congr ?_ rfl
 all_goals funext i;fin_cases i <;>simp [bank,caps,heads,extra,PoolEntryLoad.input,PoolEntryLoad.data,Fin.addCases,ZeroPadding.pad]

theorem clear_run {q : Nat} (g : ExactThresholdGate q) (H : Nat)
 (hH : PoolEntryLoad.budget g+1≤H) :
 Step clear (4*H+9) (heads g) (dirty g H) (fun _=>0)
   (bank g (ZeroPadding.pad H (exactWord g)) H) := by
 have hr : PoolEntryLoad.rawBudget g≤H := by unfold PoolEntryLoad.budget at hH;omega
 have base:=PoolEntryLoad.load_run g 0 H hr
 have ha : ∀i : Fin 6,(dirty g H (slots i.castSucc.castSucc)).length≤H := by
  intro i
  let j : Fin 9:=![1,2,3,4,7,8] i
  have hin : ((Fin.addCases (m:=8) (n:=1) (motive:=fun _=>List Bool) (PoolEntryLoad.input g 0) (fun _ : Fin 1=>List.replicate H false)) j).length≤H := by
   fin_cases i <;>simp [j,PoolEntryLoad.input,PoolEntryLoad.data,Fin.addCases]
  have hf:=LocalSupport.step_fits base j H hin (by simpa using hH)
  fin_cases i <;>simp_all [j,dirty,slots,caps,Fin.addCases,ZeroPadding.pad_length]
 have hh : ∀i : Fin 6,heads g (slots i.castSucc.castSucc)≤H := by
  intro i
  have hw : (PoolEntryLoad.word g).length≤H := by unfold PoolEntryLoad.budget PoolEntryLoad.rawBudget at hH;omega
  fin_cases i <;>simp [heads,slots]
  omega
 have h:=(PCJ45bee56da9f34d5a_HeaderRewind.clear_run 6
   (fun i=>heads g (slots i.castSucc.castSucc)) (fun i=>dirty g H (slots i.castSucc.castSucc)) H hh ha).dock
   slots (by decide) (heads g) (dirty g H)
   (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
 apply h.congr
 · funext i;fin_cases i <;> first
    | exact dockH_slot slots (by decide) _ _ 0
    | exact dockH_slot slots (by decide) _ _ 1
    | exact dockH_slot slots (by decide) _ _ 2
    | exact dockH_slot slots (by decide) _ _ 3
    | exact dockH_slot slots (by decide) _ _ 4
    | exact dockH_slot slots (by decide) _ _ 5
    | exact dockH_slot slots (by decide) _ _ 6
    | exact dockH_slot slots (by decide) _ _ 7
    | exact dockH_other slots _ _ _ (by decide)
 · apply HierarchyAllocation.install_eq slots (by decide)
   · intro i;fin_cases i <;>rfl
   · intro i hi
     fin_cases i <;> first
      | rfl
      | exact (ZeroPadding.pad_zero _).symm
      | exact False.elim (hi 0 rfl)
      | exact False.elim (hi 1 rfl)
      | exact False.elim (hi 2 rfl)
      | exact False.elim (hi 3 rfl)
      | exact False.elim (hi 4 rfl)
      | exact False.elim (hi 5 rfl)

theorem run {q : Nat} (g : ExactThresholdGate q) (H : Nat) (hH : PoolEntryLoad.budget g+1≤H) :
 Step machine (PoolEntryLoad.budget g+4*H+10) (fun _=>0) (bank g (List.replicate H false) H)
   (fun _=>0) (bank g (ZeroPadding.pad H (exactWord g)) H) := by
 have hr : PoolEntryLoad.rawBudget g≤H := by unfold PoolEntryLoad.budget at hH;omega
 have h:=(load_run g H hr).seq (clear_run g H hH)
 unfold machine
 convert h using 1;omega
end
end PCJ45bee56da9f34d5a_NativeGateLoadReady
