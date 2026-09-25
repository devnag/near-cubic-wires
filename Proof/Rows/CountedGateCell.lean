import Proof.Rows.FramedGateRun
import Proof.Rows.FlagCountTick

/-! Each actual original-gate verdict also emits one unit of the final
comparator dimension. The count cursor stays at its writable end. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_CountedGateCell
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ45bee56da9f34d5a_FramedGateBank PCJ45bee56da9f34d5a_UniformMinimumBounds
open scoped BigOperators
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_FramedGateRun.machine

def heads (h : Fin 122→Nat) (Q : Nat) : Fin 123→Nat := Fin.addCases (m:=122) (n:=1) (motive:=fun _=>Nat) h (fun _ : Fin 1=>Q+1)
def bank (a : Fin 122→List Bool) (Q : Nat) : Fin 123→List Bool := Fin.addCases (m:=122) (n:=1) (motive:=fun _=>List Bool) a (fun _ : Fin 1=>CompareMachine.word Q)
def slots : Fin 1→Fin 123 := fun _=>122
def tick := RecoveryFocus.machine slots PCJ45bee56da9f34d5a_FlagCountTick.machine
def gate := TapeEmbedding.machine 1 PCJ45bee56da9f34d5a_FramedGateRun.machine
def machine := Composition.machine gate tick

theorem tick_run (h : Fin 122→Nat) (a : Fin 122→List Bool) (Q : Nat) :
 Step tick 1 (heads h Q) (bank a Q) (heads h (Q+1)) (bank a (Q+1)) := by
 have hs:=(PCJ45bee56da9f34d5a_FlagCountTick.run Q).dock slots (by decide) (heads h Q) (bank a Q)
   (by intro i;fin_cases i;rfl) (by intro i;fin_cases i;rfl)
 apply hs.congr
 · funext i
   refine Fin.addCases (m:=122) (n:=1) (fun j=>?_) (fun j=>?_) i
   · simpa only [heads,Fin.addCases_left] using
      (dockH_other slots (heads h Q) (fun _=>Q+1+1) (j.castAdd 1)
        (by intro k he;have hv:=congrArg Fin.val he;change 122=j.val at hv;omega))
   · fin_cases j;exact dockH_slot slots (by decide) _ _ 0
 · apply HierarchyAllocation.install_eq slots (by decide)
   · intro i;fin_cases i;rfl
   · intro i hi
     refine Fin.addCases (m:=122) (n:=1) (fun j _=>?_) (fun j hj=>?_) i hi
     · simp only [bank,Fin.addCases_left]
     · fin_cases j;exact False.elim (hj 0 rfl)

def cost (B q w : Nat) :=131072*(B+q+w+1)^2+2

theorem run {q : Nat} (g : NormalizedThresholdGate q) (live : Finset (Fin q)) (x : BitInput q)
 (B w Q : Nat) (pre tail out : List Bool) (hw : 0<w)
 (hb : (PCJ45bee56da9f34d5a_FullGateBounds.source g).length≤B)
 (hm : (g.threshold-1).natAbs+(∑i,(g.weight i).natAbs)<2^w) :
 Step machine (cost B q w)
  (heads (PCJ45bee56da9f34d5a_FramedGateBank.heads pre.length out) Q)
  (bank (PCJ45bee56da9f34d5a_FramedGateBank.bank live x w (H B q w) (R B q w) (U B q w)
    (pre++frame (PoolEntryLoad.word (strict g))++tail) (List.replicate (H B q w) false) (List.replicate (H B q w) false) out) Q)
  (heads (PCJ45bee56da9f34d5a_FramedGateBank.heads (pre.length+(frame (PoolEntryLoad.word (strict g))).length) (out++[residualConstant g live x])) (Q+1))
  (bank (PCJ45bee56da9f34d5a_FramedGateBank.bank live x w (H B q w) (R B q w) (U B q w)
    (pre++frame (PoolEntryLoad.word (strict g))++tail) (List.replicate (H B q w) false) (List.replicate (H B q w) false) (out++[residualConstant g live x])) (Q+1)) := by
 have first:=(PCJ45bee56da9f34d5a_FramedGateRun.run g live x B w pre tail out hw hb hm).embed
  (fun _ : Fin 1=>Q+1) (fun _ : Fin 1=>CompareMachine.word Q)
 have last:=tick_run (PCJ45bee56da9f34d5a_FramedGateBank.heads (pre.length+(frame (PoolEntryLoad.word (strict g))).length) (out++[residualConstant g live x]))
  (PCJ45bee56da9f34d5a_FramedGateBank.bank live x w (H B q w) (R B q w) (U B q w)
    (pre++frame (PoolEntryLoad.word (strict g))++tail) (List.replicate (H B q w) false) (List.replicate (H B q w) false) (out++[residualConstant g live x])) Q
 have h:=first.seq last
 simpa only [machine,gate,cost,heads,bank,show 131072*(B+q+w+1)^2+1+1=131072*(B+q+w+1)^2+2 by omega] using h
end
end PCJ45bee56da9f34d5a_CountedGateCell
