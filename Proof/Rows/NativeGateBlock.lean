import Proof.Rows.TrueFlagCell
import Proof.Rows.NativeCircuitCount

/-! The whole bottom block emits every actual gate flag followed by the
circuit's true target flag, using a padded runtime count driver. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_NativeGateBlock
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ45bee56da9f34d5a_NativeCircuitCount PCJ45bee56da9f34d5a_UniformMinimumBounds
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_NativeGateLoop.machine

def caps (U : Nat) : Fin 124→Nat := Fin.addCases (m:=123) (n:=1) (motive:=fun _=>Nat) (fun _=>0) (fun _=>U)
theorem pad_counter (A : Fin 123→List Bool) (count : List Bool) (U : Nat) :
 (fun i=>ZeroPadding.pad (caps U i) (Fin.addCases (m:=123) (n:=1) (motive:=fun _=>List Bool) A (fun _=>count) i))=
 Fin.addCases (m:=123) (n:=1) (motive:=fun _=>List Bool) A (fun _=>ZeroPadding.pad U count) := by
 funext i
 refine Fin.addCases (m:=123) (n:=1) (fun _=>?_) (fun _=>?_) i
 · simp only [caps,Fin.addCases_left,ZeroPadding.pad_zero]
 · simp only [caps,Fin.addCases_right]

def target := TapeEmbedding.machine 1 PCJ45bee56da9f34d5a_TrueFlagCell.machine
def machine := Composition.machine PCJ45bee56da9f34d5a_NativeGateLoop.machine target

theorem loop_run {q : Nat} (gs : List (NormalizedThresholdGate q)) (live : Finset (Fin q)) (x : BitInput q)
 (pre tail out : List Bool) (B Q : Nat)
 (hb : ∀g∈gs,(PCJ45bee56da9f34d5a_FullGateBounds.source g).length≤B) :
 Step PCJ45bee56da9f34d5a_NativeGateLoop.machine (PCJ45bee56da9f34d5a_NativeGateLoop.budget gs.length B q)
  (heads pre.length out Q 1)
  (bank live x (B+1) (H B q (B+1)) (R B q (B+1)) (U B q (B+1)) (pre++PCJ45bee56da9f34d5a_NativeGateLoop.stream gs++tail)
    (List.replicate (H B q (B+1)) false) (List.replicate (H B q (B+1)) false) out
    (ZeroPadding.pad (U B q (B+1)) (CompareMachine.word gs.length)) Q)
  (heads (pre.length+(PCJ45bee56da9f34d5a_NativeGateLoop.stream gs).length) (out++gs.map (fun g=>residualConstant g live x)) (Q+gs.length) 1)
  (bank live x (B+1) (H B q (B+1)) (R B q (B+1)) (U B q (B+1)) (pre++PCJ45bee56da9f34d5a_NativeGateLoop.stream gs++tail)
    (List.replicate (H B q (B+1)) false) (List.replicate (H B q (B+1)) false) (out++gs.map (fun g=>residualConstant g live x))
    (ZeroPadding.pad (U B q (B+1)) (CompareMachine.word gs.length)) (Q+gs.length)) := by
 have h:=(PCJ45bee56da9f34d5a_NativeGateLoop.run gs live x pre tail out B Q hb).pad (caps (U B q (B+1)))
 rw [pad_counter,pad_counter] at h
 exact h

theorem run {q : Nat} (gs : List (NormalizedThresholdGate q)) (live : Finset (Fin q)) (x : BitInput q)
 (pre tail out : List Bool) (B Q : Nat)
 (hb : ∀g∈gs,(PCJ45bee56da9f34d5a_FullGateBounds.source g).length≤B) :
 Step machine (PCJ45bee56da9f34d5a_NativeGateLoop.budget gs.length B q+2)
  (heads pre.length out Q 1)
  (bank live x (B+1) (H B q (B+1)) (R B q (B+1)) (U B q (B+1)) (pre++PCJ45bee56da9f34d5a_NativeGateLoop.stream gs++tail)
    (List.replicate (H B q (B+1)) false) (List.replicate (H B q (B+1)) false) out
    (ZeroPadding.pad (U B q (B+1)) (CompareMachine.word gs.length)) Q)
  (heads (pre.length+(PCJ45bee56da9f34d5a_NativeGateLoop.stream gs).length) ((out++gs.map (fun g=>residualConstant g live x))++[true]) (Q+gs.length+1) 1)
  (bank live x (B+1) (H B q (B+1)) (R B q (B+1)) (U B q (B+1)) (pre++PCJ45bee56da9f34d5a_NativeGateLoop.stream gs++tail)
    (List.replicate (H B q (B+1)) false) (List.replicate (H B q (B+1)) false) ((out++gs.map (fun g=>residualConstant g live x))++[true])
    (ZeroPadding.pad (U B q (B+1)) (CompareMachine.word gs.length)) (Q+gs.length+1)) := by
 have first:=loop_run gs live x pre tail out B Q hb
 have last:=(PCJ45bee56da9f34d5a_TrueFlagCell.run live x (B+1) (H B q (B+1)) (R B q (B+1)) (U B q (B+1))
  (pre.length+(PCJ45bee56da9f34d5a_NativeGateLoop.stream gs).length) (Q+gs.length)
  (pre++PCJ45bee56da9f34d5a_NativeGateLoop.stream gs++tail) (List.replicate (H B q (B+1)) false)
  (List.replicate (H B q (B+1)) false) (out++gs.map (fun g=>residualConstant g live x))).embed
  (fun _ : Fin 1=>1) (fun _ : Fin 1=>ZeroPadding.pad (U B q (B+1)) (CompareMachine.word gs.length))
 have h:=first.seq last
 simpa only [machine,target,heads,bank,PCJ45bee56da9f34d5a_TrueFlagCell.heads,
  PCJ45bee56da9f34d5a_TrueFlagCell.bank,
  show PCJ45bee56da9f34d5a_NativeGateLoop.budget gs.length B q+1+1=PCJ45bee56da9f34d5a_NativeGateLoop.budget gs.length B q+2 by omega] using h
end
end PCJ45bee56da9f34d5a_NativeGateBlock
