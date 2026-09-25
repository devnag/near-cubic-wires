import Proof.Rows.NativeCircuitPrepare
import Proof.Rows.NativeGateBlock

/-! Actual native circuit payload to its complete flag block: read the count,
skip TOP, evaluate every original bottom gate, then emit the true target flag.
The source bound includes the circuit's gate count, not merely one gate width. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_NativeCircuitFlags
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ45bee56da9f34d5a_NativeCircuitCount PCJ45bee56da9f34d5a_UniformMinimumBounds
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_NativeCircuitPrepare.machine
attribute [local irreducible] PCJ45bee56da9f34d5a_NativeGateBlock.machine

def machine:=Composition.machine PCJ45bee56da9f34d5a_NativeCircuitPrepare.machine
 PCJ45bee56da9f34d5a_NativeGateBlock.machine

def payload {q : Nat} (gs : List (NormalizedThresholdGate q)) (top : List Bool) :=
 natWord gs.length++frame top++PCJ45bee56da9f34d5a_NativeGateLoop.stream gs

def flags {q : Nat} (gs : List (NormalizedThresholdGate q)) (live : Finset (Fin q)) (x : BitInput q) :=
 gs.map (fun g=>residualConstant g live x)++[true]

def budget (n B q t : Nat) :=PCJ45bee56da9f34d5a_NativeCircuitPrepare.budget n (U B q (B+1)) t+
 PCJ45bee56da9f34d5a_NativeGateLoop.budget n B q+3

theorem count_fits (n B q : Nat) (hn : n≤B) : PCPPQueryNatural.budget n<U B q (B+1) := by
 have hb : natBitLength n≤n+1 := Nat.add_le_add_right (Nat.log_le_self _ _) 1
 have hm:=Nat.mul_le_mul_left n hb
 have hsmall : PCPPQueryNatural.budget n≤80*(n+1)^2 := by
  unfold PCPPQueryNatural.budget MatrixDimensionPrepare.budget
  nlinarith
 have hp : (n+1)^2≤(B+q+(B+1)+1)^2:=Nat.pow_le_pow_left (by omega) 2
 have hpos : 1≤(B+q+(B+1)+1)^2 := Nat.one_le_pow _ _ (by omega)
 unfold U PCJ45bee56da9f34d5a_FullGateCapacity.capacity
 omega

theorem run {q : Nat} (gs : List (NormalizedThresholdGate q)) (live : Finset (Fin q)) (x : BitInput q)
 (top tail out : List Bool) (B Q : Nat) (hn : gs.length≤B)
 (hb : ∀g∈gs,(PCJ45bee56da9f34d5a_FullGateBounds.source g).length≤B) :
 Step machine (budget gs.length B q top.length)
  (heads 0 out Q 0)
  (bank live x (B+1) (H B q (B+1)) (R B q (B+1)) (U B q (B+1)) (payload gs top++tail)
    (List.replicate (H B q (B+1)) false) (List.replicate (H B q (B+1)) false) out
    (List.replicate (U B q (B+1)) false) Q)
  (heads (payload gs top).length (out++flags gs live x) (Q+gs.length+1) 1)
  (bank live x (B+1) (H B q (B+1)) (R B q (B+1)) (U B q (B+1)) (payload gs top++tail)
    (List.replicate (H B q (B+1)) false) (List.replicate (H B q (B+1)) false) (out++flags gs live x)
    (ZeroPadding.pad (U B q (B+1)) (CompareMachine.word gs.length)) (Q+gs.length+1)) := by
 have first:=PCJ45bee56da9f34d5a_NativeCircuitPrepare.run live x (B+1) (H B q (B+1))
  (R B q (B+1)) (U B q (B+1)) Q gs.length top
  (PCJ45bee56da9f34d5a_NativeGateLoop.stream gs++tail) (List.replicate (H B q (B+1)) false) out
  (count_fits gs.length B q hn)
 have last:=PCJ45bee56da9f34d5a_NativeGateBlock.run gs live x (natWord gs.length++frame top) tail out B Q hb
 simp only [List.length_append,List.append_assoc] at first last
 have h:=first.seq last
 have hf : PCJ45bee56da9f34d5a_NativeCircuitPrepare.budget gs.length (U B q (B+1)) top.length+1+
  (PCJ45bee56da9f34d5a_NativeGateLoop.budget gs.length B q+2)=budget gs.length B q top.length :=by unfold budget;omega
 simpa only [machine,hf,payload,flags,List.length_append,List.append_assoc,Nat.add_assoc] using h
end
end PCJ45bee56da9f34d5a_NativeCircuitFlags
