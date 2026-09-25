import Proof.Rows.CircuitFlagBody

/-! One reusable original circuit frame to its complete flag block and actual
coefficient count. Every private loader/parser tape returns to its cold bank. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 350000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_CircuitFlagRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ45bee56da9f34d5a_UniformMinimumBounds PCJ45bee56da9f34d5a_CircuitFlagBank
open PCJ45bee56da9f34d5a_NativeCircuitFlags (payload flags)
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_CircuitFlagLoad.machine
attribute [local irreducible] PCJ45bee56da9f34d5a_CircuitFlagBody.body
attribute [local irreducible] PCJ45bee56da9f34d5a_CircuitFlagBody.clear

def machine:=Composition.machine PCJ45bee56da9f34d5a_CircuitFlagLoad.machine
 (Composition.machine PCJ45bee56da9f34d5a_CircuitFlagBody.body PCJ45bee56da9f34d5a_CircuitFlagBody.clear)
def budget (n B q t len : Nat) :=PCJ45bee56da9f34d5a_NativeCircuitFlags.budget n B q t+8*len+4*U B q (B+1)+18

theorem reserve (B q : Nat) :2*B+2≤U B q (B+1) :=by
 have hp:B+q+(B+1)+1≤(B+q+(B+1)+1)^2:=Nat.le_self_pow (by decide) _
 unfold U PCJ45bee56da9f34d5a_FullGateCapacity.capacity
 omega

theorem run {q : Nat} (gs : List (NormalizedThresholdGate q)) (live : Finset (Fin q)) (x : BitInput q)
 (pre top tail out : List Bool) (B Q : Nat) (hn : gs.length≤B)
 (hb : ∀g∈gs,(PCJ45bee56da9f34d5a_FullGateBounds.source g).length≤B)
 (hp : (payload gs top).length≤B) :
 Step machine (budget gs.length B q top.length (payload gs top).length)
  (heads 0 pre.length out Q 0)
  (bank live x B (pre++frame (payload gs top)++tail) [] [] out (List.replicate (U B q (B+1)) false) Q)
  (heads 0 (pre.length+(frame (payload gs top)).length) (out++flags gs live x) (Q+gs.length+1) 0)
  (bank live x B (pre++frame (payload gs top)++tail) [] [] (out++flags gs live x)
    (List.replicate (U B q (B+1)) false) (Q+gs.length+1)) :=by
 have hres:=reserve B q
 have hframe : (frame (payload gs top)).length≤U B q (B+1):=by rw [frame_length];omega
 have first:=PCJ45bee56da9f34d5a_CircuitFlagLoad.run live x B Q pre (payload gs top) tail out hframe
 have middle:=PCJ45bee56da9f34d5a_CircuitFlagBody.body_run gs live x
  (pre++frame (payload gs top)++tail) top out B Q (pre.length+(frame (payload gs top)).length) hn hb
 have last:=PCJ45bee56da9f34d5a_CircuitFlagBody.clear_run live x B (Q+gs.length+1)
  (pre.length+(frame (payload gs top)).length) gs.length (pre++frame (payload gs top)++tail)
  (payload gs top) (out++flags gs live x) hframe (by omega)
 have h:=first.seq (middle.seq last)
 have hf : (8*(payload gs top).length+7)+1+
  (PCJ45bee56da9f34d5a_NativeCircuitFlags.budget gs.length B q top.length+1+(4*U B q (B+1)+9))=
  budget gs.length B q top.length (payload gs top).length :=by unfold budget;omega
 simpa only [machine,hf] using h
end
end PCJ45bee56da9f34d5a_CircuitFlagRun
