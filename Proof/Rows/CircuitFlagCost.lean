import Proof.Rows.NativeCircuitCodec

/-! A uniform cubic request-byte cost for the actual reusable circuit callback.
It depends only on unreplicated native circuit bytes and input arity. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 150000
namespace PCJ45bee56da9f34d5a_CircuitFlagCost
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open PCJ45bee56da9f34d5a_UniformMinimumBounds
open PCJ45bee56da9f34d5a_NativeCircuitFlags (payload flags)
open PCJ45bee56da9f34d5a_CircuitFlagBank
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_CircuitFlagRun.machine

def uniform (B q : Nat) :=2*(B*(8*(B+1)+10)+14*(B+1)+B+25)+10*U B q (B+1)+
 2*(B+1)+10*B+PCJ45bee56da9f34d5a_NativeGateLoop.budget B B q+42

theorem bound (n B q t len : Nat) (hn : n≤B) (ht : t≤B) (hl : len≤B) :
 PCJ45bee56da9f34d5a_CircuitFlagRun.budget n B q t len≤uniform B q :=by
 have hbit : natBitLength n≤B+1 :=(Nat.add_le_add_right (Nat.log_le_self _ _) 1).trans (by omega)
 have hm:=Nat.mul_le_mul hn (show 8*natBitLength n+10≤8*(B+1)+10 by omega)
 have hread : PCPPQueryNatural.budget n≤B*(8*(B+1)+10)+14*(B+1)+B+25 :=by
  unfold PCPPQueryNatural.budget MatrixDimensionPrepare.budget;omega
 have hloop : PCJ45bee56da9f34d5a_NativeGateLoop.budget n B q≤PCJ45bee56da9f34d5a_NativeGateLoop.budget B B q :=by
  unfold PCJ45bee56da9f34d5a_NativeGateLoop.budget
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 3
 unfold PCJ45bee56da9f34d5a_CircuitFlagRun.budget PCJ45bee56da9f34d5a_NativeCircuitFlags.budget
  PCJ45bee56da9f34d5a_NativeCircuitPrepare.budget uniform
 omega

theorem run {q : Nat} (gs : List (NormalizedThresholdGate q)) (live : Finset (Fin q)) (x : BitInput q)
 (pre top tail out : List Bool) (B Q : Nat) (hp : (payload gs top).length≤B) :
 Step PCJ45bee56da9f34d5a_CircuitFlagRun.machine (uniform B q)
  (heads 0 pre.length out Q 0)
  (bank live x B (pre++RepairOrdinary.frame (payload gs top)++tail) [] [] out (List.replicate (U B q (B+1)) false) Q)
  (heads 0 (pre.length+(RepairOrdinary.frame (payload gs top)).length) (out++flags gs live x) (Q+gs.length+1) 0)
  (bank live x B (pre++RepairOrdinary.frame (payload gs top)++tail) [] [] (out++flags gs live x)
    (List.replicate (U B q (B+1)) false) (Q+gs.length+1)) :=by
 obtain ⟨hn,hb,ht⟩:=PCJ45bee56da9f34d5a_NativeCircuitCodec.bounds gs top B hp
 exact (PCJ45bee56da9f34d5a_CircuitFlagRun.run gs live x pre top tail out B Q hn hb hp).enlarge
  (bound gs.length B q top.length (payload gs top).length hn ht hp)
end
end PCJ45bee56da9f34d5a_CircuitFlagCost
