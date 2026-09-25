import Proof.Packets.CycleFieldPrimitives

/-! A raw unary capacity physically allocates a fixed block of zero tapes.
The rewind log is also created by execution; no preallocated zero bank is assumed. -/
set_option autoImplicit false
set_option warningAsError true
namespace CycleFields.ZeroAllocate
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound

def machine (t : Nat):=RecoveryScratchErase.resetMachine t
def input (t capacity : Nat) : Fin (t+1+1)→List Bool:=
  Fin.addCases (m:=t+1) (n:=1) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=t) (n:=1) (motive:=fun _=>List Bool)
      (fun _=>[]) (fun _=>List.replicate capacity true)) (fun _=>[])
def output (t capacity : Nat):=Primitives.eraseOutput t capacity (capacity+1)

theorem run (t capacity : Nat) :
    Step (machine t) (2*capacity+4) (fun _=>0) (input t capacity)
      (fun _=>0) (output t capacity) := by
  have h:=Step.of_ready (RecoveryScratchErase.erase_ready capacity 0 (fun _ : Fin t=>[])
    (by intro i;exact Nat.zero_le _))
  refine (h.congr_in rfl ?_).congr rfl ?_
  · funext i;rfl
  · funext i
    simp only [output,Primitives.eraseOutput,Primitives.eraseInput,Nat.zero_max]

end CycleFields.ZeroAllocate
