import Proof.Packets.PacketsXVectorWorkerMetaUpdate
import Proof.Packets.PacketsXVectorWorkerProviderDock
import Proof.Packets.PacketsXVectorWorkerState

/-! Concrete per-level preparation: compute the runtime window, generate the
successor literal tag, and execute the finite ModeCache/literal/dense worker. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def levelFields (R root level : Nat) (fields : Fin 222→List Bool) :=
  Function.update (Function.update fields 118 (ZeroPadding.pad R (CompareMachine.word (GradedWindow.window root level))))
    153 (ZeroPadding.pad R (CompareMachine.word (level+1)))
def prepareBudget (R root level fuel : Nat) :=
  (2*R+3+GradedWindow.budget R root level)+1+((2*R+2*level+17)+1+fuel)

attribute [local irreducible] VectorWorkerArena.windowMachine VectorWorkerArena.deltaTag prepareLevel

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
