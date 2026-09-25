import Proof.SourceAssembly.SourcePoolIndexLayout
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourcePoolIndex
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
open PCJ6fbdd6f776f6447d_Source

theorem port_join {α : Type} (a : DecompositionAlgorithm) (H : Fin (Cold.tapes a)→α)
    (x0 x1 x2 x3 x4 : α)
    (h0 : H (coldPorts a 0)=x0) (h1 : H (coldPorts a 1)=x1)
    (h2 : H (coldPorts a 2)=x2) (h3 : H (coldPorts a 3)=x3)
    (h4 : H (coldPorts a 4)=x4) :
    ∀ j,H (coldPorts a j)=PCJ6e421fabe2aa4155_SourceClear.join ![x0,x1,x2] x3 x4 j := by
  intro j
  fin_cases j
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
end PCJ6e421fabe2aa4155_SourcePoolIndex
