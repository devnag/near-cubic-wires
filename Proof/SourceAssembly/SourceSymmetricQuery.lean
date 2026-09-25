import Proof.SourceAssembly.SourceSymmetric

/- First actual synthetic source consumer: the queried clause itself supplies
the bitmap, arity, headers, scratch and loop driver consumed by the SYM scan. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourceSymmetricQuery
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
open CloseoutRowsOriginalClause (index negative)
noncomputable section

def slots : Fin 9→Fin 141:=![13,137,131,138,139,133,3,140,135]
theorem slots_inj : Function.Injective slots:=by decide
def last:=RecoveryFocus.machine slots PCJ6e421fabe2aa4155_SourceSymmetricCold.machine


theorem capacity_fit (q : Nat) : 2*(natWord q).length+1 ≤ Capacity.value q := by
  have hw : natBitLength q ≤ q+1:=Nat.add_le_add_right (Nat.log_le_self 2 q) 1
  simp only [DecompositionSource.natWord_length,Capacity.value]
  nlinarith

end
end PCJ6e421fabe2aa4155_SourceSymmetricQuery
