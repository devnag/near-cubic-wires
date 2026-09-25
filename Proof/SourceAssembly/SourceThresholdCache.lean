import Proof.SourceAssembly.SourceThresholdBitmap
import Proof.SourceAssembly.SourceThreshold

/- Actual clause query → native count/header plus retained bitmap cache used by
THR Cold. No bitmap, count, weight cache or capacity driver is assumed resident. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourceThresholdCache
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
open CloseoutRowsOriginalClause (index negative)
noncomputable section

def slots : Fin 7→Fin 170:=![3,135,101,166,167,168,169]
def last:=RecoveryFocus.machine slots PCJ6e421fabe2aa4155_SourceThresholdBitmap.machine


end
end PCJ6e421fabe2aa4155_SourceThresholdCache
