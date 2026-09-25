import Proof.SourceAssembly.SourceThresholdBounds

/- Paid rewind of the three completed logical streams, using the retained
quadratic C driver. Metadata and counted-loop driver remain outside the reset. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourceThresholdReady
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
open CloseoutRowsOriginalClause (index negative)
noncomputable section

def slots : Fin 5→Fin 210:=![199,200,204,101,206]
def last:=RecoveryFocus.machine slots (PCJ6e421fabe2aa4155_SourceClear.rewind 3)

end
end PCJ6e421fabe2aa4155_SourceThresholdReady
