import Proof.SourceAssembly.SourceSymmetricBound
import Proof.SourceAssembly.SourceClear

/- The actual local C driver rewinds only the two produced bottom streams.
The potentially much longer retained query bitmap is outside this bank. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourceSymmetricReset
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
open CloseoutRowsOriginalClause (index negative)
noncomputable section

def slots : Fin 4→Fin 170:=![138,139,101,166]
def last:=RecoveryFocus.machine slots (PCJ6e421fabe2aa4155_SourceClear.rewind 2)

end
end PCJ6e421fabe2aa4155_SourceSymmetricReset
