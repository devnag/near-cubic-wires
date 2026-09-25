import Proof.SourceAssembly.SourceThresholdCache

/- Actual queried support/cache/count → reusable THR staircase loop. The33
callee inputs are docked from five retained tapes and freshly allocated work. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourceThresholdQuery
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
open CloseoutRowsOriginalClause (index negative)
noncomputable section

def slots (i : Fin 33) : Fin 203:=if i=22 then 101 else if i=26 then 131 else if i=27 then 166 else
  if i=28 then 167 else if i=32 then 140 else i.natAdd 170
theorem slots_inj : Function.Injective slots:=by decide
def oldSlots : Fin 5→Fin 170:=![101,131,166,167,140]
def last:=RecoveryFocus.machine slots PCJ6e421fabe2aa4155_SourceThresholdCold.machine

end
end PCJ6e421fabe2aa4155_SourceThresholdQuery
