import Proof.SourceAssembly.SourceThresholdReady

/- Full fixed physical THR parity-circuit producer from the actual queried
bank. Every source field and rewind driver comes from the paid prefix. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourceThresholdPhysical
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
open CloseoutRowsOriginalClause (index negative)
noncomputable section

def gates (q n : Nat) (bits : List Bool) : List CloseoutRowsTupleSeek.GatePair:=
  (List.range n).map (fun j=>(natWord q++weights bits++false::natWord j,bits))
theorem gates_length (q n : Nat) (bits : List Bool) : (gates q n bits).length=n:=by simp [gates]
theorem gates_native (q n : Nat) (bits : List Bool) : CloseoutRowsTupleSeek.nativeWord (gates q n bits)=
    PCJ6e421fabe2aa4155_SourceThresholdLoop.outputs q bits n 0 := by
  simp only [CloseoutRowsTupleSeek.nativeWord,gates,List.flatMap_map];rfl
theorem gates_support (q n : Nat) (bits : List Bool) : CloseoutRowsTupleSeek.supportWord (gates q n bits)=
    PCJ6e421fabe2aa4155_SourceThresholdLoop.outputs q bits n 1 := by
  simp only [CloseoutRowsTupleSeek.supportWord,gates,List.flatMap_map];rfl

def native (q n : Nat) (bits : List Bool):=PCJ6e421fabe2aa4155_SourceSymmetricAssemble.circuitWord
  (PCJ6e421fabe2aa4155_SourceThresholdTop.payload n) (gates q n bits)
def slots : Fin 8→Fin 210:=![161,204,199,200,140,207,208,209]
theorem slots_inj : Function.Injective slots:=by decide
def writer:=RecoveryFocus.machine slots PCJ6e421fabe2aa4155_SourceSymmetricAssemble.machine

end
end PCJ6e421fabe2aa4155_SourceThresholdPhysical
