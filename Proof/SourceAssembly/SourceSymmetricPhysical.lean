import Proof.SourceAssembly.SourceSymmetricReset
import Proof.SourceAssembly.SourceSymmetricAssemble

/- One fixed physical program consumes the real clause-query bank and produces
one complete native parity circuit with its original support stream. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourceSymmetricPhysical
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
open CloseoutRowsOriginalClause (index negative)
noncomputable section

def gates (q : Nat) (bits : List Bool) : List CloseoutRowsTupleSeek.GatePair:=
  (PCJ6e421fabe2aa4155_SourceSymmetricScan.selected bits q).map
    (fun j=>(bottomWord (Identity.onehot q j) 0,Identity.onehot q j))
theorem gates_length (q : Nat) (bits : List Bool) : (gates q bits).length=
    (PCJ6e421fabe2aa4155_SourceSymmetricScan.selected bits q).length:=List.length_map _
theorem gates_native (q : Nat) (bits : List Bool) : CloseoutRowsTupleSeek.nativeWord (gates q bits)=
    PCJ6e421fabe2aa4155_SourceSymmetricScan.outputs q bits q 0 := by
  simp only [CloseoutRowsTupleSeek.nativeWord,gates,List.flatMap_map]
  rfl
theorem gates_support (q : Nat) (bits : List Bool) : CloseoutRowsTupleSeek.supportWord (gates q bits)=
    PCJ6e421fabe2aa4155_SourceSymmetricScan.outputs q bits q 1 := by
  simp only [CloseoutRowsTupleSeek.supportWord,gates,List.flatMap_map]
  rfl

def slots : Fin 8→Fin 170:=![161,142,138,139,140,167,168,169]
theorem slots_inj : Function.Injective slots:=by decide
def direction (i : Fin 170):=if i=140 then HeadMove.right else .stay
def bump:=DecompositionCountPosition.move direction
def writer:=RecoveryFocus.machine slots PCJ6e421fabe2aa4155_SourceSymmetricAssemble.machine

end
end PCJ6e421fabe2aa4155_SourceSymmetricPhysical
