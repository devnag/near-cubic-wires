import Proof.SourceAssembly.SourceParityPrep

/- Actual queried clause -> actual support bitmaps and paid SYM writer inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourceParityQuery
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
open CloseoutRowsOriginalClause (index negative)
noncomputable section

def slots (i : Fin 47) : Fin 137:=if i=0 then 13 else ⟨90+i.val,by omega⟩
theorem slots_inj : Function.Injective slots:=by decide

theorem arity_eq (q : Nat) : UnaryTemplate.tape q=UWalkUnary.source (q+2) q := by
  simp [UnaryTemplate.tape,UWalkUnary.source,ZeroPadding.pad,CompareMachine.word]

end
end PCJ6e421fabe2aa4155_SourceParityQuery
