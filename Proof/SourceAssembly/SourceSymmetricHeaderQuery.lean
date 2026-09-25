import Proof.SourceAssembly.SourceSymmetricHeader

/- Consume the actual selected-count tape produced by the queried SYM scan.
Its bottom streams retain their append cursors while TOP/header are produced. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
open CloseoutRowsOriginalClause (index negative)
noncomputable section

def slots (i : Fin 26) : Fin 166:=if _h3:i=3 then 140 else if h:i.val<3 then ⟨141+i.val,by omega⟩ else ⟨140+i.val,by omega⟩
theorem slots_inj : Function.Injective slots:=by decide
def fresh (i : Fin 26) (_hi : i≠3) : Fin 25:=⟨if i.val<3 then i.val else i.val-1,by split_ifs <;>have hv:=i.isLt <;>omega⟩
theorem slots_fresh (i : Fin 26) (hi : i≠3) : slots i=(fresh i hi).natAdd 141 := by
  apply Fin.ext
  by_cases h:i.val<3
  · simp [slots,hi,fresh,h]
  · simp [slots,hi,fresh,h]
    have hn:i.val≠3:=by intro he;exact hi (Fin.ext he)
    omega

def last:=RecoveryFocus.machine slots PCJ6e421fabe2aa4155_SourceSymmetricHeader.machine

end
end PCJ6e421fabe2aa4155_SourceSymmetricHeaderQuery
