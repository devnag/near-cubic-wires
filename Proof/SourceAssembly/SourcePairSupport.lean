import Proof.SourceAssembly.SourceLiteralGuard

/- The actual queried clause produces both systematic-support bitmaps using one
fixed program. Auxiliary references are guarded; repeated references and empty
systematic supports are included. The original clause cache stays retained. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourcePairSupport
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound
open CloseoutRowsOriginalClause (index negative)
open PCJ6e421fabe2aa4155_SourceLiteralSupport
noncomputable section
attribute [local irreducible] PCPPQuerySupportReuse.machine

theorem projections (side : Bool) (source pair : List Bool) (q ci Q k C : Nat)
    (A : Fin 91→List Bool)
    (cache : ∀ j : Fin 19,A (j.castAdd 72)=PCPPQueryIndexPadding.clauseData source q ci Q pair j)
    (index : A (refPort side)=ZeroPadding.pad C (UnaryTemplate.tape k)) :
    ∀ i,A (slots side i)=words source q k Q C [] i := by
  intro i;fin_cases i
  · simpa [slots,words,caps,PCPPQuerySupportReuse.data,ZeroPadding.pad_zero,
      PCPPQueryIndexPadding.clauseData,PCPPQueryClauseReuse.data] using cache 0
  · simpa [slots,words,caps,PCPPQuerySupportReuse.data,ZeroPadding.pad_zero,
      PCPPQueryIndexPadding.clauseData,PCPPQueryClauseReuse.data] using cache 1
  · simpa [slots,words,caps,PCPPQuerySupportReuse.data,ZeroPadding.pad_zero,
      PCPPQueryIndexPadding.clauseData,PCPPQueryClauseReuse.data] using cache 2
  · simpa [slots,words,caps,PCPPQuerySupportReuse.data,ZeroPadding.pad_zero,
      PCPPQueryIndexPadding.clauseData,PCPPQueryClauseReuse.data] using cache 13
  · cases side
    · simpa [slots,outPort,words,caps,PCPPQuerySupportReuse.data,ZeroPadding.pad_zero,
        PCPPQueryIndexPadding.clauseData,PCPPQueryClauseReuse.data,ZeroPadding.pad] using cache 3
    · simpa [slots,outPort,words,caps,PCPPQuerySupportReuse.data,ZeroPadding.pad_zero,
        PCPPQueryIndexPadding.clauseData,PCPPQueryClauseReuse.data,ZeroPadding.pad] using cache 4
  · exact index
  · simpa [slots,words,caps,PCPPQuerySupportReuse.data,ZeroPadding.pad_zero,
      PCPPQueryIndexPadding.clauseData,PCPPQueryClauseReuse.data] using cache 16
  · simpa [slots,words,caps,PCPPQuerySupportReuse.data,ZeroPadding.pad_zero,
      PCPPQueryIndexPadding.clauseData,PCPPQueryClauseReuse.data] using cache 17
  · simpa [slots,words,caps,PCPPQuerySupportReuse.data,ZeroPadding.pad_zero,
      PCPPQueryIndexPadding.clauseData,PCPPQueryClauseReuse.data] using cache 18

def finish := DecompositionCountPosition.move (fun i : Fin 91=>if i=13 ∨ i=14 then .left else .stay)

theorem finish_run (A : Fin 91→List Bool) : Step finish 1 H A (fun _=>0) A := by
  obtain ⟨s,hs,hf,_⟩:=DecompositionCountPosition.move_run
    (fun i : Fin 91=>if i=13 ∨ i=14 then .left else .stay) H A
  apply Step.of_run hs
  · rw [hf];funext i;fin_cases i <;>rfl
  · rw [hf]

end
end PCJ6e421fabe2aa4155_SourcePairSupport
