import Proof.CaseAnalysis.RowsModeEnumeratorReady
import Proof.CaseAnalysis.RowsModeTuple

/-! An actual cold binary subset enumeration is consumed by the ordinary
raw monomial writer. The initial bank contains only the four numeric fields;
its output is appended in the enumerator's positional occurrence order. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeElementary
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extraHeads (out : List Bool) : Fin 4→Nat:=![0,0,0,out.length]
def extraTapes (out : List Bool) : Fin 4→List Bool:=![[],[],[],out]
def heads (out : List Bool) : Fin 45→Nat:=Fin.addCases (m:=41) (n:=4) (motive:=fun _=>Nat) (fun _=>0) (extraHeads out)
def input (w k M : Nat) (out : List Bool) : Fin 45→List Bool:=
  Fin.addCases (m:=41) (n:=4) (motive:=fun _=>List Bool) (RowTupleEnumerationReady.input w k M) (extraTapes out)
def slots : Fin 7→Fin 45:=![17,41,2,42,43,44,12]
noncomputable def first : Σ s,Machine 45 s:=⟨_,TapeEmbedding.machine 4 RowTupleEnumerationReady.machine⟩
noncomputable def last : Σ s,Machine 45 s:=⟨_,RecoveryFocus.machine slots CloseoutRowsModeTuplePolynomial.machine⟩
noncomputable def machine:=Composition.machine first.2 last.2
def monomials (w k M : Nat):=RowTupleSubsets.selected w M k
def bodyWord (w k M : Nat):=(monomials w k M).flatMap ExtIncidence.monomialWord
def budget (w k M : Nat):=RowTupleEnumerationReady.budget w k+1+
  CloseoutRowsModeTuplePolynomial.budget w k M (monomials w k M).length

theorem selected_fields (w k M : Nat) (ds : List Nat) (hs : ds∈monomials w k M) :
    ds.length=k ∧ (∀ d∈ds,d<2^w) ∧ (∀ d∈ds,d<M) := by
  obtain ⟨hc,hv⟩:=List.mem_filter.mp hs
  obtain ⟨hk,hd⟩:=(RowTupleDigits.candidates_mem w k ds).mp hc
  exact ⟨hk,hd,(RowTupleSubsets.valid_iff M ds).mp hv |>.2⟩

theorem source_word (w k M : Nat) :
    CloseoutRowsModeTuplePolynomial.sourceWord w (monomials w k M)=RowTupleEnumeration.word w k M := by
  unfold CloseoutRowsModeTuplePolynomial.sourceWord RowTupleEnumeration.word
  apply List.flatMap_congr
  intro ds hs
  rw [RowTupleFramedBody.word,(selected_fields w k M ds hs).1]

theorem elementary_run (w k M : Nat) (out : List Bool) (hM : 0<M) (hMw : M≤2^w) :
    ∃ r,runFrom machine (budget w k M) ⟨machine.start,heads out,input w k M out⟩=some r ∧
      r.final.tapes 44=out++bodyWord w k M ∧ r.final.heads 44=(out++bodyWord w k M).length ∧
      r.final.tapes 2=CompareMachine.word w ∧ r.final.tapes 12=CompareMachine.word k ∧
      r.final.heads 2=1 ∧ r.final.heads 12=1 ∧ r.steps≤budget w k M := by
  obtain ⟨a,ha,a17,ah17,a2,a12,ah2,ah12,_⟩:=CloseoutRowsModeEnumeratorReady.ready_run w k M hM hMw
  let ar:=TapeEmbedding.receipt (extraHeads out) (extraTapes out) a
  have har:=TapeEmbedding.run_embed RowTupleEnumerationReady.machine (extraHeads out) (extraTapes out) _ _ a ha
  have initial:TapeEmbedding.config (extraHeads out) (extraTapes out)
      (initialConfiguration RowTupleEnumerationReady.machine (RowTupleEnumerationReady.input w k M))=
      (⟨first.2.start,heads out,input w k M out⟩ : Configuration 45 first.1):=by rfl
  rw [initial] at har
  obtain ⟨b,hb,bh,_,b2,b5,b6,_⟩:=CloseoutRowsModeTupleCold.writer_run w k M (monomials w k M) out
    (fun ds hs=>(selected_fields w k M ds hs).1)
    (fun ds hs=>(selected_fields w k M ds hs).2.1)
    (fun ds hs d hd=>((selected_fields w k M ds hs).2.2 d hd).le)
  have hheads:∀ i,ar.final.heads (slots i)=CloseoutRowsModeTupleMonomial.heads 0 out i:=by
    intro i;fin_cases i
    · exact ah17
    · rfl
    · exact ah2
    · rfl
    · rfl
    · rfl
    · exact ah12
  have htapes:∀ i,ar.final.tapes (slots i)=CloseoutRowsModeTupleCold.input w k
      (CloseoutRowsModeTuplePolynomial.sourceWord w (monomials w k M)) out i:=by
    intro i;fin_cases i
    · exact a17.trans (source_word w k M).symm
    · rfl
    · exact a2
    · rfl
    · rfl
    · rfl
    · exact a12
  obtain ⟨br,hbr,_,_,brh,brt,_⟩:=RecoveryFocus.dock slots (by decide)
    CloseoutRowsModeTuplePolynomial.machine _ ar.final.heads ar.final.tapes _ hheads htapes b hb
  have whole:=Composition.run_join first.2 last.2 _ _ _ ar br har hbr
  refine ⟨Composition.joinedReceipt ar br,whole,(brt 5).trans b5,?_,
    (brt 2).trans b2,(brt 6).trans b6,?_,?_,runFrom_steps_le machine _ _ _ whole⟩
  · exact (brh 5).trans (congrFun bh 5)
  · exact (brh 2).trans (congrFun bh 2)
  · exact (brh 6).trans (congrFun bh 6)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeElementary
