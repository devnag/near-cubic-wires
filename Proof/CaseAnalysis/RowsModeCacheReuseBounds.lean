import Proof.CaseAnalysis.RowsModeCacheCount

/-! The actual population execution bounds its two distinct counters.
The reusable bank needs only linear backing in the original population. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
open LocalBitMultitape ExtDecompositionBatch RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def privateSlots : Fin 15→Fin 25:=![1,4,6,7,8,10,13,14,15,16,17,18,19,22,23]
def reuseCapacity (p : Parameters) (M : Nat):=p.C+M+p.rank+4

theorem track_counts (mode : Fin 3) (p : Parameters) (M : Nat) :
    (track mode p (initialState []) M).selectedCount ≤ M ∧
    (track mode p (initialState []) M).children ≤ M:=by
  induction M with
  | zero=>simp [track,initialState]
  | succ M ih=>
    have hv:((selected mode p (guarded p (track mode p (initialState []) M))).var).toNat ≤ 1:=by
      cases (selected mode p (guarded p (track mode p (initialState []) M))).var <;> decide
    have hc:((guarded p (track mode p (initialState []) M)).child).toNat ≤ 1:=by
      cases (guarded p (track mode p (initialState []) M)).child <;> decide
    change (track mode p (initialState []) M).selectedCount+_ ≤ M+1 ∧
      (track mode p (initialState []) M).children+_ ≤ M+1
    omega

theorem private_length (p : Parameters) (M : Nat) (s : State)
    (hi : s.index ≤ M) (hs : s.selectedCount ≤ M) (hc : s.children ≤ M) (i : Fin 15) :
    (loopData p s M (privateSlots i)).length ≤ reuseCapacity p M:=by
  fin_cases i <;>
    simp [privateSlots,loopData,data,fields,CloseoutRowsModeHashFields.before,extras,label,
      Fin.addCases,SignedSortKey.binary,UnaryTemplate.tape,CompareMachine.word,reuseCapacity] <;> omega

theorem final_private_length (mode : Fin 3) (p : Parameters) (M : Nat) (out : List Bool) (i : Fin 15) :
    (loopData p (atState mode p (initialState []) M out) M (privateSlots i)).length ≤ reuseCapacity p M:=by
  apply private_length
  · simpa only [atState,initialState,Nat.zero_add] using (track_index mode p (initialState []) M).le
  · exact (track_counts mode p M).1
  · exact (track_counts mode p M).2

end NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
