import Proof.CaseAnalysis.RowsModeCacheSource

/-! The physically appended cache preserves every positional pair, in
ascending original occurrence order, and retains the full child count. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
open LocalBitMultitape ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def snapshot (j : Nat) : State:={initialState [] with index:=j}
def literalState (mode : Fin 3) (p : Parameters) (j : Nat):=selected mode p (guarded p (snapshot j))
def pairs (mode : Fin 3) (p : Parameters) (count : Nat):=
  (List.range count).map (fun j=>CloseoutRowsModeLiteralPair.pair
    (literalState mode p j).neg (literalState mode p j).var j)
def childBit (p : Parameters) (j : Nat):=(guarded p (snapshot j)).child

theorem piece_eq (mode : Fin 3) (p : Parameters) (j : Nat) :
    piece mode p (initialState []) j=CloseoutRowsRawPairSeek.word
      (CloseoutRowsModeLiteralPair.pair (literalState mode p j).neg (literalState mode p j).var j):=by
  simp only [piece,pairWord,literalState,selected,guarded,hashWord,label,track_index,initialState,
    Nat.zero_add,snapshot]

theorem source_word (mode : Fin 3) (p : Parameters) (count : Nat) :
    sourceWord mode p count=(pairs mode p count).flatMap CloseoutRowsRawPairSeek.word:=by
  simp only [sourceWord,pairs,List.flatMap_map]
  apply List.flatMap_congr
  intro j hj
  exact piece_eq mode p j

theorem child_bit (mode : Fin 3) (p : Parameters) (j : Nat) :
    (guarded p (track mode p (initialState []) j)).child=childBit p j:=by
  simp only [guarded,hashWord,label,track_index,initialState,Nat.zero_add,childBit,snapshot]

theorem child_count (mode : Fin 3) (p : Parameters) (count : Nat) :
    (track mode p (initialState []) count).children=
      ((List.range count).map (fun j=>(childBit p j).toNat)).sum:=by
  induction count with
  | zero=>rfl
  | succ count ih=>
    simp only [List.range_succ,List.map_append,List.map_singleton,List.sum_append,List.sum_singleton]
    change (track mode p (initialState []) count).children+
      (guarded p (track mode p (initialState []) count)).child.toNat=_
    rw [ih,child_bit]

end NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
