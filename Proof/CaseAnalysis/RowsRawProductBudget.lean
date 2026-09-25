import Proof.CaseAnalysis.RowsRawProductLoop

/-! One polynomial preparation envelope for the actual ordered-stream product.
The width is the logical encoded input, independent of allocated padding. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawProductBudget
open CloseoutRowsRawProductLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def inputLength (left right : List (List ℕ)) :=
  (ExtIncidence.stream left).length+(ExtIncidence.stream right).length

theorem monomial_le (left : List (List ℕ)) (l : List ℕ) (hl : l∈left) :
    (l.flatMap ExtIncidence.block).length+1≤(ExtIncidence.stream left).length := by
  induction left with
  | nil=>simp at hl
  | cons m left ih=>
    rw [ExtIncidence.stream_cons,List.length_append,ExtIncidence.monomialWord_length]
    rcases List.mem_cons.mp hl with rfl|hl
    · omega
    · have h:=ih hl;omega

theorem row_bound (l : List ℕ) (right : List (List ℕ)) :
    CloseoutRowsRawProductRow.budget l right≤
      16*((l.flatMap ExtIncidence.block).length+1)*((ExtIncidence.stream right).length+1) := by
  induction right with
  | nil=>simp [CloseoutRowsRawProductRow.budget,ExtIncidence.stream];omega
  | cons r right ih=>
    simp only [CloseoutRowsRawProductRow.budget,List.map_cons,List.sum_cons] at ih ⊢
    rw [ExtIncidence.stream_cons,List.length_append,ExtIncidence.monomialWord_length]
    unfold CloseoutRowsRawProductPair.budget at ih ⊢
    nlinarith

end NearCubicWires.RepairOrdinary.CloseoutRowsRawProductBudget
