import Proof.Circuits.DecompositionCachedChildPosition

/-! The cursor of the paid native-cache scan points at exactly the selected
child, and its cost is bounded by the retained cache and actual arity/count. -/
namespace NearCubicWires.RepairOrdinary.DecompositionCachedChild
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem selected_word {n : ℕ} (gs : List (ExactThresholdGate n)) (i : ℕ) (hi : i<gs.length) :
    exactListWord gs=(natWord gs.length++(gs.take i).flatMap exactWord)++
      exactWord gs[i]++(gs.drop (i+1)).flatMap exactWord := by
  have hs : gs.take i++gs[i]::gs.drop (i+1)=gs := by
    rw [←List.drop_eq_getElem_cons hi]
    exact List.take_append_drop i gs
  have h := congrArg (fun xs : List (ExactThresholdGate n) =>
    natWord gs.length++xs.flatMap exactWord) hs
  simpa only [List.flatMap_append,List.flatMap_cons,List.append_assoc,exactListWord] using h.symm

theorem budget_bound {n : ℕ} (gs : List (ExactThresholdGate n)) (i : ℕ) (hi : i ≤ gs.length) :
    budget gs i ≤ (exactListWord gs).length+(6*n+10)*gs.length+7 := by
  have hw : natWord gs.length++(gs.take i).flatMap exactWord++(gs.drop i).flatMap exactWord=
      exactListWord gs := by
    rw [List.append_assoc,←List.flatMap_append,List.take_append_drop]
    rfl
  have hl := congrArg List.length hw
  simp only [List.length_append,DecompositionSource.natWord_length] at hl
  have hm := Nat.mul_le_mul_left (6*n+10) hi
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.DecompositionCachedChild
