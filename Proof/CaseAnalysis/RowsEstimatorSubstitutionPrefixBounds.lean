import Proof.CaseAnalysis.RowsEstimatorSubstitutionCapacity
import Proof.CaseAnalysis.RowsEstimatorSubstitutionSemantic

/-! Every physical prefix fits the same paper-owned degree and child-count bound. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionBounds
open CanonicalFourfoldRowProgram CloseoutRowsRawPairSeek
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def widthBound (d W : ℕ):=d*W+W+4
def space (cs : List Pair) (B d W : ℕ):=capacity (SubstitutionCache.capacity cs) (B^d) (widthBound d W)

theorem shape_limit (B W k d : ℕ) (p : StructuralGF2Polynomial)
    (hB : 1 ≤ B) (hk : k ≤ d) (h : Shape B W k p) :
    p.length ≤ B^d ∧ Width p (d*W) := by
  constructor
  · exact h.count.trans (Nat.pow_le_pow_right hB hk)
  · intro l hl
    exact (h.width l hl).trans (Nat.mul_le_mul_right W hk)

theorem prefix_fits (cs : List Pair) (B W d : ℕ) (hB : 1 ≤ B)
    (hc : ∀ i (hi : i<cs.length),(cs[i].1++cs[i].2).length ≤ B)
    (hw : ∀ i (hi : i<cs.length),(ExtIncidence.stream (cs[i].1++cs[i].2)).length ≤ W)
    (m : List ℕ) (valid : SubstitutionMonomial.Valid cs m) (acc : StructuralGF2Polynomial)
    (k : ℕ) (hk : k+m.length ≤ d) (h : Shape B W k acc) :
    SubstitutionMonomial.Fits (space cs B d W) (rowCapacity (widthBound d W)) cs m valid acc ∧
    Shape B W (k+m.length) (SubstitutionMonomial.value cs m valid acc) := by
  induction m generalizing acc k with
  | nil=>simpa only [SubstitutionMonomial.Fits,SubstitutionMonomial.value,List.length_nil,Nat.add_zero] using And.intro True.intro h
  | cons i m ih=>
    let hi:=valid i (by simp)
    let atom:=cs[i].1++cs[i].2
    let next:=SubstitutionFactor.value cs i hi acc
    have hs : Shape B W (k+1) next:=shape_mul B W k acc atom h (hc i hi) (width_of_stream atom W (hw i hi))
    have hk' : k+1 ≤ d:=by simp only [List.length_cons] at hk;omega
    obtain ⟨ca,wa⟩:=shape_limit B W k d acc hB (by omega) h
    obtain ⟨cp,wp⟩:=shape_limit B W (k+1) d next hB hk' hs
    have first:=factor_fits (SubstitutionCache.capacity cs) (B^d) (widthBound d W) (d*W) W acc atom
      ca cp wa wp (hw i hi) (by unfold widthBound;omega) (by unfold widthBound;omega)
    obtain ⟨rest,shape⟩:=ih (fun j hj=>valid j (by simp [hj])) next (k+1)
      (by simp only [List.length_cons] at hk;omega) hs
    refine ⟨⟨first,rest⟩,?_⟩
    simpa only [SubstitutionMonomial.value,List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using shape

theorem monomial_fits (cs : List Pair) (B d : ℕ) (hB : 1 ≤ B)
    (hc : ∀ i (hi : i<cs.length),(cs[i].1++cs[i].2).length ≤ B)
    (m : List ℕ) (valid : SubstitutionMonomial.Valid cs m) (hd : m.length ≤ d) :
    SubstitutionOuter.Fits (space cs B d (cacheWord cs).length)
      (rowCapacity (widthBound d (cacheWord cs).length)) cs m valid := by
  let W:=(cacheWord cs).length
  obtain ⟨hf,hs⟩:=prefix_fits cs B W d hB hc (atom_word cs) m valid [[]] 0 (by simpa using hd) (unit_shape B W)
  rw [Nat.zero_add] at hs
  obtain ⟨hp,hwidth⟩:=shape_limit B W m.length d (SubstitutionMonomial.value cs m valid [[]]) hB hd hs
  have hw:=bounded_word _ (B^d) (d*W) (widthBound d W) hp hwidth (by unfold widthBound;omega)
  obtain ⟨_,_,hword,hcopy⟩:=capacity_bounds (SubstitutionCache.capacity cs) (B^d) (widthBound d W) (by unfold widthBound;omega)
  refine ⟨hf,?_,hw.trans hword⟩
  have ha:=CloseoutRowsRawProductBudget.row_bound [] (SubstitutionMonomial.value cs m valid [[]])
  simp only [List.flatMap_nil,List.length_nil,Nat.zero_add,Nat.mul_one] at ha
  change CloseoutRowsRawProductRow.budget [] (SubstitutionMonomial.value cs m valid [[]]) ≤
    capacity (SubstitutionCache.capacity cs) (B^d) (widthBound d W)
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionBounds
