import Proof.CaseAnalysis.RowsEstimatorSubstitutionPrefixBounds

/-! The complete actual receipt has one expansion factor and polynomial overhead. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionBounds
open CanonicalFourfoldRowProgram CloseoutRowsRawPairSeek
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem factor_time (C R : ℕ) (cs : List Pair) (i : ℕ) (hi : i<cs.length)
    (acc : StructuralGF2Polynomial) (hc : SubstitutionCache.capacity cs ≤ C)
    (h : SubstitutionFactor.Fits C R acc (cs[i].1++cs[i].2)) :
    SubstitutionFactor.budget R cs i hi acc ≤ 32*C := by
  have ha:=SubstitutionCache.budget_bound cs i hi
  have hp:=h.productTime
  have hl:=h.accLength
  have ht:=h.atomLength
  have hcp:=h.copyTime
  have hpl:=h.productLength
  unfold SubstitutionFactor.budget SubstitutionProduct.budget SubstitutionCopy.budget
  unfold SubstitutionFactor.value
  unfold SubstitutionCache.capacity at hc
  omega

theorem monomial_time (C R : ℕ) (cs : List Pair) (m : List ℕ) (valid : SubstitutionMonomial.Valid cs m)
    (acc : StructuralGF2Polynomial) (hc : SubstitutionCache.capacity cs ≤ C)
    (h : SubstitutionMonomial.Fits C R cs m valid acc) :
    SubstitutionMonomial.budget R cs m valid acc ≤ m.length*(32*C+2)+1 := by
  induction m generalizing acc with
  | nil=>simp [SubstitutionMonomial.budget]
  | cons i m ih=>
    have first:=factor_time C R cs i (valid i (by simp)) acc hc h.1
    have rest:=ih (fun j hj=>valid j (by simp [hj])) (SubstitutionFactor.value cs i (valid i (by simp)) acc) h.2
    simp only [SubstitutionMonomial.budget,List.length_cons]
    nlinarith

theorem body_time (C R : ℕ) (cs : List Pair) (m : List ℕ) (valid : SubstitutionMonomial.Valid cs m)
    (hc : SubstitutionCache.capacity cs ≤ C) (h : SubstitutionOuter.Fits C R cs m valid) :
    SubstitutionOuter.bodyBudget R cs m valid ≤ 64*(m.length+1)*C := by
  have hm:=monomial_time C R cs m valid [[]] hc h.factors
  have hp:=h.appendTime
  have hl:=h.resultLength
  have hC : 1 ≤ C:=by unfold SubstitutionCache.capacity at hc;omega
  unfold SubstitutionOuter.bodyBudget SubstitutionAppend.budget
  nlinarith

theorem outer_time (C R d : ℕ) (cs : List Pair) (p : StructuralGF2Polynomial)
    (valid : SubstitutionOuter.Valid cs p) (hc : SubstitutionCache.capacity cs ≤ C)
    (hf : ∀ m hm,SubstitutionOuter.Fits C R cs m (valid m hm)) (hd : ∀ m∈p,m.length ≤ d) :
    SubstitutionOuter.budget R cs p valid ≤ p.length*(64*(d+1)*C+2)+1 := by
  induction p with
  | nil=>simp [SubstitutionOuter.budget]
  | cons m p ih=>
    have first:=body_time C R cs m (valid m (by simp)) hc (hf m (by simp))
    have hm:=Nat.mul_le_mul_right C (Nat.mul_le_mul_left 64 (Nat.add_le_add_right (hd m (by simp)) 1))
    have rest:=ih (fun n hn=>valid n (by simp [hn])) (fun n hn=>hf n (by simp [hn])) (fun n hn=>hd n (by simp [hn]))
    simp only [SubstitutionOuter.budget,List.length_cons]
    nlinarith

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionBounds
