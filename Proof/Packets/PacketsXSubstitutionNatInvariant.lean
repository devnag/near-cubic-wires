import Proof.Packets.PacketsXSubstitutionScanNat
import Proof.Packets.PacketsXVectorAccumulatorNat

/-! Normality and unchanged-code bounds for every literal substitution
accumulator. These are exact list invariants, not evaluation equivalences. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionInvariant
open NearCubicWires NearCubicWires.CanonicalFourfoldRowProgram
open NormalizedFiniteTransport

def Good (C : Nat) (P : Ring.Poly Nat) := Fits C P ∧ Ring.Normal P

theorem fits_down {C : Nat} (P : Ring.Poly (Fin C)) : Fits C (down P) := by
  intro m hm j hj
  obtain ⟨n,_,rfl⟩:=List.mem_map.mp hm
  obtain ⟨i,_,rfl⟩:=List.mem_map.mp hj
  exact i.isLt

theorem fits_add {C : Nat} {P Q : Ring.Poly Nat} (hP : Fits C P) (hQ : Fits C Q) :
    Fits C (Ring.add P Q) := by
  have h:=fits_down (Ring.add (lift C P) (lift C Q))
  simpa only [add_down,lift_down C P hP,lift_down C Q hQ] using h

theorem fits_mul {C : Nat} {P Q : Ring.Poly Nat} (hP : Fits C P) (hQ : Fits C Q) :
    Fits C (Ring.mul P Q) := by
  have h:=fits_down (Ring.mul (lift C P) (lift C Q))
  simpa only [mul_down,lift_down C P hP,lift_down C Q hQ] using h

theorem good_zero (C : Nat) : Good C [] := by simp [Good,Fits,Ring.Normal]
theorem good_one (C : Nat) : Good C [[]] := by simp [Good,Fits,Ring.Normal]
theorem good_add {C : Nat} {P Q : Ring.Poly Nat} (hP : Good C P) (hQ : Good C Q) :
    Good C (Ring.add P Q) := ⟨fits_add hP.1 hQ.1,Ring.normal_add hP.2 hQ.2⟩
theorem good_mul {C : Nat} {P Q : Ring.Poly Nat} (hP : Good C P) (hQ : Good C Q) :
    Good C (Ring.mul P Q) := ⟨fits_mul hP.1 hQ.1,Ring.normal_mul _ _⟩

theorem get_good (C : Nat) (atoms : List (Ring.Poly Nat)) (ha : ∀ P∈atoms,Good C P) (j : Nat) :
    Good C (atoms.getD j []) := by
  by_cases hj : j<atoms.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact ha _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact good_zero C

theorem product_good (C : Nat) (ps : List (Ring.Poly Nat)) (hps : ∀ P∈ps,Good C P) :
    Good C (NormalizedFolds.product ps) := by
  rw [NormalizedFolds.product_exact]
  change Good C (ps.foldr Ring.mul [[]])
  induction ps with
  | nil=>exact good_one C
  | cons P ps ih=>exact good_mul (hps P (by simp)) (ih (fun Q hQ=>hps Q (by simp [hQ])))

theorem monomial_good (C : Nat) (atoms : List (Ring.Poly Nat)) (ha : ∀ P∈atoms,Good C P) (m : List Nat) :
    Good C (NormalizedFolds.product (m.map (fun j=>atoms.getD j []))) := by
  apply product_good
  intro P hp
  obtain ⟨j,_,rfl⟩:=List.mem_map.mp hp
  exact get_good C atoms ha j

def partialSum (atoms : List (Ring.Poly Nat)) (P : Ring.Poly Nat) (k : Nat) :=
  (P.reverse.take k).foldl
    (fun acc m=>Ring.add (NormalizedFolds.product (m.map (fun j=>atoms.getD j []))) acc) []

theorem partialSum_good (C : Nat) (atoms : List (Ring.Poly Nat)) (ha : ∀ P∈atoms,Good C P)
    (P : Ring.Poly Nat) (k : Nat) : Good C (partialSum atoms P k) := by
  have aux (ms : List (List Nat)) (initial : Ring.Poly Nat) (hi : Good C initial) :
      Good C (ms.foldl
        (fun acc m=>Ring.add (NormalizedFolds.product (m.map (fun j=>atoms.getD j []))) acc) initial) := by
    induction ms generalizing initial with
    | nil=>exact hi
    | cons m ms ih=>exact ih _ (good_add (monomial_good C atoms ha m) hi)
  exact aux _ [] (good_zero C)

theorem partialSum_succ (atoms : List (Ring.Poly Nat)) (P : Ring.Poly Nat) (k : Nat) (hk : k<P.length) :
    partialSum atoms P (k+1)=Ring.add
      (NormalizedFolds.product ((P.getD (P.length-(k+1)) []).map (fun j=>atoms.getD j [])))
      (partialSum atoms P k) := by
  have hr : k<P.reverse.length := by simpa only [List.length_reverse] using hk
  have hj : P.length-(k+1)<P.length := by omega
  unfold partialSum
  rw [List.take_succ_eq_append_getElem hr,List.foldl_append]
  simp only [List.foldl_cons,List.foldl_nil,List.getElem_reverse]
  rw [List.getD_eq_getElem _ _ hj]
  simp only [Nat.sub_sub,Nat.add_comm 1 k]

theorem partialSum_complete (atoms : List (Ring.Poly Nat)) (P : Ring.Poly Nat) :
    partialSum atoms P P.length=Normalized.structuralGF2Substitute (fun j=>atoms.getD j []) P := by
  rw [←NormalizedFolds.substitute_exact]
  unfold partialSum NormalizedFolds.substitute
  rw [List.take_of_length_le (by simp)]

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionInvariant
