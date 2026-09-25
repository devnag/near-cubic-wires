import Proof.Packets.SubstitutionOuterLoop
import Proof.Packets.PacketsXSubstitutionNatInvariant

/-! The actual outer loop agrees with the frozen natural-code substitution,
including the exact order of every monomial and parity accumulator. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionOuter
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.ExtDecompositionBatch
open NormalizedFiniteTransport SubstitutionInvariant

def nativeMasks (C : Nat) (P : Ring.Poly Nat) := (P.map (maskNat C)).flatten
def atomMasks (C : Nat) (atoms : List (Ring.Poly Nat)) := atoms.map (List.map (maskNat C))

theorem nativeMasks_length (C : Nat) (P : Ring.Poly Nat) : (nativeMasks C P).length=P.length*C := by
  induction P with
  | nil=>simp [nativeMasks]
  | cons m P ih=>
    simp only [nativeMasks,List.map_cons,List.flatten_cons,List.length_append,maskNat,List.length_ofFn,
      List.length_cons] at *
    nlinarith

theorem nativeMasks_split (C : Nat) (P : Ring.Poly Nat) (j : Fin P.length) :
    nativeMasks C P=nativeMasks C (P.take j.val)++maskNat C P[j.val]++nativeMasks C (P.drop (j.val+1)) := by
  have hp : P.take j.val++P[j.val]::P.drop (j.val+1)=P := by
    rw [List.getElem_cons_drop,List.take_append_drop]
  conv_lhs=>rw [←hp]
  simp only [nativeMasks,List.map_append,List.map_cons,List.flatten_append,List.flatten_cons,List.append_assoc]

theorem product_at (C : Nat) (P : Ring.Poly Nat) (hP : Good C P)
    (atoms : List (Ring.Poly Nat)) (ha : ∀ Q∈atoms,Good C Q) (left : Packet) (j : Fin P.length) :
    (productState C (j.val*C) (nativeMasks C P) (atomMasks C atoms) left).2=
      (NormalizedFolds.product (P[j.val].map (fun code=>atoms.getD code []))).map (maskNat C) := by
  have h:=SubstitutionScan.monomial_nat C (nativeMasks C (P.take j.val))
    (nativeMasks C (P.drop (j.val+1))) P[j.val] (hP.2.2 _ (List.getElem_mem j.isLt))
    (hP.1 _ (List.getElem_mem j.isLt)) atoms (fun Q hQ=>(ha Q hQ).1) left
  have hpre : (nativeMasks C (P.take j.val)).length=j.val*C := by
    rw [nativeMasks_length,List.length_take,Nat.min_eq_left j.isLt.le]
  rw [hpre,←nativeMasks_split C P j] at h
  exact h

theorem product_at_k (C : Nat) (P : Ring.Poly Nat) (hP : Good C P)
    (atoms : List (Ring.Poly Nat)) (ha : ∀ Q∈atoms,Good C Q) (left : Packet) (k : Nat) (hk : k<P.length) :
    (productState C ((P.length-(k+1))*C) (nativeMasks C P) (atomMasks C atoms) left).2=
      (NormalizedFolds.product ((P.getD (P.length-(k+1)) []).map (fun code=>atoms.getD code []))).map (maskNat C) := by
  have hj : P.length-(k+1)<P.length := by omega
  rw [List.getD_eq_getElem _ _ hj]
  exact product_at C P hP atoms ha left ⟨_,hj⟩

theorem fold_partialSum (C : Nat) (P : Ring.Poly Nat) (hP : Good C P)
    (atoms : List (Ring.Poly Nat)) (ha : ∀ Q∈atoms,Good C Q) (left : Packet) (k : Nat) (hk : k≤P.length) :
    (fold C P.length (nativeMasks C P) (atomMasks C atoms) left [] k).2=
      (partialSum atoms P k).map (maskNat C) := by
  induction k with
  | zero=>rfl
  | succ k ih=>
    have hlt : k<P.length := by omega
    let prior:=fold C P.length (nativeMasks C P) (atomMasks C atoms) left [] k
    change VectorAccumulator.answer
      (productState C ((P.length-(k+1))*C) (nativeMasks C P) (atomMasks C atoms) prior.1).2 prior.2=_
    rw [product_at_k C P hP atoms ha prior.1 k hlt]
    change VectorAccumulator.answer _
      (fold C P.length (nativeMasks C P) (atomMasks C atoms) left [] k).2=_
    rw [ih (by omega),partialSum_succ atoms P k hlt]
    have hp:=monomial_good C atoms ha (P.getD (P.length-(k+1)) [])
    have hs:=partialSum_good C atoms ha P k
    exact VectorAccumulator.answer_nat C _ _ hp.1 hs.1 hp.2 hs.2

theorem fold_exact (C : Nat) (P : Ring.Poly Nat) (hP : Good C P)
    (atoms : List (Ring.Poly Nat)) (ha : ∀ Q∈atoms,Good C Q) (left : Packet) :
    (fold C P.length (nativeMasks C P) (atomMasks C atoms) left [] P.length).2=
      (Normalized.structuralGF2Substitute (fun code=>atoms.getD code []) P).map (maskNat C) := by
  rw [fold_partialSum C P hP atoms ha left P.length (Nat.le_refl _),partialSum_complete]

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionOuter
