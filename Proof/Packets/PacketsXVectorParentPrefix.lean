import Proof.Packets.PacketsXVectorChildTransactionNat
import Proof.Packets.PacketsXNormalizedIntermediate
import Proof.Packets.PacketsXSubstitutionNatInvariant

/-! The literal forward prefix used by the physical parent accumulator.
Products are child*delta and summation is foldl acc+term, exactly as in the
original normalized level constructor. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorParentPrefix
open NearCubicWires NearCubicWires.CanonicalFourfoldRowProgram
open NormalizedFiniteTransport

def terms (ps : List (Ring.Poly Nat)) (delta : Nat→Ring.Poly Nat) : List (Ring.Poly Nat) :=
  List.ofFn (fun i : Fin ps.length=>Ring.mul ps[i.val] (delta i.val))
def value (ps : List (Ring.Poly Nat)) (delta : Nat→Ring.Poly Nat) (n : Nat) : Ring.Poly Nat :=
  ((terms ps delta).take n).foldl Ring.add []

theorem terms_length (ps : List (Ring.Poly Nat)) (delta : Nat→Ring.Poly Nat) :
    (terms ps delta).length=ps.length := List.length_ofFn

theorem succ (ps : List (Ring.Poly Nat)) (delta : Nat→Ring.Poly Nat) (n : Nat) (hn : n<ps.length) :
    value ps delta (n+1)=Ring.add (value ps delta n) (Ring.mul ps[n] (delta n)) := by
  unfold value
  rw [List.take_succ_eq_append_getElem (by rw [terms_length];exact hn)]
  simp only [List.foldl_append,List.foldl_cons,List.foldl_nil,terms,List.getElem_ofFn]

theorem finish (ps : List (Ring.Poly Nat)) (delta : Nat→Ring.Poly Nat) :
    value ps delta ps.length=Normalized.structuralGF2Sum (terms ps delta) := by
  unfold value
  rw [←terms_length ps delta,List.take_length]
  rfl

theorem good (C : Nat) (ps : List (Ring.Poly Nat)) (delta : Nat→Ring.Poly Nat)
    (hps : ∀ P∈ps,Fits C P) (hd : ∀ i,i<ps.length→Fits C (delta i)) (n : Nat) :
    SubstitutionInvariant.Good C (value ps delta n) := by
  have ht : ∀ P∈terms ps delta,SubstitutionInvariant.Good C P := by
    intro P hp
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hp
    exact ⟨VectorChildTransaction.term_fits C _ _ (hps _ (List.getElem_mem i.isLt)) (hd i.val i.isLt),
      Ring.normal_mul _ _⟩
  have foldgood (qs : List (Ring.Poly Nat)) (hq : ∀ Q∈qs,SubstitutionInvariant.Good C Q)
      (init : Ring.Poly Nat) (hi : SubstitutionInvariant.Good C init) :
      SubstitutionInvariant.Good C (qs.foldl Ring.add init) := by
    induction qs generalizing init with
    | nil=>exact hi
    | cons Q qs ih=>
      exact ih (fun P hp=>hq P (by simp [hp])) _ (SubstitutionInvariant.good_add hi (hq Q (by simp)))
  exact foldgood _ (fun Q hQ=>ht Q (List.mem_of_mem_take hQ)) [] (SubstitutionInvariant.good_zero C)

theorem bounded (S : Finset Nat) (d : Nat) (ps : List (Ring.Poly Nat)) (delta : Nat→Ring.Poly Nat)
    (ht : ∀ i : Fin ps.length,NormalizedIntermediate.Bounded S d (Ring.mul ps[i.val] (delta i.val)))
    (n : Nat) : NormalizedIntermediate.Bounded S d (value ps delta n) := by
  apply NormalizedIntermediate.sum_prefix
  intro P hp
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hp
  exact ht i

end PCJ9eff70d512234a4c_Fixed.Materializer.VectorParentPrefix
