import Proof.Packets.PacketsXSubstitutionSemanticGuard
import Proof.Packets.SubstitutionReusable

/-! The reusable physical substitution call, including setup and cleanup,
with the exact frozen natural-code result and every resource guard discharged
from the actual source and intermediate finite-alphabet census. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionCall
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport SubstitutionCensus Theorem25Completion.CycleBounds
open SubstitutionOuter SubstitutionInvariant

def leftResult (atoms : List (Ring.Poly Nat)) (P : Ring.Poly Nat) (left : Ring.Poly Nat) : Ring.Poly Nat :=
  match P with
  | []=>left
  | m::_=>NormalizedFolds.product (m.map (fun code=>atoms.getD code []))

theorem fold_left_exact (C : Nat) (P : Ring.Poly Nat) (hP : Good C P)
    (atoms : List (Ring.Poly Nat)) (ha : ∀ Q∈atoms,Good C Q) (left : Ring.Poly Nat) :
    (SubstitutionOuter.fold C P.length (nativeMasks C P) (atomMasks C atoms)
      (left.map (maskNat C)) [] P.length).1=(leftResult atoms P left).map (maskNat C) := by
  cases P with
  | nil=>rfl
  | cons m ms=>
    change (productState C (((m::ms).length-(ms.length+1))*C) (nativeMasks C (m::ms))
      (atomMasks C atoms)
      (SubstitutionOuter.fold C (m::ms).length (nativeMasks C (m::ms)) (atomMasks C atoms)
        (left.map (maskNat C)) [] ms.length).1).2=_
    simp only [List.length_cons,Nat.sub_self,Nat.zero_mul]
    have h:=product_at C (m::ms) hP atoms ha
      (SubstitutionOuter.fold C (m::ms).length (nativeMasks C (m::ms)) (atomMasks C atoms)
        (left.map (maskNat C)) [] ms.length).1 ⟨0,by simp⟩
    simpa only [Nat.zero_mul,List.getElem_cons_zero,leftResult,List.length_cons] using h

theorem result_bounded (d : Nat) (S : Finset Nat)
    (atoms : List (Ring.Poly Nat)) (ha : ∀ Q∈atoms,Bounded S 1 Q)
    (P : Ring.Poly Nat) (hP : Ring.Degree d P) :
    Bounded S d (Normalized.structuralGF2Substitute (fun code=>atoms.getD code []) P) := by
  have h:=NormalizedIntermediate.substitution_sum_prefix _ (bounded_get S atoms ha) P hP P.length
  change Bounded S d (partialSum atoms P P.length) at h
  rw [partialSum_complete] at h
  exact h

theorem leftResult_count (w d : Nat) (S : Finset Nat) (hfit : (S.card+1)^d≤2^w)
    (atoms : List (Ring.Poly Nat)) (ha : ∀ Q∈atoms,Bounded S 1 Q)
    (P : Ring.Poly Nat) (hP : Ring.Degree d P) (left : Ring.Poly Nat) (hl : left.length≤2^w) :
    (leftResult atoms P left).length≤2^w := by
  cases P with
  | nil=>exact hl
  | cons m ms=>
    exact (NormalizedIntermediate.census (NormalizedIntermediate.substituted_monomial _
      (bounded_get S atoms ha) m (hP m (by simp)))).trans hfit

theorem nat_run (C w d : Nat) (S : Finset Nat) (hS : ∀ j∈S,j<C)
    (hw : 1≤w) (hfit : (S.card+1)^d≤2^w) (hfitAtom : S.card+1≤2^w)
    (P : Ring.Poly Nat) (hP : Good C P) (hdeg : Ring.Degree d P) (hcount : P.length≤2^w)
    (atoms : List (Ring.Poly Nat)) (hlen : atoms.length=C) (ha : ∀ Q∈atoms,Bounded S 1 Q)
    (left : Ring.Poly Nat) (hl : left.length≤2^w) :
    Step execute (totalBudget C (commonReserve C w) P.length) heads
      (resident C (commonReserve C w) (left.map (maskNat C)) (P.map (maskNat C))
        (PacketVector.bank (commonReserve C w) (atomMasks C atoms)))
      heads (resident C (commonReserve C w) ((leftResult atoms P left).map (maskNat C))
        ((Normalized.structuralGF2Substitute (fun code=>atoms.getD code []) P).map (maskNat C))
        (PacketVector.bank (commonReserve C w) (atomMasks C atoms))) := by
  have hgood : ∀ Q∈atoms,Good C Q := fun Q hQ=>bounded_good hS (ha Q hQ)
  have hg : ∀ k,k<(P.map (maskNat C)).length→
      let state:=SubstitutionOuter.fold C (P.map (maskNat C)).length (P.map (maskNat C)).flatten
        (atomMasks C atoms) (left.map (maskNat C)) [] k
      Guard C (commonReserve C w) (((P.map (maskNat C)).length-(k+1))*C)
        (P.map (maskNat C)).flatten (atomMasks C atoms) state.1 state.2 := by
    simpa only [List.length_map,nativeMasks] using fold_guards C w d S hS hw hfit hfitAtom P hP hdeg atoms ha left hl
  have hout : VectorAccumulator.Fits (commonReserve C w)
      (SubstitutionOuter.fold C (P.map (maskNat C)).length (P.map (maskNat C)).flatten
        (atomMasks C atoms) (left.map (maskNat C)) [] (P.map (maskNat C)).length).2 := by
    simp only [List.length_map]
    have he:=fold_exact C P hP atoms hgood (left.map (maskNat C))
    simp only [nativeMasks] at he
    rw [he]
    exact (bounded_packet C w d S _ (result_bounded d S atoms ha P hdeg) hfit).2
  have result:=execute_run C (commonReserve C w) (atomMasks C atoms) (left.map (maskNat C))
    (P.map (maskNat C)) (by simpa only [atomMasks,List.length_map] using hlen)
    (width_fits C w) (packet_fits C w _ (mask_width C P) (by simpa only [List.length_map] using hcount)).2
    (atoms_fit C w S hfitAtom atoms ha) hg hout
  have heRight:=fold_exact C P hP atoms hgood (left.map (maskNat C))
  have heLeft:=fold_left_exact C P hP atoms hgood left
  simp only [nativeMasks] at heRight heLeft
  simpa only [List.length_map,heRight,heLeft] using result

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionCall
