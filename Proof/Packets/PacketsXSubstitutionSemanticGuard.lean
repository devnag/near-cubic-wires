import Proof.Packets.PacketsXSubstitutionCensus
import Proof.Packets.PacketsXSubstitutionOuterNat

/-! The actual substitution controller's workspace and fuel guards follow
from normality, support, degree and the chosen finite-alphabet census. No
individual execution guard or physical result is supplied as advice. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionCensus
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport Theorem25Completion.CycleBounds

 theorem encoded_count {C w d : Nat} {S : Finset Nat} {P : Ring.Poly Nat}
    (hP : Bounded S d P) (hfit : (S.card+1)^d≤2^w) :
    (P.map (maskNat C)).length≤2^w := by
  simpa only [List.length_map] using (NormalizedIntermediate.census hP).trans hfit

 theorem encoded_get (C : Nat) (atoms : List (Ring.Poly Nat)) (j : Nat) :
    (atoms.map (List.map (maskNat C))).getD j []=(atoms.getD j []).map (maskNat C) :=
  List.getD_map atoms [] (List.map (maskNat C))

 theorem bounded_good {C d : Nat} {S : Finset Nat} (hS : ∀ j∈S,j<C)
    {P : Ring.Poly Nat} (hP : Bounded S d P) : SubstitutionInvariant.Good C P :=
  ⟨fits_of_bounded C S hS hP,hP.1.1⟩

 theorem monomial_guard (C w d : Nat) (S : Finset Nat) (hS : ∀ j∈S,j<C)
    (hw : 1≤w) (hfit : (S.card+1)^d≤2^w) (hfitAtom : S.card+1≤2^w)
    (pre post : List Bool) (m : List Nat) (hm : m.length≤d)
    (atoms : List (Ring.Poly Nat)) (ha : ∀ P∈atoms,Bounded S 1 P)
    (left stored : Ring.Poly Nat) (hl : left.length≤2^w) (hs : Bounded S d stored) :
    SubstitutionOuter.Guard C (commonReserve C w) pre.length (pre++maskNat C m++post)
      (atoms.map (List.map (maskNat C))) (left.map (maskNat C)) (stored.map (maskNat C)) := by
  have hat (j : Nat) : Bounded S 1 (atoms.getD j []) := bounded_get S atoms ha j
  have hfitOne : (S.card+1)^1≤2^w := by simpa only [pow_one] using hfitAtom
  have hleft (k : Nat) :
      PacketVector.Fits (commonReserve C w)
        (SubstitutionScan.scan C pre.length (pre++maskNat C m++post)
          (atoms.map (List.map (maskNat C))) (left.map (maskNat C)) (SubstitutionOuter.one C) k).1 ∧
      VectorAccumulator.Fits (commonReserve C w)
        (SubstitutionScan.scan C pre.length (pre++maskNat C m++post)
          (atoms.map (List.map (maskNat C))) (left.map (maskNat C)) (SubstitutionOuter.one C) k).1 := by
    apply scan_left_property C pre.length (pre++maskNat C m++post)
      (atoms.map (List.map (maskNat C))) (left.map (maskNat C)) (SubstitutionOuter.one C)
      (fun P=>PacketVector.Fits (commonReserve C w) P ∧ VectorAccumulator.Fits (commonReserve C w) P)
      (packet_fits C w _ (mask_width C left) (by simpa only [List.length_map] using hl))
    intro j
    rw [encoded_get]
    exact bounded_packet C w 1 S (atoms.getD j []) (hat j) hfitOne
  obtain ⟨product,hproduct,hproductEq⟩:=prefix_bounded C d S hS pre post m hm atoms ha
    (left.map (maskNat C)) C (Nat.le_refl C)
  refine ⟨?_,(hleft C).2,?_,(bounded_packet C w d S stored hs hfit).2,?_,
    mask_width C stored,?_,?_⟩
  · intro k hk
    obtain ⟨right,hr,he⟩:=prefix_bounded C d S hS pre post m hm atoms ha
      (left.map (maskNat C)) k hk.le
    refine ⟨(hleft k).1,?_,?_,?_⟩
    · rw [he];exact mask_width C right
    · rw [he,encoded_get]
      exact arithmetic_input_reserve C w _ _ (mask_width C _) (mask_width C _)
        (encoded_count (hat _) hfitOne) (encoded_count hr hfit)
    · rw [he,encoded_get]
      exact normalized_multiply_reserve C w _ _ (mask_width C _) (mask_width C _)
        (encoded_count (hat _) hfitOne) (encoded_count hr hfit) hw
  · change VectorAccumulator.Fits _
      (SubstitutionScan.scan C pre.length (pre++maskNat C m++post) _ _ _ C).2
    rw [hproductEq]
    exact (bounded_packet C w d S product hproduct hfit).2
  · change ∀ bits∈(SubstitutionScan.scan C pre.length (pre++maskNat C m++post) _ _ _ C).2,bits.length=C
    rw [hproductEq]
    exact mask_width C product
  · change ∀ i,(ReusableArithmetic.data C
      (SubstitutionScan.scan C pre.length (pre++maskNat C m++post) _ _ _ C).2
      (stored.map (maskNat C)) i).length≤_
    rw [hproductEq]
    exact arithmetic_input_reserve C w _ _ (mask_width C _) (mask_width C _)
      (encoded_count hproduct hfit) (encoded_count hs hfit)
  · change NormalizedAddition.budget C
      (SubstitutionScan.scan C pre.length (pre++maskNat C m++post) _ _ _ C).2
      (stored.map (maskNat C))+3≤_
    rw [hproductEq]
    exact normalized_addition_reserve C w _ _ (mask_width C _) (mask_width C _)
      (encoded_count hproduct hfit) (encoded_count hs hfit) hw

 theorem fold_left_census (C w d : Nat) (S : Finset Nat) (hS : ∀ j∈S,j<C)
    (hfit : (S.card+1)^d≤2^w)
    (P : Ring.Poly Nat) (hP : SubstitutionInvariant.Good C P) (hdeg : Ring.Degree d P)
    (atoms : List (Ring.Poly Nat)) (ha : ∀ Q∈atoms,Bounded S 1 Q)
    (left : Ring.Poly Nat) (hl : left.length≤2^w) (k : Nat) (hk : k≤P.length) :
    ∃ L : Ring.Poly Nat,L.length≤2^w ∧
      (SubstitutionOuter.fold C P.length (SubstitutionOuter.nativeMasks C P)
        (SubstitutionOuter.atomMasks C atoms) (left.map (maskNat C)) [] k).1=L.map (maskNat C) := by
  cases k with
  | zero=>exact ⟨left,hl,rfl⟩
  | succ k=>
    have hlt : k<P.length := by omega
    have hj : P.length-(k+1)<P.length := by omega
    let m:=P.getD (P.length-(k+1)) []
    have hp : Bounded S d (NormalizedFolds.product (m.map (fun code=>atoms.getD code []))) := by
      apply NormalizedIntermediate.substituted_monomial _ (bounded_get S atoms ha)
      exact hdeg _ (by dsimp [m];rw [List.getD_eq_getElem _ _ hj];exact List.getElem_mem hj)
    exact ⟨_,(NormalizedIntermediate.census hp).trans hfit,
      SubstitutionOuter.product_at_k C P hP atoms
        (fun Q hQ=>bounded_good hS (ha Q hQ)) _ k hlt⟩

 theorem fold_guards (C w d : Nat) (S : Finset Nat) (hS : ∀ j∈S,j<C)
    (hw : 1≤w) (hfit : (S.card+1)^d≤2^w) (hfitAtom : S.card+1≤2^w)
    (P : Ring.Poly Nat) (hP : SubstitutionInvariant.Good C P) (hdeg : Ring.Degree d P)
    (atoms : List (Ring.Poly Nat)) (ha : ∀ Q∈atoms,Bounded S 1 Q)
    (left : Ring.Poly Nat) (hl : left.length≤2^w) (k : Nat) (hk : k<P.length) :
    let state:=SubstitutionOuter.fold C P.length (SubstitutionOuter.nativeMasks C P)
      (SubstitutionOuter.atomMasks C atoms) (left.map (maskNat C)) [] k
    SubstitutionOuter.Guard C (commonReserve C w) ((P.length-(k+1))*C)
      (SubstitutionOuter.nativeMasks C P) (SubstitutionOuter.atomMasks C atoms) state.1 state.2 := by
  dsimp only
  obtain ⟨L,hL,heL⟩:=fold_left_census C w d S hS hfit P hP hdeg atoms ha left hl k hk.le
  rw [heL,SubstitutionOuter.fold_partialSum C P hP atoms
    (fun Q hQ=>bounded_good hS (ha Q hQ)) _ k hk.le]
  have hj : P.length-(k+1)<P.length := by omega
  let j : Fin P.length:=⟨P.length-(k+1),hj⟩
  have hpre : (SubstitutionOuter.nativeMasks C (P.take j.val)).length=j.val*C := by
    rw [SubstitutionOuter.nativeMasks_length,List.length_take,Nat.min_eq_left j.isLt.le]
  have hstored : Bounded S d (SubstitutionInvariant.partialSum atoms P k) :=
    NormalizedIntermediate.substitution_sum_prefix _ (bounded_get S atoms ha) P hdeg k
  have h:=monomial_guard C w d S hS hw hfit hfitAtom
    (SubstitutionOuter.nativeMasks C (P.take j.val))
    (SubstitutionOuter.nativeMasks C (P.drop (j.val+1))) P[j.val]
    (hdeg _ (List.getElem_mem j.isLt)) atoms ha L (SubstitutionInvariant.partialSum atoms P k) hL hstored
  rw [hpre,←SubstitutionOuter.nativeMasks_split C P j] at h
  exact h

 theorem atoms_fit (C w : Nat) (S : Finset Nat) (hfit : S.card+1≤2^w)
    (atoms : List (Ring.Poly Nat)) (ha : ∀ Q∈atoms,Bounded S 1 Q) :
    ∀ P∈SubstitutionOuter.atomMasks C atoms,
      PacketVector.Fits (commonReserve C w) P ∧ ∀ bits∈P,bits.length=C := by
  intro P hp
  obtain ⟨Q,hQ,rfl⟩:=List.mem_map.mp hp
  exact ⟨(bounded_packet C w 1 S Q (ha Q hQ) (by simpa only [pow_one] using hfit)).1,mask_width C Q⟩

 theorem width_fits (C w : Nat) : C+2≤commonReserve C w := by
  have h:=arithmetic_input_reserve C w [] [] (by simp) (by simp) (by simp) (by simp) 24
  change (UnaryTemplate.tape C).length≤commonReserve C w at h
  simp only [UnaryTemplate.tape,List.length_cons,List.length_append,List.length_replicate] at h
  omega

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionCensus
