import Proof.Packets.PacketsXMajorityCompleteEnumeration

/-! Exact constructor identity and prefix-safe census for the emitted
majority terms. The final parity uses the frozen right-fold ordering. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete
open NearCubicWires NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.SupplierEstimator
open NearCubicWires.P1Closure NormalizedFiniteTransport PairedPacketMeaning

def majority (ps : List Poly) :=
  Normalized.structuralGF2BitMajority (fun i : Fin ps.length=>ps[i.val])

theorem terms_length (ps : List Poly) : (terms ps).length=2^ps.length := by
  simp only [terms,assignments,LiveEnumeration.binary,List.length_map,List.length_ofFn]

theorem term_ofFn {n : Nat} (ps : Fin n→Poly) (b : BitInput n) :
    MajorityTermArena.term (List.ofFn ps) (List.ofFn b)=
      if compiledBitMajority b then Normalized.structuralGF2BooleanSelector ps b else [] := by
  unfold MajorityTermArena.term MajorityTermArena.accepted MajorityTermArena.product
  rw [List.length_ofFn,MajorityPredicateMeaning.predicate,MajorityPredicateMeaning.selector]

theorem terms_ofFn {n : Nat} (ps : Fin n→Poly) :
    terms (List.ofFn ps)=List.ofFn (fun code : Fin (2^n)=>
      if compiledBitMajority (structuralTruthAssignment n code) then
        Normalized.structuralGF2BooleanSelector ps (structuralTruthAssignment n code)
      else []) := by
  apply List.ext_getElem
  · simp only [terms_length,List.length_ofFn]
  · intro i hi hj
    simp only [terms,assignments,LiveEnumeration.binary,List.length_ofFn,List.getElem_map,List.getElem_ofFn]
    exact term_ofFn ps (structuralTruthAssignment n ⟨i,by simpa only [List.length_ofFn] using hj⟩)

theorem parity_exact (ps : List Poly) :
    (terms ps).foldr Ring.add []=majority ps := by
  let f : Fin ps.length→Poly := fun i=>ps[i.val]
  have hf : List.ofFn f=ps := List.ofFn_getElem
  have he : (terms (List.ofFn f)).foldr Ring.add []=
      Normalized.structuralGF2BitMajority f := by
    rw [terms_ofFn]
    exact (NormalizedFolds.finiteParity_foldr _).symm
  simpa only [hf,majority,f] using he

theorem term_bounded (S : Finset Nat) (d : Nat) (ps : List Poly) (bits : List Bool)
    (hps : ∀P∈ps,NormalizedIntermediate.Bounded S d P) :
    NormalizedIntermediate.Bounded S (d*ps.length) (MajorityTermArena.term ps bits) := by
  unfold MajorityTermArena.term
  split
  · have h:=NormalizedIntermediate.product (factors ps bits) (factors_bounded S d ps bits hps)
    simpa only [factors_length,MajorityTermArena.product] using h
  · exact NormalizedIntermediate.zero S _

theorem terms_bounded (S : Finset Nat) (d : Nat) (ps : List Poly)
    (hps : ∀P∈ps,NormalizedIntermediate.Bounded S d P) :
    ∀P∈terms ps,NormalizedIntermediate.Bounded S (d*ps.length) P := by
  intro P hp
  obtain ⟨b,_,rfl⟩:=List.mem_map.mp hp
  exact term_bounded S d ps (List.ofFn b) hps

theorem majority_bounded (S : Finset Nat) (d : Nat) (ps : List Poly)
    (hps : ∀P∈ps,NormalizedIntermediate.Bounded S d P) :
    NormalizedIntermediate.Bounded S (d*ps.length) (majority ps) := by
  rw [←parity_exact,←List.foldl_reverse]
  exact NormalizedIntermediate.fold_parity (terms ps).reverse
    (fun P hp=>terms_bounded S d ps hps P (List.mem_reverse.mp hp)) _
    (NormalizedIntermediate.zero S _)

end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete
