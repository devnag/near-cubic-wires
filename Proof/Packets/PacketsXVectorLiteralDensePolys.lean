import Proof.Packets.PacketsXDenseAtomsNat
import Proof.Packets.PacketsXVectorLiteralCompleteLoop

/-! Natural-polynomial model of the actual cumulative atom bank. The model
is related by exact ordered mask serialization, and every stored atom has
original-variable support and degree at most one. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open CloseoutRowsModeCache NormalizedFiniteTransport NormalizedIntermediate
noncomputable section

def densePolys (M depth : Nat) (p : Parameters) (initial : List (Ring.Poly Nat)) : Nat → List (Ring.Poly Nat)
  | 0=>initial
  | done+1=>let q:={p with level:=depth-(done+1)}
      DenseAtomsNat.table (q.level+1) (WindowProvider.modePairs q M) (densePolys M depth p initial done)
        (WindowProvider.modePairs q M).length

theorem dense_polys_length (M depth : Nat) (p : Parameters) (initial : List (Ring.Poly Nat)) (done : Nat) :
    (densePolys M depth p initial done).length=initial.length := by
  induction done with
  | zero=>rfl
  | succ done ih=>exact (DenseAtomsNat.table_length _ _ _ _).trans ih

theorem mode_pairs_bounded (M : Nat) (p : Parameters) :
    ∀pair∈WindowProvider.modePairs p M,Bounded (Finset.range M) 1 (DenseAtomsNat.answer pair) := by
  intro pair hp
  rcases List.mem_append.mp hp with hp|hp
  all_goals
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hp
    exact DenseAtomsNat.literal_answer_bounded (Finset.range M) i
      (Finset.mem_range.mpr (List.mem_range.mp hi)) _ _

theorem dense_polys_bounded (M depth : Nat) (p : Parameters) (initial : List (Ring.Poly Nat))
    (hi : ∀P∈initial,Bounded (Finset.range M) 1 P) (done : Nat) :
    ∀P∈densePolys M depth p initial done,Bounded (Finset.range M) 1 P := by
  induction done with
  | zero=>exact hi
  | succ done ih=>exact DenseAtomsNat.table_bounded _ _ _ _ (mode_pairs_bounded M _) ih _ le_rfl

theorem dense_polys_masks (C M depth : Nat) (p : Parameters) (initial : List (Ring.Poly Nat))
    (hM : M≤C) (done : Nat) :
    denseLevels C M depth p (initial.map (List.map (maskNat C))) done=
      (densePolys M depth p initial done).map (List.map (maskNat C)) := by
  induction done with
  | zero=>rfl
  | succ done ih=>
    rw [denseLevels,densePolys,ih]
    apply DenseAtomsNat.table_masks C _ _ _ _ _ le_rfl
    intro pair hp
    have shape : Theorem25Completion.CycleDenseAtomCost.AtomShape C pair := by
      rcases List.mem_append.mp hp with hp|hp
      · exact ModeCacheBounded.pairs_shape C M 1 _ hM pair hp
      · exact ModeCacheBounded.pairs_shape C M 2 _ hM pair hp
    exact (Theorem25Completion.CycleDenseAtomCost.atom_facts C pair shape).2.1

theorem dense_polys_lookup (M depth : Nat) (p : Parameters) (initial : List (Ring.Poly Nat))
    (hcodes : ∀level,level<depth → ∀i,i<2*M → Nat.pair (level+1) i< initial.length)
    (done : Nat) (hdone : done≤depth) (level : Nat) (hlo : depth-done≤level) (hhi : level<depth)
    (i : Nat) (hi : i<2*M) :
    (densePolys M depth p initial done).getD (Nat.pair (level+1) i) []=
      DenseAtomsNat.answer ((WindowProvider.modePairs {p with level:=level} M).getD i ([],[])) := by
  induction done with
  | zero=>omega
  | succ done ih=>
    let q:={p with level:=depth-(done+1)}
    have length : (WindowProvider.modePairs q M).length=2*M := by simp [WindowProvider.modePairs,pairs,two_mul]
    have current : depth-(done+1)<depth := by omega
    by_cases he : level=depth-(done+1)
    · subst level
      exact DenseAtomsNat.table_lookup (q.level+1) (WindowProvider.modePairs q M)
        (densePolys M depth p initial done)
        (by intro j hj;rw [dense_polys_length];exact hcodes q.level current j (by omega))
        i (by omega)
    · rw [densePolys,DenseAtomsNat.table_lookup_other_tag (q.level+1) (level+1)
        (WindowProvider.modePairs q M) (densePolys M depth p initial done) (by dsimp [q];omega) i _ le_rfl]
      exact ih (by omega) (by omega)

theorem dense_polys_delta_meaning (C population active depth done : Nat)
    (mask : Finset (Fin population)) (seed : ToeplitzSeed (canonicalGradedRank population active))
    (initial : List (Ring.Poly Nat)) (hinit : initial.length=C)
    (hd : depth≤canonicalGradedRank population active) (hC : (depth+2*population+2)^2≤C)
    (hdone : done≤depth) (level : Fin depth) (hl : depth-done≤level.val)
    (i : Nat) (hi : i<2*population) :
    (densePolys population depth (parameters population active 0 (C+9) mask seed) initial done).getD
      (Nat.pair (level.val+1) i) []=
      Normalized.structuralListLiteralAtom (depth:=depth) mask (canonicalGradedLabel population active) seed
        (Nat.pair (level.val+1) i) := by
  rw [dense_polys_lookup population depth _ initial (by
    intro l hl j hj
    rw [hinit]
    exact (LiteralAlphabet.pair_lt_square (l+1) j).trans_le
      ((Nat.pow_le_pow_left (by omega : l+1+j+1≤depth+2*population+2) 2).trans hC))
    done hdone level.val hl level.isLt i hi]
  exact (congrArg Ring.norm (DenseLiteralAtomMeaning.delta_raw population active depth (C+9) mask seed hd level i hi)).trans
    (LiteralAtomNormalize.atom_eq mask (canonicalGradedLabel population active) seed _).symm

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
