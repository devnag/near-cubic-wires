import Proof.Packets.PacketsXNormalizedWindow
import Mathlib.Data.List.Nodup

/-! Exact source order for literal windows. Distinct literal codes make the
inner elementary blocks disjoint by monomial length. The frozen inner sum
therefore needs the reflected native subset blocks in descending degree;
only the outer sum needs parity normalization. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowHomogeneousOrder
open NearCubicWires NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowBinomial
open NormalizerOrder

variable (codes : List Nat) (hc : codes.Pairwise (·<·))

def block (coefficient : Nat→Nat) (k : Nat) :=
  gf2ParityScale (coefficient k) (codes.sublistsLen k)

include hc in
theorem subsets_normal (k : Nat) : Ring.Normal (codes.sublistsLen k) := by
  refine ⟨List.nodup_sublistsLen k hc.nodup,?_⟩
  intro m hm
  exact hc.sublist (List.mem_sublistsLen.mp hm).1

include hc in
theorem block_normal (coefficient : Nat→Nat) (k : Nat) : Ring.Normal (block codes coefficient k) := by
  unfold block gf2ParityScale
  split
  · exact ⟨by simp,by simp⟩
  · exact subsets_normal codes hc k

theorem block_length (coefficient : Nat→Nat) (k : Nat) (m : List Nat)
    (hm : m∈block codes coefficient k) : m.length=k := by
  unfold block gf2ParityScale at hm
  split at hm
  · simp at hm
  · exact (List.mem_sublistsLen.mp hm).2

theorem scale_reverse (value : Nat) (P : Ring.Poly Nat) :
    gf2ParityScale value P.reverse=(gf2ParityScale value P).reverse := by
  unfold gf2ParityScale
  split <;> rfl

include hc in
theorem elementary_reverse (k : Nat) :
    Normalized.structuralGF2ElementarySymmetric codes k=(codes.sublistsLen k).reverse :=
  norm_normal _ (subsets_normal codes hc k)

include hc in
theorem flat_normal (coefficient : Nat→Nat) (ks : List Nat) (hk : ks.Nodup) :
    Ring.Normal (ks.flatMap (fun k=>(block codes coefficient k).reverse)) := by
  constructor
  · apply List.nodup_flatMap.mpr
    refine ⟨fun k _=>List.nodup_reverse.mpr (block_normal codes hc coefficient k).1,?_⟩
    apply hk.imp
    intro a b hab
    change List.Disjoint (block codes coefficient a).reverse (block codes coefficient b).reverse
    intro m hma hmb
    exact hab ((block_length codes coefficient a m (List.mem_reverse.mp hma)).symm.trans
      (block_length codes coefficient b m (List.mem_reverse.mp hmb)))
  · intro m hm
    obtain ⟨k,_,hm⟩:=List.mem_flatMap.mp hm
    exact (block_normal codes hc coefficient k).2 m (List.mem_reverse.mp hm)

theorem sum_eq_norm (ps : List (Ring.Poly Nat))
    (hp : ∀ P∈ps,∀m∈P,m.Pairwise (·<·)) :
    ps.foldl Ring.add []=Ring.norm ps.flatten := by
  unfold Ring.norm
  rw [fold_canon_eq]
  · rw [List.foldl_flatten]
    rfl
  · intro m hm
    obtain ⟨P,hP,hm⟩:=List.mem_flatten.mp hm
    exact hp P hP m hm

include hc in
theorem sum_elementary (coefficient : Nat→Nat) (ks : List Nat) (hk : ks.Nodup) :
    ks.foldl (fun acc k=>Ring.add acc
      (gf2ParityScale (coefficient k) (Normalized.structuralGF2ElementarySymmetric codes k))) []=
      ks.reverse.flatMap (block codes coefficient) := by
  simp only [elementary_reverse codes hc,scale_reverse]
  change ks.foldl (fun acc k=>Ring.add acc (block codes coefficient k).reverse) []=_
  rw [←List.foldl_map]
  rw [sum_eq_norm]
  · change Ring.norm (ks.flatMap (fun k=>(block codes coefficient k).reverse))=_
    rw [norm_normal _ (flat_normal codes hc coefficient ks hk),List.reverse_flatMap]
    simp only [Function.comp_def,List.reverse_reverse]
  · intro P hP m hm
    obtain ⟨k,_,rfl⟩:=List.mem_map.mp hP
    exact (block_normal codes hc coefficient k).2 m (List.mem_reverse.mp hm)

def rawShifted (offset degree : Nat) :=
  (List.range (degree+1)).reverse.flatMap (block codes (fun a=>(offset+(degree-a)-1).choose (degree-a)))

include hc in
theorem shifted_exact (w offset degree : Nat) (hM : codes.length≤2^w) :
    NormalizedWindow.shifted w codes offset degree=rawShifted codes offset degree := by
  unfold NormalizedWindow.shifted
  simp only [NormalizedWindow.elementary_exact w codes _ hM]
  exact sum_elementary codes hc _ _ List.nodup_range

def rawWindow (offset width target : Nat) :=
  (List.range (width+1)).flatMap (fun d=>gf2ParityScale (d.choose target) (rawShifted codes offset d))

include hc in
theorem rawShifted_sorted (offset degree : Nat) :
    ∀m∈rawShifted codes offset degree,m.Pairwise (·<·) := by
  intro m hm
  obtain ⟨k,_,hm⟩:=List.mem_flatMap.mp hm
  exact (block_normal codes hc _ k).2 m hm

include hc in
theorem window_exact (w offset width target : Nat) (hM : codes.length≤2^w) :
    NormalizedWindow.window w codes offset width target=Ring.norm (rawWindow codes offset width target) := by
  unfold NormalizedWindow.window
  simp only [shifted_exact codes hc w _ _ hM]
  rw [←List.foldl_map,sum_eq_norm]
  · rfl
  · intro P hP m hm
    obtain ⟨d,_,rfl⟩:=List.mem_map.mp hP
    unfold gf2ParityScale at hm
    split at hm
    · simp at hm
    · exact rawShifted_sorted codes hc offset d m hm

include hc in
theorem canon_reflected (w k : Nat) (hM : codes.length≤2^w) :
    (SubsetOrder.reflectedSource w k codes).map Ring.canon=codes.sublistsLen k := by
  calc
    _=((SubsetOrder.reflectedSource w k codes).map List.reverse).map Ring.canon := by
      simp only [List.map_map,Function.comp_def,SubsetOrder.canon_reverse]
    _=(codes.sublistsLen k).map Ring.canon := by rw [SubsetOrder.reflectedSource_reverse w k codes hM]
    _=codes.sublistsLen k := by
      conv_rhs=>rw [←List.map_id (codes.sublistsLen k)]
      apply List.map_congr_left
      intro m hm
      exact canon_eq_of_pairwise m ((subsets_normal codes hc k).2 m hm)

def nativeShifted (w offset degree : Nat) :=
  (List.range (degree+1)).reverse.flatMap (fun a=>
    gf2ParityScale ((offset+(degree-a)-1).choose (degree-a)) (SubsetOrder.reflectedSource w a codes))
def nativeWindow (w offset width target : Nat) :=
  (List.range (width+1)).flatMap (fun d=>gf2ParityScale (d.choose target) (nativeShifted codes w offset d))

theorem canon_scale (value : Nat) (P : Ring.Poly Nat) :
    (gf2ParityScale value P).map Ring.canon=gf2ParityScale value (P.map Ring.canon) := by
  unfold gf2ParityScale
  split <;> rfl

include hc in
theorem canon_nativeShifted (w offset degree : Nat) (hM : codes.length≤2^w) :
    (nativeShifted codes w offset degree).map Ring.canon=rawShifted codes offset degree := by
  unfold nativeShifted rawShifted
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro k _
  rw [canon_scale,canon_reflected codes hc w k hM]
  rfl

include hc in
theorem canon_nativeWindow (w offset width target : Nat) (hM : codes.length≤2^w) :
    (nativeWindow codes w offset width target).map Ring.canon=rawWindow codes offset width target := by
  unfold nativeWindow rawWindow
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro d _
  rw [canon_scale,canon_nativeShifted codes hc w offset d hM]

theorem norm_map_canon (P : Ring.Poly Nat) : Ring.norm (P.map Ring.canon)=Ring.norm P := by
  rw [norm_ordered,norm_ordered,List.map_map]
  apply congrArg NormalizerOrder.ordered
  apply List.map_congr_left
  intro m _
  exact canon_eq_of_pairwise _ (Ring.canon_pairwise m)

include hc in
theorem nativeWindow_exact (w offset width target : Nat) (hM : codes.length≤2^w) :
    Ring.norm (nativeWindow codes w offset width target)=
      Normalized.structuralGF2ConsecutiveWindowIndicator codes offset width target := by
  rw [←NormalizedWindow.window_exact w codes offset width target hM,
    window_exact codes hc w offset width target hM,←canon_nativeWindow codes hc w offset width target hM,
    norm_map_canon]

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowHomogeneousOrder
