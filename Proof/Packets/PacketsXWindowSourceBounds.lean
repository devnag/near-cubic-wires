import Proof.Packets.PacketsXWindowHomogeneousOrder
import Mathlib.Data.Nat.Choose.Bounds

/-! The descending native window is a bounded raw intermediate: at most a
quadratic number of elementary blocks, each bounded by the degree census.
This bound is independent of any truth assignment. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowHomogeneousOrder
open NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowBinomial

theorem length_flatMap_le {α β : Type} (xs : List α) (f : α→List β) (bound : Nat)
    (h : ∀x∈xs,(f x).length≤bound) : (xs.flatMap f).length≤xs.length*bound := by
  induction xs with
  | nil=>simp
  | cons x xs ih=>
    have hx := h x (by simp)
    have hs := ih (by intro y hy;exact h y (by simp [hy]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem scale_length (n : Nat) (P : Ring.Poly Nat) : (gf2ParityScale n P).length≤P.length := by
  unfold gf2ParityScale
  split <;> simp


theorem rawShifted_normal (codes : List Nat) (hc : codes.Pairwise (·<·)) (offset d : Nat) :
    Ring.Normal (rawShifted codes offset d) := by
  let coefficient := fun a=>(offset+(d-a)-1).choose (d-a)
  have hn := flat_normal codes hc coefficient (List.range (d+1)) List.nodup_range
  have hr : Ring.Normal (((List.range (d+1)).flatMap
      (fun a=>(block codes coefficient a).reverse)).reverse) := by
    exact ⟨List.nodup_reverse.mpr hn.1,fun m hm=>hn.2 m (List.mem_reverse.mp hm)⟩
  simpa only [List.reverse_flatMap,List.reverse_reverse,Function.comp_def,coefficient,rawShifted] using hr

theorem rawShifted_length_sharp (codes : List Nat) (hc : codes.Pairwise (·<·)) (offset d : Nat) :
    (rawShifted codes offset d).length≤(codes.length+1)^d := by
  apply (Ring.size_bound codes.toFinset d (rawShifted_normal codes hc offset d) ?_ ?_).trans
    (Nat.pow_le_pow_left (Nat.add_le_add_right (List.toFinset_card_le codes) 1) d)
  · intro m hm
    obtain ⟨k,hk,hm⟩ := List.mem_flatMap.mp hm
    have hlen := block_length codes _ k m hm
    have hkd := List.mem_range.mp (List.mem_reverse.mp hk)
    omega
  · intro m hm x hx
    obtain ⟨k,_,hm⟩ := List.mem_flatMap.mp hm
    unfold block gf2ParityScale at hm
    split at hm
    · simp at hm
    · exact List.mem_toFinset.mpr ((List.mem_sublistsLen.mp hm).1.subset hx)

theorem nativeWindow_length_sharp (codes : List Nat) (hc : codes.Pairwise (·<·))
    (w offset width target : Nat) (hM : codes.length≤2^w) :
    (nativeWindow codes w offset width target).length≤(width+1)*(codes.length+1)^width := by
  have he := congrArg List.length (canon_nativeWindow codes hc w offset width target hM)
  simp only [List.length_map] at he
  rw [he]
  have result := length_flatMap_le (List.range (width+1))
    (fun d=>gf2ParityScale (d.choose target) (rawShifted codes offset d))
    ((codes.length+1)^width) (by
      intro d hd
      have hdw : d≤width := by have := List.mem_range.mp hd;omega
      exact (scale_length _ _).trans ((rawShifted_length_sharp codes hc offset d).trans
        (Nat.pow_le_pow_right (by omega) hdw)))
  simpa only [rawWindow,List.length_range] using result


theorem rawShifted_support (codes : List Nat) (offset d : Nat) :
    ∀m∈rawShifted codes offset d,∀x∈m,x∈codes := by
  intro m hm x hx
  obtain ⟨k,_,hm⟩ := List.mem_flatMap.mp hm
  unfold block gf2ParityScale at hm
  split at hm
  · simp at hm
  · exact (List.mem_sublistsLen.mp hm).1.subset hx

theorem rawWindow_support (codes : List Nat) (offset width target : Nat) :
    ∀m∈rawWindow codes offset width target,∀x∈m,x∈codes := by
  intro m hm x hx
  obtain ⟨d,_,hm⟩ := List.mem_flatMap.mp hm
  unfold gf2ParityScale at hm
  split at hm
  · simp at hm
  · exact rawShifted_support codes offset d m hm x hx

theorem nativeWindow_support (codes : List Nat) (hc : codes.Pairwise (·<·))
    (w offset width target : Nat) (hM : codes.length≤2^w) :
    ∀m∈nativeWindow codes w offset width target,∀x∈m,x∈codes := by
  intro m hm x hx
  have hm' : Ring.canon m∈rawWindow codes offset width target := by
    rw [←canon_nativeWindow codes hc w offset width target hM]
    exact List.mem_map_of_mem hm
  exact rawWindow_support codes offset width target _ hm' x (Ring.canon_mem.mpr hx)


end PCJ9eff70d512234a4c_Fixed.Materializer.WindowHomogeneousOrder
