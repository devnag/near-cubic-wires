import Proof.Packets.PhysicalCoefficientAlgebra
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Induction

/-! Exact ordered parity normal form: retain the last occurrence of every
odd-multiplicity monomial, then reverse that list. This is the literal order
of the fixed compiler's erase-or-cons fold, not merely a permutation. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NormalizerOrder
open PhysicalCoefficientAlgebra
variable {α : Type} [DecidableEq α]

def ordered (P : List α) : List α :=
  P.dedup.reverse.filter (fun a => coefficient a P)

@[simp] theorem coefficient_append_singleton (a x : α) (P : List α) :
    coefficient a (P++[x]) = xor (coefficient a P) (decide (a=x)) := by
  simp [coefficient,List.foldl_append]

theorem coefficient_of_not_mem (a : α) (P : List α) (h : a ∉ P) :
    coefficient a P = false := by
  induction P with
  | nil => rfl
  | cons x P ih =>
    have hx : a ≠ x := fun e => h (by simp [e])
    have ht : a ∉ P := fun hm => h (by simp [hm])
    simpa [coefficient_cons,hx] using ih ht

theorem dedup_snoc (P : List α) (x : α) :
    (P++[x]).dedup = (P.dedup.filter (fun a => decide (a≠x)))++[x] := by
  induction P with
  | nil => simp
  | cons a P ih =>
    by_cases he : a=x
    · subst a
      by_cases hm : x ∈ P <;> simp [hm,ih]
    · by_cases hm : a ∈ P <;> simp [he,hm,ih]

@[simp] theorem ordered_nodup (P : List α) : (ordered P).Nodup :=
  (List.nodup_reverse.mpr (List.nodup_dedup P)).filter _

@[simp] theorem mem_ordered (a : α) (P : List α) :
    a ∈ ordered P ↔ coefficient a P = true := by
  simp only [ordered,List.mem_filter,List.mem_reverse,List.mem_dedup]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_,h⟩
    by_contra hn
    rw [coefficient_of_not_mem a P hn] at h
    contradiction

theorem filter_append_coefficient (P : List α) (x : α) :
    (P.dedup.reverse.filter (fun a => decide (a≠x))).filter
      (fun a => coefficient a (P++[x])) =
      (ordered P).filter (fun a => decide (a≠x)) := by
  simp only [ordered,List.filter_filter,coefficient_append_singleton]
  apply List.filter_congr
  intro a _
  by_cases he : a=x
  · simp [he]
  · simp [he,Bool.and_comm]

theorem ordered_snoc (P : List α) (x : α) :
    ordered (P++[x]) = toggle x (ordered P) := by
  have hf := filter_append_coefficient P x
  change ((P++[x]).dedup.reverse.filter (fun a => coefficient a (P++[x]))) = toggle x (ordered P)
  have horder : (P++[x]).dedup.reverse = x::(P.dedup.reverse.filter (fun a => decide (a≠x))) := by
    rw [dedup_snoc,List.reverse_append,List.reverse_singleton,List.singleton_append,←List.filter_reverse]
  rw [horder,List.filter_cons,hf,coefficient_append_singleton]
  simp only [decide_true,Bool.xor_true]
  change (if !(coefficient x P) then x::((ordered P).filter (fun a => decide (a≠x)))
    else (ordered P).filter (fun a => decide (a≠x))) = toggle x (ordered P)
  by_cases hm : x ∈ ordered P
  · have hc : coefficient x P=true := (mem_ordered x P).mp hm
    rw [hc]
    simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte,toggle,if_pos hm]
    simpa only [bne,decide_not,Bool.beq_eq_decide_eq] using ((ordered_nodup P).erase_eq_filter x).symm
  · have hc : coefficient x P=false := Bool.eq_false_iff.mpr (fun h => hm ((mem_ordered x P).mpr h))
    have he : (ordered P).filter (fun a => decide (a≠x))=ordered P := by
      apply List.filter_eq_self.mpr
      intro a ha
      apply decide_eq_true
      intro hax
      exact hm (hax ▸ ha)
    rw [hc,he]
    simp only [Bool.not_false,↓reduceIte,toggle,if_neg hm]

/-- Ordered byte materialization can use keep-last deduplication, reversal,
and parity filtering while matching the exact foldl output. -/
theorem ordered_eq_fold (P : List α) :
    ordered P = P.foldl (fun acc x => toggle x acc) [] := by
  induction P using List.reverseRecOn with
  | nil => rfl
  | append_singleton P x ih => rw [ordered_snoc,ih,List.foldl_append]; rfl

end PCJ9eff70d512234a4c_Fixed.Materializer.NormalizerOrder
