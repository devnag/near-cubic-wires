import Proof.Supplier.RowTupleSubsets
import Proof.Packets.SubsetOrderAlgebra

/-! Exact order bridge for the original positional tuple source. Every
source declaration is retained; the source module narrows only unused imports. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubsetOrder
open NearCubicWires.RepairOrdinary.RowTupleDigits
open NearCubicWires.RepairOrdinary.RowTupleSubsets

theorem rank_snoc (base a : Nat) (xs : List Nat) :
    rank base (xs++[a])=rank base xs*base+a := by
  induction xs with
  | nil => simp [rank]
  | cons x xs ih =>
    simp only [List.cons_append,rank,List.length_append,List.length_singleton,pow_succ,ih]
    ring

theorem rank_reverse (w : Nat) (xs : List Nat) : rank (2^w) xs.reverse=encode w xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [List.reverse_cons,rank_snoc,ih,encode];ring

theorem selected_sorted (w M k : Nat) :
    (selected w M k).Pairwise (fun xs ys=>encode w xs<encode w ys) := by
  apply List.Pairwise.filter
  unfold candidates
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp_of_mem _ List.pairwise_lt_range
  intro a b ha hb hab
  rw [encode_digits w k a (List.mem_range.mp ha),encode_digits w k b (List.mem_range.mp hb)]
  exact hab

theorem colex_mem (M k : Nat) (xs : List Nat) :
    xs∈colexLen (List.range M) k ↔ xs∈(List.range M).sublistsLen k := by
  simp only [colexLen,List.mem_filter,List.mem_sublists,List.mem_sublistsLen,beq_iff_eq]

theorem colex_sorted (w M k : Nat) (hM : M≤2^w) :
    (colexLen (List.range M) k).Pairwise (fun xs ys=>encode w xs<encode w ys) := by
  have hp := (List.pairwise_sublists (List.pairwise_lt_range (n:=M))).filter (fun xs=>xs.length==k)
  apply List.Pairwise.imp_of_mem _ hp
  intro xs ys hx hy hlex
  have hx' := List.mem_sublistsLen.mp ((colex_mem M k xs).mp hx)
  have hy' := List.mem_sublistsLen.mp ((colex_mem M k ys).mp hy)
  rw [←rank_reverse,←rank_reverse]
  apply rank_lex_lt _ _ _ (by positivity) _ _ _ hlex
  · intro x hx
    exact (List.mem_range.mp (hx'.1.subset (List.mem_reverse.mp hx))).trans_le hM
  · intro y hy
    exact (List.mem_range.mp (hy'.1.subset (List.mem_reverse.mp hy))).trans_le hM
  · simpa only [List.length_reverse] using hx'.2.trans hy'.2.symm

/-- The low-digit-first physical source is exactly the colex subset list. -/
theorem selected_eq_colex (w M k : Nat) (hM : M≤2^w) :
    selected w M k=colexLen (List.range M) k := by
  have hp : (selected w M k).Perm (colexLen (List.range M) k) := by
    apply (List.perm_ext_iff_of_nodup ((candidates_nodup w k).filter _)
      ((List.nodup_sublists.mpr List.nodup_range).filter _)).mpr
    intro xs
    change xs∈selected w M k ↔ xs∈colexLen (List.range M) k
    rw [selected_mem w M k hM,colex_mem]
  exact hp.eq_of_pairwise (fun _ _ _ _ hab hba=>False.elim (Nat.lt_asymm hab hba))
    (selected_sorted w M k) (colex_sorted w M k hM)

theorem colex_map {α β : Type} (f : α→β) (l : List α) (k : Nat) :
    colexLen (l.map f) k=(colexLen l k).map (List.map f) := by
  simp only [colexLen,List.sublists_map,List.filter_map,Function.comp_def,List.length_map]

def lookup (codes : List Nat) (i : Nat) := codes[i]?.getD 0

theorem lookup_range (codes : List Nat) :
    (List.range codes.length).map (lookup codes)=codes := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range,lookup,List.getElem?_eq_getElem hj,Option.getD_some]

/-- Read the resident positional source cache in reverse order. Individual
monomials then only need their irrelevant internal reversal removed. The
bank order is exactly the frozen `sublistsLen` order, including repetitions. -/
theorem selected_reflected (w k : Nat) (codes : List Nat) (hM : codes.length≤2^w) :
    (selected w codes.length k).map (fun xs=>(xs.map (lookup codes.reverse)).reverse)=
      codes.sublistsLen k := by
  have hm := colex_map (lookup codes.reverse) (List.range codes.reverse.length) k
  rw [lookup_range] at hm
  simp only [List.length_reverse] at hm
  rw [selected_eq_colex w codes.length k hM]
  have hh := congrArg (fun ps=>ps.map List.reverse) hm
  rw [List.map_map] at hh
  exact hh.symm.trans (reflected_colex codes k)

end PCJ9eff70d512234a4c_Fixed.Materializer.SubsetOrder
