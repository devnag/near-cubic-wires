import Proof.Packets.SubsetSourceOrder
import Proof.Packets.PacketsXNormalizerOperations

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubsetOrder
open NearCubicWires.RepairOrdinary.RowTupleSubsets

variable {α : Type} [LinearOrder α]

theorem canon_reverse (m : List α) : Ring.canon m.reverse=Ring.canon m := by
  apply Ring.pairwise_toFinset_injective (Ring.canon_pairwise _) (Ring.canon_pairwise _)
  ext x
  simp only [List.mem_toFinset,Ring.canon_mem,List.mem_reverse]

theorem norm_reverse_rows (P : Ring.Poly α) : Ring.norm (P.map List.reverse)=Ring.norm P := by
  simp only [Ring.norm,List.foldl_map,canon_reverse]

def reflectedSource (w k : Nat) (codes : List Nat) : Ring.Poly Nat :=
  (selected w codes.length k).map (List.map (lookup codes.reverse))

theorem reflectedSource_reverse (w k : Nat) (codes : List Nat) (hM : codes.length≤2^w) :
    (reflectedSource w k codes).map List.reverse=codes.sublistsLen k := by
  simpa only [reflectedSource,List.map_map,Function.comp_def] using selected_reflected w k codes hM

/-- Literal equality, not parity equivalence or list permutation. This is the
source-order repair used before the complete physical normalizer. -/
theorem elementary_exact (w k : Nat) (codes : List Nat) (hM : codes.length≤2^w) :
    Ring.norm (reflectedSource w k codes)=Normalized.structuralGF2ElementarySymmetric codes k := by
  unfold Normalized.structuralGF2ElementarySymmetric
  rw [←reflectedSource_reverse w k codes hM,norm_reverse_rows]

end PCJ9eff70d512234a4c_Fixed.Materializer.SubsetOrder
