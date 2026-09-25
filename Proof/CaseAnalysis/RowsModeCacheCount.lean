import Proof.CaseAnalysis.RowsModeCacheDelta
import Proof.CaseAnalysis.RowsModeCacheTerms

/-! The real unmasked counter equals the exact child cardinality used by
the original structural delta-factor offset. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
open SupplierWalkBridge SupplierToeplitzCore SupplierToeplitz SupplierListPolynomial
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem original_child_count (mode : Fin 3) (population activeBound level C : Nat)
    (mask : Finset (Fin population)) (seed : ToeplitzSeed (canonicalGradedRank population activeBound))
    (hl : level < canonicalGradedRank population activeBound) :
    (track mode (parameters population activeBound level C mask seed) (initialState []) population).children=
      (hashIndexCell (canonicalGradedLabel population activeBound) seed
        (zeroPrefixCell (canonicalGradedRank population activeBound) (level+1))).card:=by
  rw [child_count]
  have he:((List.range population).map (fun j=>
      (childBit (parameters population activeBound level C mask seed) j).toNat))=
      List.ofFn (fun j : Fin population=>(decide (toeplitzHash
        (canonicalGradedLabel population activeBound j) seed∈
          zeroPrefixCell (canonicalGradedRank population activeBound) (level+1))).toNat):=by
    apply List.ext_getElem
    · simp
    · intro j hj hk
      simp only [List.length_map,List.length_range] at hj
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,childBit]
      rw [child_original population activeBound level C mask seed (snapshot j) hj hl]
      rfl
  rw [he,List.sum_ofFn]
  simp_rw [ThresholdRows.bool_nat,decide_eq_true_eq]
  simp [hashIndexCell]

end NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
