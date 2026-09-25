import Proof.CaseAnalysis.RowsModeHashBit

/-! The physical diagonal scan computes the literal Toeplitz hash of the
original three seed components, including its translation bit. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeHashMeaning
open LocalBitMultitape SupplierToeplitzCore CloseoutRowsModeHashBit
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def field (b : Bool) : ZMod 2:=if b then 1 else 0
def bits {n : Nat} (v : Fin n→ZMod 2):=List.ofFn (fun i=>decide (v i=1))

theorem field_bit (z : ZMod 2) : field (decide (z=1))=z:=by fin_cases z <;> decide

theorem field_injective : Function.Injective field:=by intro a b h;cases a <;> cases b <;> simp_all [field]

theorem field_xor (a b : Bool) : field (xor a b)=field a+field b:=by cases a <;> cases b <;> decide

theorem field_and (a b : Bool) : field (a&&b)=field a*field b:=by cases a <;> cases b <;> decide

theorem read_bits {n : Nat} (v : Fin n→ZMod 2) (i : Nat) (hi : i<n) :
    field (readTapeBit (bits v) i)=v ⟨i,hi⟩:=by
  simp [readTapeBit,List.getD,bits,hi,field_bit]

theorem field_fold (row : Nat) (label lower upper : List Bool) (cs : List Nat) (acc : Bool) :
    field (fold row label lower upper cs acc)=field acc+(cs.map (fun c=>field (term row c label lower upper))).sum:=by
  induction cs generalizing acc with
  | nil=>simp [fold]
  | cons c cs ih=>
    simp only [fold,List.foldl_cons] at ih ⊢
    rw [ih,field_xor,List.map_cons,List.sum_cons]
    ring

theorem term_meaning {rank : Nat} (label : SupplierToeplitzCore.BitVec rank) (seed : ToeplitzSeed rank) (row column : Fin rank) :
    field (term row.val column.val (bits label) (bits seed.1.1) (bits seed.1.2))=
      toeplitzEntry seed.1 row column*label column:=by
  unfold term
  rw [field_and,read_bits label column.val column.isLt]
  by_cases h:column.val≤row.val
  · rw [if_pos h,read_bits seed.1.1 (row.val-column.val) (by omega)]
    simp [toeplitzEntry,h,mul_comm]
  · rw [if_neg h,read_bits seed.1.2 (column.val-(row.val+1)) (by omega)]
    simp [toeplitzEntry,h,Nat.sub_sub,mul_comm]

theorem hash_meaning {rank : Nat} (label : SupplierToeplitzCore.BitVec rank) (seed : ToeplitzSeed rank) (row : Fin rank) :
    fold row.val (bits label) (bits seed.1.1) (bits seed.1.2) (List.range rank)
      (readTapeBit (bits seed.2) row.val)=decide (toeplitzHash label seed row=1):=by
  apply field_injective
  rw [field_bit,field_fold,read_bits seed.2 row.val row.isLt]
  have hs:((List.range rank).map (fun c=>field (term row.val c (bits label) (bits seed.1.1) (bits seed.1.2)))).sum=
      ∑ c : Fin rank,toeplitzEntry seed.1 row c*label c:=by
    rw [←List.sum_ofFn]
    congr 1
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.length_map,List.length_range] at hi
      simpa only [List.getElem_map,List.getElem_range,List.getElem_ofFn] using term_meaning label seed row ⟨i,hi⟩
  rw [hs]
  change _=toeplitzApply seed.1 label row+seed.2 row
  unfold toeplitzApply
  ring

end NearCubicWires.RepairOrdinary.CloseoutRowsModeHashMeaning
