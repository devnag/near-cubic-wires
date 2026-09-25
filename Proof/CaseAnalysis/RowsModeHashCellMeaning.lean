import Proof.CaseAnalysis.RowsModeHashCell

/-! The three actual prefix flags are the original zero-prefix, sibling
and child cells of the same Toeplitz seed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeHashCellMeaning
open LocalBitMultitape SupplierToeplitzCore SupplierToeplitz CloseoutRowsModeHashMeaning CloseoutRowsModeHashCell
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem bit_zero (z : ZMod 2) : (!decide (z=1))=true ↔ z=0:=by
  have h:=field_bit z
  cases hb:decide (z=1)
  · rw [hb] at h
    change (0 : ZMod 2)=z at h
    exact ⟨fun _=>h.symm,fun _=>rfl⟩
  · rw [hb] at h
    change (1 : ZMod 2)=z at h
    simp only [Bool.not_true,Bool.false_eq_true,false_iff]
    intro hz
    exact one_ne_zero (h.trans hz)

theorem zero_meaning {rank : Nat} (v : SupplierToeplitzCore.BitVec rank) (level : Nat) (hl : level≤rank) :
    zeroFlag ((bits v).take level)=decide (v∈zeroPrefixCell rank level):=by
  apply Bool.eq_iff_iff.mpr
  rw [zeroFlag,List.all_eq_true,List.forall_mem_iff_getElem]
  simp only [bits,List.length_take,List.length_ofFn,min_eq_left hl,List.getElem_take,List.getElem_ofFn,
    bit_zero,decide_eq_true_eq,mem_zeroPrefixCell]
  constructor
  · intro h i hi
    exact h i.val hi
  · intro h i hi
    exact h ⟨i,by omega⟩ hi

theorem read_meaning {rank : Nat} (v : SupplierToeplitzCore.BitVec rank) (level : Nat) (hl : level<rank) :
    readTapeBit (bits v) level=decide (v ⟨level,hl⟩=1):=by simp [readTapeBit,List.getD,bits,hl]

theorem child_meaning {rank : Nat} (v : SupplierToeplitzCore.BitVec rank) (level : Nat) (hl : level<rank) :
    (zeroFlag ((bits v).take level)&&!readTapeBit (bits v) level)=decide (v∈zeroPrefixCell rank (level+1)):=by
  rw [zero_meaning v level hl.le,read_meaning v level hl]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,decide_eq_true_eq,bit_zero,mem_zeroPrefixCell]
  constructor
  · rintro ⟨h,hbit⟩ i hi
    by_cases he:i.val=level
    · have eq:i=⟨level,hl⟩:=Fin.ext he
      simpa only [eq] using hbit
    · exact h i (by omega)
  · intro h
    exact ⟨fun i hi=>h i (by omega),h ⟨level,hl⟩ (by simp)⟩

theorem sibling_meaning {rank : Nat} (v : SupplierToeplitzCore.BitVec rank) (level : Nat) (hl : level<rank) :
    (zeroFlag ((bits v).take level)&&readTapeBit (bits v) level)=decide (v∈siblingPrefixCell rank level):=by
  have hz:=zero_meaning v level hl.le
  have hc:=child_meaning v level hl
  have hs : decide (v∈siblingPrefixCell rank level)=
      (decide (v∈zeroPrefixCell rank level)&&!decide (v∈zeroPrefixCell rank (level+1))):=by
    by_cases hp:v∈zeroPrefixCell rank level <;> by_cases hq:v∈zeroPrefixCell rank (level+1) <;>
      simp only [siblingPrefixCell,Finset.mem_sdiff,hp,hq,not_true_eq_false,not_false_eq_true,
        and_self,and_false,and_true,decide_true,decide_false,Bool.not_false,Bool.not_true,
        Bool.true_and,Bool.false_and]
  rw [hs,←hz,←hc]
  cases zeroFlag ((bits v).take level) <;> cases readTapeBit (bits v) level <;> rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsModeHashCellMeaning
