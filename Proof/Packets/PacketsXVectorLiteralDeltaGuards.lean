import Proof.Packets.PacketsXVectorDeltaMeaning
import Proof.Packets.PacketsXVectorLiteralDeltaResident

/-! Every concrete delta alphabet and window fits the unchanged global
literal census. Positive depth supplies the required nonempty alphabet. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.SupplierListPolynomial NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore
open NearCubicWires.RepairSource.CloseoutRawRows

theorem literal_delta_guards {depth population : Nat} (C w d : Nat) (level : Fin depth)
    (wins : Fin depth → Nat) (hpop : 1≤population) (hC : (depth+2*population+2)^2≤C)
    (hdegree : 2*wins level≤d) (hfit : (population*(2*depth+1)+2)^d≤2^w) :
    (∀c∈deltaLiteralVariableCodes (population:=population) level,c<C) ∧
    (deltaLiteralVariableCodes (population:=population) level).length≤C ∧
    1≤(deltaLiteralVariableCodes (population:=population) level).length ∧
    ((deltaLiteralVariableCodes (population:=population) level).length+1)^(2*wins level)≤2^w ∧
    population+2≤C := by
  have hd : 1≤depth := by have h:=level.isLt;omega
  have linear : depth+2*population+2≤C :=
    (Nat.le_self_pow (by decide : 2≠0) (depth+2*population+2)).trans hC
  have length : (deltaLiteralVariableCodes (population:=population) level).length=2*population := by
    simp only [deltaLiteralVariableCodes,List.length_ofFn]
  refine ⟨?_,by omega,by omega,?_,by omega⟩
  · intro c hc
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hc
    change Nat.pair (level.val+1) i.val<C
    exact (LiteralAlphabet.pair_lt_square (level.val+1) i.val).trans_le
      ((Nat.pow_le_pow_left (by have hi:=i.isLt;have hl:=level.isLt;omega) 2).trans hC)
  · rw [length]
    have base : 2*population+1≤population*(2*depth+1)+2 := by nlinarith only [hd,Nat.mul_le_mul_left population hd]
    exact ((Nat.pow_le_pow_left base (2*wins level)).trans
      (Nat.pow_le_pow_right (by omega) hdegree)).trans hfit

end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
