import Proof.Packets.PacketsXCycleDenseAtomCost

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true
namespace Theorem25Completion.CycleDenseAtomCost
open PCJ9eff70d512234a4c_Fixed.Materializer
open CycleBounds

theorem budget_envelope (C R count : Nat) (hc : count≤C) :
    DenseAtomMaterialize.budget C R count≤512*(C+1)^2*(R+1) := by
  have h:=Nat.mul_le_mul_right (128*(C+1)*(R+1)+3) hc
  unfold DenseAtomMaterialize.budget DenseAtomProgram.budget DenseAtomProgram.bodyBudget
  nlinarith only [h,hc,Nat.zero_le C,Nat.zero_le R,Nat.zero_le (C^2),Nat.zero_le (C^2*R),Nat.zero_le (C*R)]

theorem cold_budget_envelope (C R count : Nat) (hc : count≤C) :
    C*(12*R+24)+16+DenseAtomMaterialize.budget C R count≤1024*(C+1)^2*(R+1) := by
  have h:=budget_envelope C R count hc
  nlinarith only [h,Nat.zero_le C,Nat.zero_le R,Nat.zero_le (C^2),Nat.zero_le (C^2*R),Nat.zero_le (C*R)]

theorem cold_budget_polynomial (C w count : Nat) (hc : count≤C) :
    C*(12*commonReserve C w+24)+16+DenseAtomMaterialize.budget C (commonReserve C w) count
      ≤2^27*(C+1)^6*2^(8*w) := by
  have h:=cold_budget_envelope C (commonReserve C w) count hc
  have hp : 1≤commonReserve C w:=by have h:=(reserve_small C w).1;omega
  have hs : commonReserve C w+1≤2*commonReserve C w:=by omega
  have he:=Nat.mul_le_mul_left (1024*(C+1)^2) hs
  calc
    _≤1024*(C+1)^2*(commonReserve C w+1):=h
    _≤1024*(C+1)^2*(2*commonReserve C w):=he
    _=2^27*(C+1)^6*2^(8*w):=by unfold commonReserve;ring

end Theorem25Completion.CycleDenseAtomCost
