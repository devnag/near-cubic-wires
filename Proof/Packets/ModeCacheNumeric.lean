import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! Numeric bounds for the actual mode-cache source. The hash workspace is
the already produced scalar C+9; no second reserve driver is needed. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ModeCacheNumeric

theorem hash_workspace (M rank C : Nat) (hr : rank≤9*M)
    (hC : (258*M+2)^2≤C) :
    rank+2≤C+9 ∧ (rank*(5*rank+22)+3)+2≤C+9 := by
  have hs : rank^2≤(9*M)^2 := Nat.pow_le_pow_left hr 2
  constructor <;>nlinarith only [hr,hs,hC,Nat.zero_le M]

theorem source_envelope (C M rank level : Nat)
    (hM : M≤C) (hr : rank≤C) (hl : level≤C) :
    4+(M*((2*((rank*(5*rank+22)+3)+2)+2)+2*level+4*M+2*rank+2*(C+9)+55+3)+3)
      ≤256*(C+1)^3 := by
  have hs : rank^2≤C^2 := Nat.pow_le_pow_left hr 2
  have hb : (2*((rank*(5*rank+22)+3)+2)+2)+2*level+4*M+2*rank+2*(C+9)+55+3
      ≤10*C^2+54*C+88 := by nlinarith only [hM,hr,hl,hs]
  have hp := Nat.mul_le_mul hM hb
  nlinarith only [hp,Nat.zero_le (C^3),Nat.zero_le (C^2),Nat.zero_le C]

theorem reserve_dominates (C w : Nat) :
    256*(C+1)^3≤65536*(C+1)^4*2^(8*w) ∧
    3*C+13≤65536*(C+1)^4*2^(8*w) := by
  have hp : (C+1)^3≤(C+1)^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have he : 1≤2^(8*w) := Nat.one_le_pow _ _ (by decide)
  have ht := Nat.mul_le_mul_left (65536*(C+1)^4) he
  constructor <;>nlinarith only [hp,ht,Nat.zero_le (C^2),Nat.zero_le (C^3),Nat.zero_le C]

end PCJ9eff70d512234a4c_Fixed.Materializer.ModeCacheNumeric
