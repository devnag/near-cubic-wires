import Proof.Packets.PacketsXLiteralPairUnary
import Proof.Packets.CycleCommonReserve

/-! Concrete cost of constructing a native paired literal from actual unary
metadata. The reserve bound pays both unary-to-binary conversions, actual pair
arithmetic, and every emitted unary code cell. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option warningAsError true
namespace Theorem25Completion.CycleLiteralPairCost
open NearCubicWires NearCubicWires.RepairOrdinary
open PCJ9eff70d512234a4c_Fixed.Materializer

abbrev commonReserve (C w : Nat) := CycleCommonReserve.reserve C w

theorem bits_length (n : Nat) : (CloseoutRowsCountBinary.bits n).length≤n+1 := by
  unfold CloseoutRowsCountBinary.bits
  split_ifs
  · simp
  · rw [SignedSortKey.binary_length]
    unfold natBitLength
    exact Nat.add_le_add_right (Nat.log_le_self 2 n) 1

theorem pair_width (C tag index : Nat) (ht : tag≤C) (hi : index≤C) :
    PCPPair.width (CloseoutRowsCountBinary.bits tag) (CloseoutRowsCountBinary.bits index)≤4*C+6 := by
  have h1:=bits_length tag
  have h2:=bits_length index
  unfold PCPPair.width
  omega

theorem pair_cold_bound (C tag index : Nat) (ht : tag≤C) (hi : index≤C) :
    PCPPairCold.budget (CloseoutRowsCountBinary.bits tag) (CloseoutRowsCountBinary.bits index)
      ≤9216*(C+1)^2 := by
  have h:=PCPPairCold.budget_quadratic (CloseoutRowsCountBinary.bits tag) (CloseoutRowsCountBinary.bits index)
  have hlen : (CloseoutRowsCountBinary.bits tag).length+
      (CloseoutRowsCountBinary.bits index).length+1≤3*(C+1) := by
    have h1:=bits_length tag
    have h2:=bits_length index
    omega
  have hs:=Nat.pow_le_pow_left hlen 2
  nlinarith

theorem budget_polynomial (R C tag index : Nat) (ht : tag≤C) (hi : index≤C)
    (hc : Nat.pair tag index≤C) :
    LiteralPairUnary.budget R tag index+1≤16384*(C+1)^2 := by
  have hp:=pair_cold_bound C tag index ht hi
  have hw:=pair_width C tag index ht hi
  have hs1:=Nat.pow_le_pow_left ht 2
  have hs2:=Nat.pow_le_pow_left hi 2
  have hrecord : Nat.pair tag index*(4*PCPPair.width
      (CloseoutRowsCountBinary.bits tag) (CloseoutRowsCountBinary.bits index)+7)
      ≤C*(16*C+31) := Nat.mul_le_mul hc (by omega)
  unfold LiteralPairUnary.budget LiteralPairUnary.budget5 LiteralPairUnary.budget4
    LiteralPairUnary.budget3 LiteralPairUnary.budget2 LiteralPairUnary.budget1
    LiteralPairUnary.cost1 LiteralPairUnary.cost2 LiteralPairUnary.cost3 LiteralPairUnary.cost4
    LiteralPairUnary.cost5 LiteralPairCold.budget LiteralPairRecord.budget
    CloseoutRowsModeIndexBlock.budget CloseoutRowsCountBinary.budget
  simp only [CloseoutRowsCountBinary.value_bits]
  nlinarith

theorem budget_reserve (R C w tag index : Nat) (ht : tag≤C) (hi : index≤C)
    (hc : Nat.pair tag index≤C) :
    LiteralPairUnary.budget R tag index+1≤commonReserve C w := by
  have hp:=budget_polynomial R C tag index ht hi hc
  have he : 1≤2^(8*w) := Nat.one_le_pow _ _ (by decide)
  have hpow : (C+1)^2≤(C+1)^4 := Nat.pow_le_pow_right (by omega) (by omega)
  unfold commonReserve CycleCommonReserve.reserve
  nlinarith [Nat.mul_le_mul_left (65536*(C+1)^4) he]

end Theorem25Completion.CycleLiteralPairCost
