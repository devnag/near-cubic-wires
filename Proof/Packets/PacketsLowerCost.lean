import Proof.Packets.PacketsLowerBudget

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.LowerCost
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.ExtDecompositionBatch
open Completion Theorem25Completion.CycleCommonReserve
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
noncomputable section

theorem reserve_generation_eq (B w : ℕ) :
    Theorem25Completion.CycleCommonReserve.budget B w =
      6 * ((B + 1) ^ 4 * 2 ^ (8 * w + 16)) + (128 * w + 328) * 2 ^ (8 * w + 16) +
        10 * (B + 1) ^ 4 + 10 * (B + 1) ^ 3 + 10 * (B + 1) ^ 2 + 10 * (B + 1) + 4 * B + 308 * w + 920 := by
  simp only [Theorem25Completion.CycleCommonReserve.budget, budget8, budget7, budget6, budget5, budget4,
    budget3, budget2, budget1, cost1, cost2, cost3, cost4, cost5, cost6, cost7, cost8, UnaryAffine.budget,
    DimensionPower.cost, WilliamsUnaryProduct.budget, CloseoutCapacity.Power.budget,
    MatrixScorePower.budget, MatrixUnaryTemplate.budget, exponent,
    pow_zero, Nat.mul_one, ← Theorem25Completion.CycleCommonReserve.value_eq]
  ring

theorem reserve_generation_le (B w : ℕ) :
    Theorem25Completion.CycleCommonReserve.budget B w ≤ 134217728 * (B + w + 2) ^ 5 * 2 ^ (8 * w) := by
  let X := B + w + 2
  let Y := 2 ^ (8 * w + 16)
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hBX : B + 1 ≤ X := by dsimp [X]; omega
  have hY : 1 ≤ Y := Nat.one_le_two_pow
  have hx4 : (B + 1) ^ 4 ≤ X ^ 5 :=
    (Nat.pow_le_pow_left hBX 4).trans (Nat.pow_le_pow_right hX (by decide))
  have hx3 : (B + 1) ^ 3 ≤ X ^ 5 :=
    (Nat.pow_le_pow_left hBX 3).trans (Nat.pow_le_pow_right hX (by decide))
  have hx2 : (B + 1) ^ 2 ≤ X ^ 5 :=
    (Nat.pow_le_pow_left hBX 2).trans (Nat.pow_le_pow_right hX (by decide))
  have hx1 : B + 1 ≤ X ^ 5 := hBX.trans (Nat.le_self_pow (by decide) _)
  have hw : w ≤ X ^ 5 := (by dsimp [X]; omega : w ≤ X).trans (Nat.le_self_pow (by decide) _)
  have hone : 1 ≤ X ^ 5 := Nat.one_le_pow _ _ hX
  have hsmall :
      6 * (B + 1) ^ 4 + (128 * w + 328) + 10 * (B + 1) ^ 4 + 10 * (B + 1) ^ 3 +
        10 * (B + 1) ^ 2 + 10 * (B + 1) + 4 * B + 308 * w + 920 ≤ 1734 * X ^ 5 := by omega
  have hlower :
      10 * (B + 1) ^ 4 + 10 * (B + 1) ^ 3 + 10 * (B + 1) ^ 2 + 10 * (B + 1) + 4 * B + 308 * w + 920 ≤
        (10 * (B + 1) ^ 4 + 10 * (B + 1) ^ 3 + 10 * (B + 1) ^ 2 + 10 * (B + 1) + 4 * B + 308 * w + 920) * Y :=
    Nat.le_mul_of_pos_right _ (by omega)
  calc
    _ ≤ (6 * (B + 1) ^ 4 + (128 * w + 328) + 10 * (B + 1) ^ 4 + 10 * (B + 1) ^ 3 +
        10 * (B + 1) ^ 2 + 10 * (B + 1) + 4 * B + 308 * w + 920) * Y := by
      rw [reserve_generation_eq]
      dsimp only [Y] at hlower ⊢
      nlinarith only [hlower]
    _ ≤ 1734 * X ^ 5 * Y := Nat.mul_le_mul_right _ hsmall
    _ ≤ 2048 * X ^ 5 * Y := by gcongr; norm_num
    _ = _ := by dsimp only [X, Y]; rw [pow_add]; norm_num; ring

/-- The request-level fuel of the F2 core: `LowerCore.cost` with the uniform join bound. -/
def total (mc C w cap poolLen : ℕ) : ℕ :=
  mc + 1 + (KitBoot.cost C w + 1 + ((2 * CloseoutRowsRawAtomProducer.budget cap poolLen + 2) + 1 +
    ((1 + 1 + (PacketBank.lookupBudget (PolyKit.reserve C w) 0 + 1 + 1)) + 1 +
      2 ^ 45 * (C + 1) ^ 9 * 2 ^ (17 * w))))

theorem core_cost_le (mc C w cap poolLen occLen : ℕ) (P Q : Ring.Poly ℕ) (hc : occLen ≤ C) (hw : 1 ≤ w)
    (hp : P.length ≤ 2 ^ w) (hq : Q.length ≤ 2 ^ w) (hn : (Ring.norm Q).length ≤ 2 ^ w) :
    LowerCore.cost mc C w cap poolLen occLen P Q ≤ total mc C w cap poolLen := by
  have h := LowerBudget.join_budget C w occLen P Q hc hw hp hq hn
  have hres : PolyKit.reserve C w = Theorem25Completion.CycleBounds.commonReserve C w := rfl
  unfold LowerCore.cost total
  rw [hres] at ⊢
  omega

theorem total_le (mc C w cap poolLen Y : ℕ) (hm : mc ≤ Y) (hC : C ≤ Y) (hw : 2 ^ w ≤ Y)
    (hraw : CloseoutRowsRawAtomProducer.budget cap poolLen ≤ Y) (hR : 2 * PolyKit.reserve C w ≤ Y) :
    total mc C w cap poolLen ≤ 2 ^ 46 * (Y + 1) ^ 26 := by
  have hwl : w < 2 ^ w := @Nat.lt_two_pow_self w
  have hZ : 1 ≤ Y + 1 := by omega
  have hgen := reserve_generation_le C w
  have hsum : C + w + 2 ≤ 2 * (Y + 1) := by omega
  have h5 : (C + w + 2) ^ 5 ≤ 32 * (Y + 1) ^ 5 := by
    calc (C + w + 2) ^ 5 ≤ (2 * (Y + 1)) ^ 5 := Nat.pow_le_pow_left hsum 5
      _ = 32 * (Y + 1) ^ 5 := by ring
  have h8 : 2 ^ (8 * w) ≤ (Y + 1) ^ 8 := by
    rw [Nat.mul_comm, Nat.pow_mul]
    exact Nat.pow_le_pow_left (by omega) 8
  have h17 : 2 ^ (17 * w) ≤ (Y + 1) ^ 17 := by
    rw [Nat.mul_comm, Nat.pow_mul]
    exact Nat.pow_le_pow_left (by omega) 17
  have h9 : (C + 1) ^ 9 ≤ (Y + 1) ^ 9 := Nat.pow_le_pow_left (by omega) 9
  have hkb : Theorem25Completion.CycleCommonReserve.budget C w ≤ 2 ^ 32 * (Y + 1) ^ 26 := by
    have h13 : (Y + 1) ^ 5 * (Y + 1) ^ 8 ≤ (Y + 1) ^ 26 := by
      rw [← Nat.pow_add]; exact Nat.pow_le_pow_right hZ (by norm_num)
    calc _ ≤ 134217728 * (C + w + 2) ^ 5 * 2 ^ (8 * w) := hgen
      _ ≤ 134217728 * (32 * (Y + 1) ^ 5) * (Y + 1) ^ 8 := by gcongr
      _ = 2 ^ 32 * ((Y + 1) ^ 5 * (Y + 1) ^ 8) := by ring
      _ ≤ 2 ^ 32 * (Y + 1) ^ 26 := Nat.mul_le_mul_left _ h13
  have hjoin : 2 ^ 45 * (C + 1) ^ 9 * 2 ^ (17 * w) ≤ 2 ^ 45 * (Y + 1) ^ 26 := by
    calc _ ≤ 2 ^ 45 * (Y + 1) ^ 9 * (Y + 1) ^ 17 := by gcongr
      _ = 2 ^ 45 * (Y + 1) ^ 26 := by ring
  have hlin : Y + 1 ≤ (Y + 1) ^ 26 := Nat.le_self_pow (by norm_num) _
  have hres := KitBoot.reserve_eq C w
  unfold total KitBoot.cost PacketBank.lookupBudget
  rw [hres]
  generalize (Y + 1) ^ 26 = Z at hkb hjoin hlin ⊢
  generalize Theorem25Completion.CycleCommonReserve.budget C w = G at hkb ⊢
  generalize 2 ^ 45 * (C + 1) ^ 9 * 2 ^ (17 * w) = J at hjoin ⊢
  omega

/-- The polynomial form: every input bounded by `c·s^d` gives a fixed power of `s`. -/
theorem poly_le (Y c d s : ℕ) (hs : 1 ≤ s) (hY : Y ≤ c * s ^ d) :
    2 ^ 46 * (Y + 1) ^ 26 ≤ 2 ^ 46 * (c + 1) ^ 26 * s ^ (26 * d) := by
  have hpos : 1 ≤ s ^ d := Nat.one_le_pow _ _ hs
  have h1 : Y + 1 ≤ (c + 1) * s ^ d := by nlinarith only [hY, hpos]
  calc 2 ^ 46 * (Y + 1) ^ 26 ≤ 2 ^ 46 * ((c + 1) * s ^ d) ^ 26 := by gcongr
    _ = 2 ^ 46 * (c + 1) ^ 26 * s ^ (26 * d) := by rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm d 26]; ring

/-- Collecting several `c_i·s^{d_i}` bounds under one. -/
theorem lift_le (x c d cS D s : ℕ) (hs : 1 ≤ s) (hc : c ≤ cS) (hd : d ≤ D) (hx : x ≤ c * s ^ d) :
    x ≤ cS * s ^ D :=
  hx.trans (Nat.mul_le_mul hc (Nat.pow_le_pow_right hs hd))

end
end NearCubicWires.PacketsConstruction.LowerCost
