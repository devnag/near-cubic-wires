import Proof.Packets.PacketsCombineCap

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsCombine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.ExtDecompositionBatch
open Completion Theorem25Completion.CycleCommonReserve
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction
open Theorem25Completion.CycleBounds
noncomputable section

theorem reserveGen_eq (B w : ℕ) :
    Theorem25Completion.CycleCommonReserve.budget B w =
      6 * ((B + 1) ^ 4 * 2 ^ (8 * w + 16)) + (128 * w + 328) * 2 ^ (8 * w + 16) +
        10 * (B + 1) ^ 4 + 10 * (B + 1) ^ 3 + 10 * (B + 1) ^ 2 + 10 * (B + 1) + 4 * B + 308 * w + 920 := by
  simp only [Theorem25Completion.CycleCommonReserve.budget, budget8, budget7, budget6, budget5, budget4,
    budget3, budget2, budget1, cost1, cost2, cost3, cost4, cost5, cost6, cost7, cost8, UnaryAffine.budget,
    DimensionPower.cost, WilliamsUnaryProduct.budget, CloseoutCapacity.Power.budget,
    MatrixScorePower.budget, MatrixUnaryTemplate.budget, exponent,
    pow_zero, Nat.mul_one, ← Theorem25Completion.CycleCommonReserve.value_eq]
  ring

theorem reserveGen_le (B w : ℕ) :
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
      rw [reserveGen_eq]
      dsimp only [Y] at hlower ⊢
      nlinarith only [hlower]
    _ ≤ 1734 * X ^ 5 * Y := Nat.mul_le_mul_right _ hsmall
    _ ≤ 2048 * X ^ 5 * Y := by gcongr; norm_num
    _ = _ := by dsimp only [X, Y]; rw [pow_add]; norm_num; ring

/-- `KitBoot.cost` below one power of a dominating `Y`. -/
theorem kitBoot_le (C w Y : ℕ) (hC : C ≤ Y) (hw : 2 ^ w ≤ Y) (hR : commonReserve C w ≤ Y) :
    KitBoot.cost C w ≤ 2 ^ 34 * (Y + 1) ^ 26 := by
  have hwl : w < 2 ^ w := @Nat.lt_two_pow_self w
  have hZ : 1 ≤ Y + 1 := by omega
  have hgen := reserveGen_le C w
  have hsum : C + w + 2 ≤ 2 * (Y + 1) := by omega
  have h5 : (C + w + 2) ^ 5 ≤ 32 * (Y + 1) ^ 5 := by
    calc (C + w + 2) ^ 5 ≤ (2 * (Y + 1)) ^ 5 := Nat.pow_le_pow_left hsum 5
      _ = 32 * (Y + 1) ^ 5 := by ring
  have h8 : 2 ^ (8 * w) ≤ (Y + 1) ^ 8 := by
    rw [Nat.mul_comm, Nat.pow_mul]
    exact Nat.pow_le_pow_left (by omega) 8
  have hkb : Theorem25Completion.CycleCommonReserve.budget C w ≤ 2 ^ 32 * (Y + 1) ^ 26 := by
    have h13 : (Y + 1) ^ 5 * (Y + 1) ^ 8 ≤ (Y + 1) ^ 26 := by
      rw [← Nat.pow_add]; exact Nat.pow_le_pow_right hZ (by norm_num)
    calc _ ≤ 134217728 * (C + w + 2) ^ 5 * 2 ^ (8 * w) := hgen
      _ ≤ 134217728 * (32 * (Y + 1) ^ 5) * (Y + 1) ^ 8 := by gcongr
      _ = 2 ^ 32 * ((Y + 1) ^ 5 * (Y + 1) ^ 8) := by ring
      _ ≤ 2 ^ 32 * (Y + 1) ^ 26 := Nat.mul_le_mul_left _ h13
  have hlin : Y + 1 ≤ (Y + 1) ^ 26 := Nat.le_self_pow (by norm_num) _
  have hres := KitBoot.reserve_eq C w
  unfold KitBoot.cost
  have hR' : Theorem25Completion.CycleCommonReserve.reserve C w ≤ Y := by rw [hres]; exact hR
  generalize (Y + 1) ^ 26 = Z at hkb hlin ⊢
  generalize Theorem25Completion.CycleCommonReserve.budget C w = G at hkb ⊢
  omega

/-- A cube bound for the per-block/per-code fuels. -/
theorem cube_ge (Y : ℕ) : (Y + 1) ^ 2 ≤ (Y + 1) ^ 3 ∧ Y + 1 ≤ (Y + 1) ^ 3 ∧ Y * (Y + 1) ^ 2 ≤ (Y + 1) ^ 3 := by
  refine ⟨Nat.pow_le_pow_right (by omega) (by norm_num), Nat.le_self_pow (by norm_num) _, ?_⟩
  calc Y * (Y + 1) ^ 2 ≤ (Y + 1) * (Y + 1) ^ 2 := Nat.mul_le_mul_right _ (by omega)
    _ = (Y + 1) ^ 3 := by ring

theorem symBody_le (C w m Y : ℕ) (hR : commonReserve C w ≤ Y) (hm : m ≤ Y) :
    symBodyBudget C w m ≤ 256 * (Y + 1) ^ 3 := by
  obtain ⟨h2, h1, h3⟩ := cube_ge Y
  have hq : (commonReserve C w + 1) ^ 2 ≤ (Y + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hmq : m * (128 * (commonReserve C w + 1) ^ 2 + 3) ≤ 131 * (Y + 1) ^ 3 := by
    calc m * (128 * (commonReserve C w + 1) ^ 2 + 3) ≤ Y * (128 * (Y + 1) ^ 2 + 3 * (Y + 1) ^ 2) := by
          apply Nat.mul_le_mul hm; nlinarith
      _ = 131 * (Y * (Y + 1) ^ 2) := by ring
      _ ≤ 131 * (Y + 1) ^ 3 := Nat.mul_le_mul_left _ h3
  unfold symBodyBudget TranscriptColumnLookupFold.budget TranscriptColumnLookupBody.budget
    ReusableArithmetic.boundedBudget
  omega

theorem symEngine_le (C w n m Y : ℕ) (hR : commonReserve C w ≤ Y) (hm : m ≤ Y) (hn : n ≤ 4) :
    symEngineCost C w n m ≤ 2048 * (Y + 1) ^ 3 := by
  have hb := symBody_le C w m Y hR hm
  obtain ⟨_, h1, _⟩ := cube_ge Y
  have hnb : n * (symBodyBudget C w m + 3) ≤ 4 * (256 * (Y + 1) ^ 3 + 3) := Nat.mul_le_mul hn (by omega)
  unfold symEngineCost
  omega

theorem symLocal_le (mcost C w n m Y : ℕ) (hmc : mcost ≤ Y) (hC : C ≤ Y) (hw : 2 ^ w ≤ Y)
    (hR : commonReserve C w ≤ Y) (hm : m ≤ Y) (hn : n ≤ 4) :
    symLocalCost mcost C w n m ≤ 2 ^ 36 * (Y + 1) ^ 26 := by
  have hk := kitBoot_le C w Y hC hw hR
  have he := symEngine_le C w n m Y hR hm hn
  have h3 : (Y + 1) ^ 3 ≤ (Y + 1) ^ 26 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hlin : Y + 1 ≤ (Y + 1) ^ 26 := Nat.le_self_pow (by norm_num) _
  unfold symLocalCost PacketBank.storeBudget
  generalize (Y + 1) ^ 26 = Z at hk h3 hlin ⊢
  generalize (Y + 1) ^ 3 = T at he h3 ⊢
  omega

theorem thrBody_le (C w K Y : ℕ) (hR : commonReserve C w ≤ Y) (hK : K ≤ Y) :
    thrBodyBudget C w K ≤ 1024 * (Y + 1) ^ 3 := by
  obtain ⟨h2, h1, h3⟩ := cube_ge Y
  have hq : (commonReserve C w + 1) ^ 2 ≤ (Y + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hkq : K * (160 * (commonReserve C w + 1) ^ 2 + 3) ≤ 163 * (Y + 1) ^ 3 := by
    calc K * (160 * (commonReserve C w + 1) ^ 2 + 3) ≤ Y * (160 * (Y + 1) ^ 2 + 3 * (Y + 1) ^ 2) := by
          apply Nat.mul_le_mul hK; nlinarith
      _ = 163 * (Y * (Y + 1) ^ 2) := by ring
      _ ≤ 163 * (Y + 1) ^ 3 := Nat.mul_le_mul_left _ h3
  unfold thrBodyBudget fmulBudget ReusableArithmetic.boundedBudget
  omega

theorem thrLocal_le (mcost C w K N Y : ℕ) (hmc : mcost ≤ Y) (hC : C ≤ Y) (hw : 2 ^ w ≤ Y)
    (hR : commonReserve C w ≤ Y) (hK : K ≤ Y) (hN : N ≤ Y) :
    thrLocalCost mcost C w K N ≤ 2 ^ 36 * (Y + 1) ^ 26 := by
  have hk := kitBoot_le C w Y hC hw hR
  have hb := thrBody_le C w K Y hR hK
  obtain ⟨_, h1, h3⟩ := cube_ge Y
  have h4 : (Y + 1) ^ 4 ≤ (Y + 1) ^ 26 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hnb : N * (thrBodyBudget C w K + 3) ≤ 1027 * (Y + 1) ^ 4 := by
    calc N * (thrBodyBudget C w K + 3) ≤ Y * (1024 * (Y + 1) ^ 3 + 3 * (Y + 1) ^ 3) :=
          Nat.mul_le_mul hN (by omega)
      _ = 1027 * (Y * (Y + 1) ^ 3) := by ring
      _ ≤ 1027 * ((Y + 1) * (Y + 1) ^ 3) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
      _ = 1027 * (Y + 1) ^ 4 := by ring
  have hlin : Y + 1 ≤ (Y + 1) ^ 26 := Nat.le_self_pow (by norm_num) _
  unfold thrLocalCost PacketBank.storeBudget
  generalize (Y + 1) ^ 26 = Z at hk h4 hlin ⊢
  generalize (Y + 1) ^ 4 = F at hnb h4 ⊢
  omega

theorem polyLe (Y c d s : ℕ) (hs : 1 ≤ s) (hY : Y ≤ c * s ^ d) :
    2 ^ 36 * (Y + 1) ^ 26 ≤ 2 ^ 36 * (c + 1) ^ 26 * s ^ (26 * d) := by
  have hpos : 1 ≤ s ^ d := Nat.one_le_pow _ _ hs
  have h1 : Y + 1 ≤ (c + 1) * s ^ d := by nlinarith only [hY, hpos]
  calc 2 ^ 36 * (Y + 1) ^ 26 ≤ 2 ^ 36 * ((c + 1) * s ^ d) ^ 26 := by gcongr
    _ = 2 ^ 36 * (c + 1) ^ 26 * s ^ (26 * d) := by rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm d 26]; ring

end
end NearCubicWires.PacketsCombine
