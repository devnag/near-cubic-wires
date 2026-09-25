import Proof.Rows.RowsFrameSymInst
import Proof.Rows.RowsLoopCostBound

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsInit.FrameSymCost
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open PCJd4d1d9d7d1fa4313_Production RowsConstruction RowsConstruction.BaseLayout
noncomputable section

/-! ## 1. Arithmetic -/

/-- The key-0 writer is linear in its width and reserve. -/
theorem k0_lin (w R : ℕ) : KeyZero.symK0Cost w R + 2 ≤ 128 * (w + R + 1) := by
  unfold KeyZero.symK0Cost KeyZero.zcost SymC5.recCost SymC5.tcost
  omega

/-- **The assembly of the SYM branch's cost** from the bounds of its pieces (as plain numbers). -/
theorem assemble (W SL C N K P Q T Rs cw kL cc kR : ℕ)
    (hW : W ≤ cw * P) (hSL : SL ≤ kL * P + kL * Q) (hC : C ≤ cc * P) (hN : N ≤ 8 * P)
    (hK : K ≤ 128 * (T + 3 + Rs + 1)) (hRs : Rs ≤ kR * P) (hT : T ≤ P) :
    (2 * W + 2) + 1 + ((SL + 1 + ((2 * C + 2) + 1 + (2 * (2 * natBitLength N + 1) + 4))) + 1 + K) + 2 ≤
      (2 * cw + kL + 2 * cc + 128 * kR + 1000) * (P + Q + 1) := by
  have hb := SymBounds.natBitLength_le N
  have e : (2 * cw + kL + 2 * cc + 128 * kR + 1000) * (P + Q + 1) =
      2 * (cw * P) + kL * P + 2 * (cc * P) + 128 * (kR * P) + 1000 * P +
        (2 * cw + kL + 2 * cc + 128 * kR + 1000) * Q + (2 * cw + kL + 2 * cc + 128 * kR + 1000) := by ring
  have hQ : kL * Q ≤ (2 * cw + kL + 2 * cc + 128 * kR + 1000) * Q := Nat.mul_le_mul_right Q (by omega)
  rw [e]
  omega

/-! ## 2. The SYM branch -/

section Sym
variable (a : DecompositionAlgorithm)

/-- The degree: the words' and C5's exponents, RS's loop exponent, `symRd`, PM's `163`. -/
def dS : ℕ := (RowsInit.FrameSymWords.symVec a).degree + (RowsInit.C5.c5Vec a).degree + RowsInit.LoopCost.symD a +
  symRd + 163 + 1

/-- The coefficient. -/
def cS : ℕ := 2 * (RowsInit.FrameSymWords.symVec a).coefficient + RowsInit.LoopCost.symK a +
  2 * (RowsInit.C5.c5Vec a).coefficient + 128 * (symRc + 1) + 1000

/-- **The SYM branch's cost** (`S.costNe` of `FrameSymInst.symSpec`) in `rowBudget`'s shape, one `c d` per `a`. -/
theorem sym_cost_le (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) :
    RowsInit.FrameSymWork.neCost a (RowsInit.FrameSymInst.symLoop a) (.sym r four L target) + 2 ≤
      cS a * ((Request.smallSize a (.sym r four L target)) ^ dS a +
        2 ^ (PCJ9eff70d512234a4c_Fixed.Packets.residual ((Request.sym r four L target).family a)) *
          ((Request.sym r four L target).q + ((Request.sym r four L target).input a).length + 1) ^ dS a + 1) := by
  have hS1 : 1 ≤ Request.smallSize a (.sym r four L target) := NearCubicWires.PacketsGlue.RequestMeta.one_le_small a _
  have hmS := RowsInit.LoopCost.qT_le_small a (.sym r four L target)
  have pw : ∀ k, k ≤ dS a → (Request.smallSize a (.sym r four L target)) ^ k ≤
      (Request.smallSize a (.sym r four L target)) ^ dS a := fun k hk => Nat.pow_le_pow_right hS1 hk
  have p1 : Request.smallSize a (.sym r four L target) ≤ (Request.smallSize a (.sym r four L target)) ^ dS a := by
    have := pw 1 (by unfold dS; omega)
    rwa [pow_one] at this
  -- the loop block (RS), table exponent at the geometry
  have hres := RowsInit.LoopCost.compl_residual a (.sym r four L target)
    (PCJ9eff70d512234a4c_Fixed.Packets.geometry selector _)
  have hSL : RowsInit.SymLoop.cost a (.sym r four L target) ≤
      RowsInit.LoopCost.symK a * (Request.smallSize a (.sym r four L target)) ^ dS a +
      RowsInit.LoopCost.symK a * (2 ^ (PCJ9eff70d512234a4c_Fixed.Packets.residual ((Request.sym r four L target).family a)) *
        ((Request.sym r four L target).q + ((Request.sym r four L target).input a).length + 1) ^ dS a) := by
    have h := RowsInit.LoopCost.sym_cost_le a (.sym r four L target)
    rw [hres] at h
    have hm : ((Request.sym r four L target).q + ((Request.sym r four L target).input a).length + 1) ^
        RowsInit.LoopCost.symD a ≤
        ((Request.sym r four L target).q + ((Request.sym r four L target).input a).length + 1) ^ dS a :=
      Nat.pow_le_pow_right (by omega) (by unfold dS; omega)
    have hP := pw (RowsInit.LoopCost.symD a) (by unfold dS; omega)
    rw [← Nat.mul_add]
    exact h.trans (Nat.mul_le_mul_left _ (Nat.add_le_add hP (Nat.mul_le_mul_left _ hm)))
  -- the words and C5 vector stages
  have hW := ((RowsInit.FrameSymWords.symVec a).cost_le (.sym r four L target)).trans
    (Nat.mul_le_mul_left _ (pw _ (by unfold dS; omega)))
  have hC := ((RowsInit.C5.c5Vec a).cost_le (.sym r four L target)).trans
    (Nat.mul_le_mul_left _ (pw _ (by unfold dS; omega)))
  -- the seed count
  have hN : NearCubicWires.PacketsGlue.RequestMeta.seedCount a (.sym r four L target) ≤
      8 * (Request.smallSize a (.sym r four L target)) ^ dS a :=
    (NearCubicWires.PacketsMeta.Seed.seedCount_le_small a _).trans (Nat.mul_le_mul_left 8 (pw 163 (by unfold dS; omega)))
  -- the key-0 writer
  have hK : KeyZeroMode.k0Cost a (.sym r four L target) ≤
      128 * (((Request.sym r four L target).input a).length + 3 + symRes r.q (symT a r four L target) + 1) :=
    k0_lin (SymC5.sw a r four L target) (symRes r.q (symT a r four L target))
  have hRs : symRes r.q (symT a r four L target) ≤ (symRc + 1) * (Request.smallSize a (.sym r four L target)) ^ dS a :=
    (RowsInit.LoopCost.res_le a (.sym r four L target) symRd (symRc + 1)).trans
      (Nat.mul_le_mul_left _ (pw _ (by unfold dS; omega)))
  have hT : ((Request.sym r four L target).input a).length ≤ (Request.smallSize a (.sym r four L target)) ^ dS a := by
    omega
  exact assemble _ _ _ _ _ _ _ _ _ _ _ _ _ hW hSL hC hN hK hRs hT

end Sym

/-- **The SYM branch's cost, as one pair of constants per `a`** (the exact form RW asked for, RW 04:4x). -/
theorem sym_cost_exists (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws) (a : DecompositionAlgorithm) :
    ∃ c d : ℕ, ∀ (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r.circuits.length ≤ 4) (L target : ℕ),
      RowsInit.FrameSymWork.neCost a (RowsInit.FrameSymInst.symLoop a) (.sym r four L target) + 2 ≤
        c * ((Request.smallSize a (.sym r four L target)) ^ d +
          2 ^ (PCJ9eff70d512234a4c_Fixed.Packets.residual ((Request.sym r four L target).family a)) *
            ((Request.sym r four L target).q + ((Request.sym r four L target).input a).length + 1) ^ d + 1) :=
  ⟨cS a, dS a, sym_cost_le a selector⟩

/-- The empty-family branch (`symSpec`'s `costE`) is the switch alone: `0 + 2`. -/
theorem costE_eq (a : DecompositionAlgorithm) (NI oB : ℕ) (h : 146 ≤ NI) (hB : 150 ≤ oB)
    (hS : oB + RowsInit.FrameSymWork.needS a (RowsInit.FrameSymInst.symLoop a) ≤ NI) (r : Request) :
    (RowsInit.FrameSymInst.symSpec a NI oB h hB hS).costE r = 2 := rfl

/-- `symSpec`'s `costNe` IS `neCost + 2`. -/
theorem costNe_eq (a : DecompositionAlgorithm) (NI oB : ℕ) (h : 146 ≤ NI) (hB : 150 ≤ oB)
    (hS : oB + RowsInit.FrameSymWork.needS a (RowsInit.FrameSymInst.symLoop a) ≤ NI) (r : Request) :
    (RowsInit.FrameSymInst.symSpec a NI oB h hB hS).costNe r =
      RowsInit.FrameSymWork.neCost a (RowsInit.FrameSymInst.symLoop a) r + 2 := rfl

end
end RowsInit.FrameSymCost
