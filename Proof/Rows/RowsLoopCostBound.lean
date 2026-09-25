import Proof.Rows.RowsSymLoop

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsInit.LoopCost
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open PCJd4d1d9d7d1fa4313_Production NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.SupplierPipeline
open RowsConstruction RowsConstruction.BaseLayout NearCubicWires.BlockPlatform
noncomputable section

/-! ## 1. The arithmetic -/

/-- `2·tableCost s + 2 ≤ 8002·2^s·m` for `s + 1 ≤ m`. -/
theorem table_le (s m : ℕ) (hs : s + 1 ≤ m) : 2 * RowsInit.LoopTable.tableCost s + 2 ≤ 8002 * (2 ^ s * m) := by
  have h := RowsInit.LoopTable.table_cost_le s
  have h1 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
  have h2 : (2 ^ s + 1) * (s + 1) ≤ (2 * 2 ^ s) * m := Nat.mul_le_mul (by omega) hs
  have h3 : 1 ≤ 2 ^ s * m := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have e : 2 * 2 ^ s * m = 2 * (2 ^ s * m) := by ring
  omega

/-- **The generic bound** for a loop-block writer of RX's shape `((2V+2)+1+(2R+4))+1+(2X+2))+1+(2·tableCost s+2)`. -/
theorem loop_bound (V R X s S m cV dV cX dX cR dR : ℕ) (hV : V ≤ cV * S ^ dV) (hX : X ≤ cX * S ^ dX)
    (hR : R ≤ cR * S ^ dR) (hS : 1 ≤ S) (hs : s + 1 ≤ m) :
    (((2 * V + 2) + 1 + (2 * R + 4)) + 1 + (2 * X + 2)) + 1 + (2 * RowsInit.LoopTable.tableCost s + 2) ≤
      (2 * cV + 2 * cX + 2 * cR + 8015) * (S ^ (dV + dX + dR + 1) + 2 ^ s * m ^ (dV + dX + dR + 1)) := by
  set D := dV + dX + dR + 1 with hD
  have pV : S ^ dV ≤ S ^ D := Nat.pow_le_pow_right hS (by omega)
  have pX : S ^ dX ≤ S ^ D := Nat.pow_le_pow_right hS (by omega)
  have pR : S ^ dR ≤ S ^ D := Nat.pow_le_pow_right hS (by omega)
  have p1 : 1 ≤ S ^ D := Nat.one_le_pow _ _ (by omega)
  have pm : m ≤ m ^ D := Nat.le_self_pow (by omega) m
  have hT := table_le s m hs
  have hT' : 2 ^ s * m ≤ 2 ^ s * m ^ D := Nat.mul_le_mul_left _ pm
  have qV : cV * S ^ dV ≤ cV * S ^ D := Nat.mul_le_mul_left _ pV
  have qX : cX * S ^ dX ≤ cX * S ^ D := Nat.mul_le_mul_left _ pX
  have qR : cR * S ^ dR ≤ cR * S ^ D := Nat.mul_le_mul_left _ pR
  have e : (2 * cV + 2 * cX + 2 * cR + 8015) * (S ^ D + 2 ^ s * m ^ D) =
      2 * (cV * S ^ D) + 2 * (cX * S ^ D) + 2 * (cR * S ^ D) + 8015 * S ^ D +
        (2 * (cV * (2 ^ s * m ^ D)) + 2 * (cX * (2 ^ s * m ^ D)) + 2 * (cR * (2 ^ s * m ^ D)) +
          8015 * (2 ^ s * m ^ D)) := by ring
  rw [e]
  omega

/-- `q + |input| + 1 ≤ smallSize`. -/
theorem qT_le_small (a : DecompositionAlgorithm) (r : Request) : r.q + (r.input a).length + 1 ≤ r.smallSize a := by
  have key : ∀ q n x1 x2 x3 x4 x5 x6 : ℕ, q + n + 1 ≤ q + n + x1 + x2 + x3 + x4 + x5 + x6 + 1 := by
    intros; omega
  unfold Request.smallSize
  exact key _ _ _ _ _ _ _ _

/-- `|liveᶜ| + 1 ≤ q + |input| + 1`. -/
theorem compl_le (a : DecompositionAlgorithm) (r : Request) :
    RowsInit.complCount a r + 1 ≤ r.q + (r.input a).length + 1 := by
  unfold RowsInit.complCount
  exact Nat.succ_le_succ (le_trans (card_compl_le _) (Nat.le_add_right _ _))

/-- A fixed polynomial reserve `C·(q+|input|+1)^D` is at most `C·smallSize^D`. -/
theorem res_le (a : DecompositionAlgorithm) (r : Request) (D C : ℕ) :
    UnaryCalc.value D C (r.q + (r.input a).length) ≤ C * (r.smallSize a) ^ D := by
  have h := qT_le_small a r
  have hp : (r.q + (r.input a).length + 1) ^ D ≤ (r.smallSize a) ^ D := Nat.pow_le_pow_left h D
  simp only [UnaryCalc.value]
  exact Nat.mul_le_mul_left _ hp

/-! ## 2. The two loop-block writers -/

section Consts
variable (a : DecompositionAlgorithm)

def symK : ℕ := 2 * (RowsInit.SymLoopWords.symVec a).coefficient + 2 * (RowsInit.LoopAux.auxVec a).coefficient +
  2 * (symRc + 1) + 8015
def symD : ℕ := (RowsInit.SymLoopWords.symVec a).degree + (RowsInit.LoopAux.auxVec a).degree + symRd + 1
def thrK : ℕ := 2 * (RowsInit.LoopWords.loopVec a).coefficient + 2 * (RowsInit.LoopAux.auxVec a).coefficient +
  2 * (thrRc + 1) + 8015
def thrD : ℕ := (RowsInit.LoopWords.loopVec a).degree + (RowsInit.LoopAux.auxVec a).degree + thrRd + 1

end Consts

theorem sym_cost_le (a : DecompositionAlgorithm) (r : Request) :
    RowsInit.SymLoop.cost a r ≤ symK a * ((r.smallSize a) ^ symD a +
      2 ^ RowsInit.complCount a r * (r.q + (r.input a).length + 1) ^ symD a) :=
  loop_bound _ _ _ _ _ _ _ _ _ _ _ _ (RowsInit.SymLoopWords.vec_cost_le a r) ((RowsInit.LoopAux.auxVec a).cost_le r)
    (res_le a r symRd (symRc + 1)) (NearCubicWires.PacketsGlue.RequestMeta.one_le_small a r) (compl_le a r)

theorem thr_cost_le (a : DecompositionAlgorithm) (r : Request) :
    RowsInit.ThrLoop.cost a r ≤ thrK a * ((r.smallSize a) ^ thrD a +
      2 ^ RowsInit.complCount a r * (r.q + (r.input a).length + 1) ^ thrD a) :=
  loop_bound _ _ _ _ _ _ _ _ _ _ _ _ (RowsInit.LoopWords.loop_cost_le a r) ((RowsInit.LoopAux.auxVec a).cost_le r)
    (res_le a r thrRd (thrRc + 1)) (NearCubicWires.PacketsGlue.RequestMeta.one_le_small a r) (compl_le a r)

/-- The exponent of the table factor IS the family's residual (at any geometry; `RowsPartsStep.residual_eq`'s proof). -/
theorem compl_residual (a : DecompositionAlgorithm) (r : Request)
    (g : PCJ9eff70d512234a4c_Fixed.Packets.Geometry (r.family a)) :
    RowsInit.complCount a r = PCJ9eff70d512234a4c_Fixed.Packets.residual (r.family a) := by
  unfold RowsInit.complCount
  rw [Finset.card_compl, Fintype.card_fin, g.card]

end
end RowsInit.LoopCost
