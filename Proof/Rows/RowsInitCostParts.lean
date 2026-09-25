import Proof.Rows.RowsLoopCostBound
import Proof.Rows.RowsInitWorkPhase

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsInit.InitCost
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open PCJd4d1d9d7d1fa4313_Production NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.SupplierPipeline
open NearCubicWires.ValidatorPolynomialDomination NearCubicWires.BlockPlatform
open RowsConstruction RowsConstruction.BaseLayout
noncomputable section

/-! ## 1. Small helpers -/

theorem pb_of_le {x S c d : ℕ} (h : x ≤ c * S ^ d) : PolyBounded x S c d :=
  le_trans h (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ S) d))

theorem pb_of_vb {x S c d : ℕ} (h : x + 3 ≤ (c + 7) * S ^ (d + 1)) : PolyBounded x S (c + 7) (d + 1) :=
  pb_of_le (by omega)

/-- A `PolyBounded` quantity in `smallSize` (`S ≥ 1`) is at most `c·2^d·S^d`. -/
theorem pb_small {x S c d : ℕ} (h : PolyBounded x S c d) (hS : 1 ≤ S) : x ≤ c * 2 ^ d * S ^ d := by
  unfold PolyBounded at h
  have h1 : (S + 1) ^ d ≤ 2 ^ d * S ^ d := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) d
  calc x ≤ c * (S + 1) ^ d := h
    _ ≤ c * (2 ^ d * S ^ d) := Nat.mul_le_mul_left _ h1
    _ = c * 2 ^ d * S ^ d := by ring

/-! ## 2. The work-phase prefix -/

/-- **(1) The prefix** (`RowsInitPrefix`: `pfxVec`, the metadata unwrap, `caps_dock`). -/
theorem prefix_cost_le (a : DecompositionAlgorithm) : ∃ c d : ℕ, ∀ (r : Request) (w deg C hF cC dR rR : ℕ),
    RowsInit.Prefix.cost a r w deg C hF cC dR rR ≤ c * ((r.smallSize a) ^ d + C + hF + cC + dR +
      (RowsInit.metaWord w deg C hF cC dR rR).length + 1) := by
  refine ⟨2 * (RowsInit.Prefix.pfxVec a).coefficient + 406, (RowsInit.Prefix.pfxVec a).degree, fun r w deg C hF cC dR rR => ?_⟩
  have hp := (RowsInit.Prefix.pfxVec a).cost_le r
  have hc := RowsInit.capsCost_le w deg C hF cC dR rR
  set P := (r.smallSize a) ^ (RowsInit.Prefix.pfxVec a).degree with hP
  set m := (RowsInit.metaWord w deg C hF cC dR rR).length with hm
  set pc := (RowsInit.Prefix.pfxVec a).coefficient with hpc
  have hS : P ≤ P + C + hF + cC + dR + m + 1 := by omega
  have q1 : pc * P ≤ pc * (P + C + hF + cC + dR + m + 1) := Nat.mul_le_mul_left _ hS
  have e : (2 * pc + 406) * (P + C + hF + cC + dR + m + 1) =
      2 * (pc * (P + C + hF + cC + dR + m + 1)) + 406 * (P + C + hF + cC + dR + m + 1) := by ring
  unfold RowsInit.Prefix.cost
  rw [e]
  omega

/-! ## 3. The THR branch -/

/-- The prime-reserve value stage (the `UnaryStage` under RX's `rpS`), for its `value_bound`. -/
def rpU (a : DecompositionAlgorithm) : UnaryStage a (RowsInit.ThrInitWords.rpVal a) :=
  ((inputLenStage a).pairP (NearCubicWires.PacketsMeta.cutoffStage a) addMap2 6 1 add_cost).thenMapP
    (RowsInit.LoopWords.polyMap 3 16384) (UnaryCalc.polyCoefficient 3 16384) (3+1) (RowsInit.LoopWords.poly_cost 3 16384)

section Thr
variable (a : DecompositionAlgorithm) (bnd : Request → Fin 4 → ℕ)
  (bndW : (c : Fin 4) → WordStage a (fun r => frame (SignedSortKey.binary (r.input a).length (bnd r c))))

/-- RX's THR init-word vector stage at the base constants. -/
abbrev ivOf := RowsInit.ThrInitWords.initVec a bnd bndW ThrSelBase.bcD ThrSelBase.bdD ThrSelBase.bcU ThrSelBase.bdU

/-- The THR branch cost without the table stage, summand by summand. -/
def EOf (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4) (L target : ℕ) : ℕ :=
  2 * (ivOf a bnd bndW).cost (.thr r four L target) +
    2 * RowsInit.ThrInitWords.rpVal a (.thr r four L target) +
    2 * ThrSelBase.bU ((Request.thr r four L target).input a).length +
    2 * (RowsInit.C5.c5Vec a).cost (.thr r four L target) +
    2 * seedScratch (seedCount a (.thr r four L target)) +
    2 * (Uf r.q ((Request.thr r four L target).input a).length + Ff r.q ((Request.thr r four L target).input a).length) +
    4 * ThrSelBase.bF ((Request.thr r four L target).input a).length +
    1000 * ((Request.thr r four L target).input a).length + 2000

/-- Its degree and coefficient (`c1 d1` from `ThrSelBase.b_poly`, `c2 d2` from `fns_poly`). -/
def D0Of (d1 d2 : ℕ) : ℕ :=
  (ivOf a bnd bndW).degree + ((rpU a).degree + 1) + d1 + (RowsInit.C5.c5Vec a).degree +
    ((RowsInit.C5.scrS a).degree + 1) + d2 + 1
def cEOf (c1 c2 : ℕ) : ℕ :=
  2 * (ivOf a bnd bndW).coefficient + 2 * ((rpU a).coefficient + 7) + 2 * c1 + 2 * (RowsInit.C5.c5Vec a).coefficient +
    2 * ((RowsInit.C5.scrS a).coefficient + 7) + 2 * c2 + 4 * c1 + 1000 * 1 + 2000

/-- The THR branch cost splits into `EOf` and the loop block (whose table stage is the only `2^residual` term). -/
theorem thr_ne_split (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : ℕ) :
    RowsInit.ThrWork.neCost a bnd bndW r four L target ≤
      EOf a bnd bndW r four L target + RowsInit.ThrLoop.cost a (.thr r four L target) := by
  have eU : ThrSelBase.bU ((Request.thr r four L target).input a).length =
      ThrBaseBounds.UOf' ThrSelBase.bcD ThrSelBase.bdD ThrSelBase.bcU ThrSelBase.bdU
        ((Request.thr r four L target).input a).length := rfl
  have eT : ThrWidth.T a r four L target = ((Request.thr r four L target).input a).length := rfl
  have eW : KeyTop.wT a r four L target = 12 * ((Request.thr r four L target).input a).length + 19 := rfl
  have eI : (ivOf a bnd bndW).cost (.thr r four L target) =
      (RowsInit.ThrInitWords.initVec a bnd bndW ThrSelBase.bcD ThrSelBase.bdD ThrSelBase.bcU ThrSelBase.bdU).cost
        (.thr r four L target) := rfl
  unfold RowsInit.ThrWork.neCost RowsInit.ThrWork.mainCost RowsInit.ThrWork.preCost RowsInit.ThrInitRun.cost
    RowsInit.C5.cost KeyZeroThr.thrK0Cost KeyZeroThr.zc ThrSelBase.baseCost EOf
  rw [eW, eT]
  omega

/-- `EOf` is ONE fixed polynomial of `smallSize`. -/
theorem thr_ne_poly (c1 d1 : ℕ) (h1 : ∀ T : ℕ, PolyBounded (ThrSelBase.bD T + ThrSelBase.bU T + ThrSelBase.bF T) T c1 d1)
    (c2 d2 : ℕ) (h2 : ∀ q T : ℕ, PolyBounded (Uf q T + Ff q T + Pf q T + Bf q T) (q + T) c2 d2)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4) (L target : ℕ) :
    PolyBounded (EOf a bnd bndW r four L target) ((Request.thr r four L target).smallSize a) (cEOf a bnd bndW c1 c2)
      (D0Of a bnd bndW d1 d2) := by
  have hTS : ((Request.thr r four L target).input a).length + 1 ≤ (Request.thr r four L target).smallSize a :=
    input_le_small a _
  have hqT : r.q + ((Request.thr r four L target).input a).length ≤ (Request.thr r four L target).smallSize a := by
    have := RowsInit.LoopCost.qT_le_small a (.thr r four L target)
    have e : (Request.thr r four L target).q = r.q := rfl
    omega
  unfold EOf cEOf
  have hD : ∀ x, x ≤ D0Of a bnd bndW d1 d2 → x ≤ D0Of a bnd bndW d1 d2 := fun _ h => h
  have p1 := ((pb_of_le ((ivOf a bnd bndW).cost_le (.thr r four L target))).const_mul 2).degree_mono
    (hD _ (by unfold D0Of; omega))
  have p2 := ((pb_of_vb ((rpU a).value_bound (.thr r four L target))).const_mul 2).degree_mono
    (hD _ (by unfold D0Of; omega))
  have hb := h1 ((Request.thr r four L target).input a).length
  have p3 := (((hb.mono (show ThrSelBase.bU ((Request.thr r four L target).input a).length ≤
    ThrSelBase.bD ((Request.thr r four L target).input a).length + ThrSelBase.bU ((Request.thr r four L target).input a).length +
      ThrSelBase.bF ((Request.thr r four L target).input a).length by omega)).measure_mono (show ((Request.thr r four L target).input a).length ≤
      (Request.thr r four L target).smallSize a by omega)).const_mul 2).degree_mono
    (hD _ (by unfold D0Of; omega))
  have p4 := ((pb_of_le ((RowsInit.C5.c5Vec a).cost_le (.thr r four L target))).const_mul 2).degree_mono
    (hD _ (by unfold D0Of; omega))
  have p5 := ((pb_of_vb ((RowsInit.C5.scrS a).value_bound (.thr r four L target))).const_mul 2).degree_mono
    (hD _ (by unfold D0Of; omega))
  have hf := h2 r.q ((Request.thr r four L target).input a).length
  have p6 := (((hf.mono (show Uf r.q ((Request.thr r four L target).input a).length + Ff r.q ((Request.thr r four L target).input a).length ≤
    Uf r.q ((Request.thr r four L target).input a).length + Ff r.q ((Request.thr r four L target).input a).length +
      Pf r.q ((Request.thr r four L target).input a).length + Bf r.q ((Request.thr r four L target).input a).length by omega)).measure_mono hqT).const_mul 2).degree_mono
    (hD _ (by unfold D0Of; omega))
  have p7 := (((hb.mono (show ThrSelBase.bF ((Request.thr r four L target).input a).length ≤
    ThrSelBase.bD ((Request.thr r four L target).input a).length + ThrSelBase.bU ((Request.thr r four L target).input a).length +
      ThrSelBase.bF ((Request.thr r four L target).input a).length by omega)).measure_mono (show ((Request.thr r four L target).input a).length ≤
      (Request.thr r four L target).smallSize a by omega)).const_mul 4).degree_mono
    (hD _ (by unfold D0Of; omega))
  have p8 := ((show PolyBounded ((Request.thr r four L target).input a).length ((Request.thr r four L target).smallSize a)
    1 1 by unfold PolyBounded; rw [pow_one]; omega).const_mul 1000).degree_mono (hD _ (by unfold D0Of; omega))
  have p9 := polyBounded_const 2000 ((Request.thr r four L target).smallSize a) (D0Of a bnd bndW d1 d2)
  exact ((((((((p1.add p2).add p3).add p4).add p5).add p6).add p7).add p8).add p9)

end Thr

/-- **(2) The THR branch** (`RowsInit.ThrWork.neCost`), in `rowInitBudget`'s shape. -/
theorem thr_ne_cost_le (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws) (a : DecompositionAlgorithm)
    (bnd : Request → Fin 4 → ℕ)
    (bndW : (c : Fin 4) → WordStage a (fun r => frame (SignedSortKey.binary (r.input a).length (bnd r c)))) :
    ∃ c d : ℕ, ∀ (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4) (L target : ℕ),
      RowsInit.ThrWork.neCost a bnd bndW r four L target ≤
        c * (((Request.thr r four L target).smallSize a) ^ d +
          2 ^ PCJ9eff70d512234a4c_Fixed.Packets.residual ((Request.thr r four L target).family a) *
            ((Request.thr r four L target).q + ((Request.thr r four L target).input a).length + 1) ^ d + 1) := by
  obtain ⟨c1, d1, h1⟩ := ThrSelBase.b_poly
  obtain ⟨c2, d2, h2⟩ := fns_poly
  refine ⟨cEOf a bnd bndW c1 c2 * 2 ^ D0Of a bnd bndW d1 d2 + RowsInit.LoopCost.thrK a,
    D0Of a bnd bndW d1 d2 + RowsInit.LoopCost.thrD a, fun r four L target => ?_⟩
  have hS1 : 1 ≤ (Request.thr r four L target).smallSize a := one_le_small a _
  have hsplit := thr_ne_split a bnd bndW r four L target
  have hE := pb_small (thr_ne_poly a bnd bndW c1 d1 h1 c2 d2 h2 r four L target) hS1
  have hL := RowsInit.LoopCost.thr_cost_le a (.thr r four L target)
  rw [RowsInit.LoopCost.compl_residual a _
    (PCJ9eff70d512234a4c_Fixed.Packets.geometry selector ((Request.thr r four L target).family a))] at hL
  generalize RowsInit.ThrWork.neCost a bnd bndW r four L target = N at hsplit ⊢
  generalize EOf a bnd bndW r four L target = E at hsplit hE
  generalize RowsInit.ThrLoop.cost a (.thr r four L target) = Lc at hsplit hL
  generalize cEOf a bnd bndW c1 c2 * 2 ^ D0Of a bnd bndW d1 d2 = K1 at hE ⊢
  generalize D0Of a bnd bndW d1 d2 = D0 at hE ⊢
  generalize RowsInit.LoopCost.thrK a = K2 at hL ⊢
  generalize RowsInit.LoopCost.thrD a = D2 at hL ⊢
  generalize (Request.thr r four L target).smallSize a = S at hS1 hE hL ⊢
  generalize hm : (Request.thr r four L target).q + ((Request.thr r four L target).input a).length + 1 = m at hL ⊢
  generalize 2 ^ PCJ9eff70d512234a4c_Fixed.Packets.residual ((Request.thr r four L target).family a) = Y0 at hL ⊢
  have hm1 : 1 ≤ m := by omega
  have s1 : S ^ D0 ≤ S ^ (D0 + D2) := Nat.pow_le_pow_right hS1 (by omega)
  have s2 : S ^ D2 ≤ S ^ (D0 + D2) := Nat.pow_le_pow_right hS1 (by omega)
  have s3 : Y0 * m ^ D2 ≤ Y0 * m ^ (D0 + D2) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hm1 (by omega))
  have t1 : K1 * S ^ D0 ≤ K1 * S ^ (D0 + D2) := Nat.mul_le_mul_left _ s1
  have t2 : K2 * (S ^ D2 + Y0 * m ^ D2) ≤ K2 * (S ^ (D0 + D2) + Y0 * m ^ (D0 + D2)) :=
    Nat.mul_le_mul_left _ (by omega)
  have e1 : K2 * (S ^ (D0 + D2) + Y0 * m ^ (D0 + D2)) = K2 * S ^ (D0 + D2) + K2 * (Y0 * m ^ (D0 + D2)) := by ring
  have e2 : (K1 + K2) * (S ^ (D0 + D2) + Y0 * m ^ (D0 + D2) + 1) =
      K1 * S ^ (D0 + D2) + K2 * S ^ (D0 + D2) + K1 * (Y0 * m ^ (D0 + D2)) + K2 * (Y0 * m ^ (D0 + D2)) + K1 + K2 := by
    ring
  rw [e2]
  omega

end
end RowsInit.InitCost
