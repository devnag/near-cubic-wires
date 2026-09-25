import Proof.Packets.PacketsCoordLen
import Proof.Packets.PacketsCombineAllRunCost

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.Residual
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.SupplierListSchedule
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore PCJ9eff70d512234a4c_Fixed.Materializer
open Theorem25Completion Theorem25Completion.CycleBounds
noncomputable section

theorem graded_le_any (C w root population active : ℕ) (mask : Finset (Fin population))
    (hactive : active ≤ population) (hC : (258 * population + 2) ^ 2 ≤ C) (hw : 3 ≤ w)
    (hroot : root ≤ commonReserve C w) (hrank : Completion.SourceGradedRank.rank population active ≤ 9 * population)
    (hdepth : Completion.SourceGradedRank.depth active ≤ C) :
    WalkLiteralMasters.gradedBudget C (commonReserve C w) root population active
      (List.ofFn (fun i => decide (i ∈ mask))) ≤ 65 * commonReserve C w := by
  have rankCost : Completion.SourceGradedRank.budget population active + 1 ≤ commonReserve C w :=
    (Completion.SourceGradedRank.budget_bound population active).trans
      (WalkLiteralMasters.graded_capacity_le C w population active hactive hC hw)
  have hR := ConeBounds.reserve_ge C w
  have hpC : 258 * population + 2 ≤ C :=
    (show 258 * population + 2 ≤ (258 * population + 2) ^ 2 from Nat.le_self_pow (by norm_num) _).trans hC
  have fits : WalkLiteralMasters.Bounds C (commonReserve C w) root (Completion.SourceGradedRank.rank population active)
      (Completion.SourceGradedRank.depth active) population (List.ofFn (fun i => decide (i ∈ mask))) := by
    refine ⟨?_, ?_, hroot, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · rw [List.length_ofFn]; omega
  have paletteCost := WalkLiteralMasters.budget_le C (commonReserve C w) root
    (Completion.SourceGradedRank.rank population active) (Completion.SourceGradedRank.depth active) population
    (List.ofFn (fun i => decide (i ∈ mask))) fits
  unfold WalkLiteralMasters.gradedBudget
  omega

theorem allRun_budget_le_any {population active depth : ℕ} (C w root n : ℕ) (mask : Finset (Fin population))
    (hC : (258 * population + 2) ^ 2 ≤ C) (hdC : depth ≤ C) (hw : 3 ≤ w)
    (hroot : root ≤ commonReserve C w) (hdepth : depth = Completion.SourceGradedRank.depth active)
    (hactive : active ≤ population) (hrank : canonicalGradedRank population active ≤ 9 * population)
    (hCodes : 2 ^ (n + 1) ≤ 2 ^ w) :
    WalkLiteralProducedMajority.budget C w root population active depth n (List.ofFn (fun i => decide (i ∈ mask))) ≤
      2 ^ 119 * (commonReserve C w) ^ 27 := by
  have hR := PacketsCombine.AllRunCost.R_pos C w
  have hpopC : population ≤ C := by
    have h1 : 258 * population + 2 ≤ (258 * population + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have hP : 2 ^ (n + 1) ≤ commonReserve C w := hCodes.trans (PacketsCombine.AllRunCost.pow_le_R C w)
  have hn4 : n + 4 ≤ commonReserve C w := by
    have hn1 : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
    have h8 : 2 ^ w ≤ 2 ^ (8 * w) := Nat.pow_le_pow_right (by omega) (by omega)
    have h1 : 1 ≤ 2 ^ (8 * w) := Nat.one_le_two_pow
    have := PacketsCombine.AllRunCost.R_ge C w
    omega
  have hN := PacketsCombine.AllRunCost.pop_le_R C w population hpopC
  have hgraded := graded_le_any C w root population active mask hactive hC hw hroot hrank (hdepth ▸ hdC)
  have hres := literal_produced_reserve_cost C w population active root depth n
    (List.ofFn (fun i => decide (i ∈ mask))) hw hpopC hdC hroot hrank hgraded
  have hres' := hres.trans (PacketsCombine.AllRunCost.reserveTail_le C w n (by omega))
  have hpre := PacketsCombine.AllRunCost.prefix_le C w population n hN hn4 hP
  have hall := PacketsCombine.AllRunCost.all_le C w population (n + 1) hN (by omega) hP
  have hS := PacketsCombine.AllRunCost.S_le C w
  obtain ⟨p2, p3, p4, p5, p27, p0⟩ := PacketsCombine.AllRunCost.pows (commonReserve C w) hR
  show WalkLiteralProducedReserve.budget C w root population active depth n (List.ofFn (fun i => decide (i ∈ mask))) +
    1 + WalkLiteralProducedMajority.prefixBudget C w population n + 1 +
    WalkTranscriptColumn.allBudget C w population (n + 1) ≤ _
  linarith

theorem budget_family {q : ℕ} (occ : List (SupportedNormalizedGate q)) (I : Finset (Fin q)) (den C w : ℕ)
    (M : Finset (Fin occ.length)) (hC : (258 * occ.length + 2) ^ 2 ≤ C)
    (hcode : (canonicalGradedDepth (LiveRows.bound occ I) + 2 * occ.length + 2) ^ 2 ≤ C) (hw : 3 ≤ w)
    (hwalk : 2 ^ canonicalWalkLength den ≤ 2 ^ w) :
    ConeRun.budget occ I den C w M ≤ 2 ^ 119 * (commonReserve C w) ^ 27 := by
  have hB := bound_le_pop occ I
  have hRC := ConeBounds.reserve_ge C w
  have hpC : 258 * occ.length + 2 ≤ C :=
    (show 258 * occ.length + 2 ≤ (258 * occ.length + 2) ^ 2 from Nat.le_self_pow (by norm_num) _).trans hC
  have hdC : canonicalGradedDepth (LiveRows.bound occ I) ≤ C := by
    have : canonicalGradedDepth (LiveRows.bound occ I) + 2 * occ.length + 2 ≤
        (canonicalGradedDepth (LiveRows.bound occ I) + 2 * occ.length + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have hroot := ConeBounds.root_le (LiveRows.bound occ I)
  have hrank : canonicalGradedRank occ.length (LiveRows.bound occ I) ≤ 9 * occ.length := by
    rcases Nat.eq_zero_or_pos occ.length with h0 | h0
    · have hz : canonicalGradedRank occ.length (LiveRows.bound occ I) = 0 :=
        (ConeBounds.rank_eq_zero_iff _ _ hB).2 ⟨by omega, by omega⟩
      omega
    · exact ConeBounds.rank_le _ _ hB h0
  exact allRun_budget_le_any (population := occ.length) (active := LiveRows.bound occ I)
    (depth := canonicalGradedDepth (LiveRows.bound occ I)) C w (ConeWindow.root (LiveRows.bound occ I))
    (2 * Nat.clog 2 (den + 1)) M hC hdC hw (by omega) rfl hB hrank hwalk

variable (a : DecompositionAlgorithm)

/-- The route-A capacity facts at any request (no keyed condition). -/
theorem caps (K : KitShape a) (r : Request) :
    (canonicalGradedDepth (LiveRows.bound (r.family a).occurrences (Packets.live (r.family a))) +
        2 * (r.family a).occurrences.length + 2) ^ 2 ≤ K.C r ∧ 3 ≤ K.w r ∧
      2 ^ canonicalWalkLength (r.denominator a) ≤ 2 ^ (K.w r) := by
  have hcode := K.codes r
  unfold codeNeed at hcode
  have hwalk := small_walk a r
  have hcen := K.census r
  have hocc := small_occ a r
  have hs12 : r.smallSize a ≤ (r.smallSize a) ^ 12 := Nat.le_self_pow (by norm_num) _
  have hs2 : 2 ≤ r.smallSize a := by
    have : 2 ≤ ((r.family a).occurrences.length + 2) ^ (r.degree a + 1) :=
      (Nat.le_self_pow (by omega) _).trans' (by omega)
    omega
  have hw : 3 ≤ K.w r := by
    by_contra hlt
    have h1 : 2 ^ (K.w r) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ 12 ≤ (r.smallSize a) ^ 12 := Nat.pow_le_pow_left hs2 12
    omega
  exact ⟨by omega, hw, by omega⟩

/-- **The external budget of every mask of every key, bounded by one polynomial of the reserve.** -/
theorem budgetOf_le (K : KitShape a) (hA : ConeBounds.RouteA a K) (r : Request) (k : rcKey a r) (j : ℕ) :
    ConeRun.budgetOf a K r k j ≤ 2 ^ 119 * (commonReserve (K.C r) (K.w r)) ^ 27 := by
  obtain ⟨hcode, hw, hwalk⟩ := caps a K r
  have hC := hA r
  cases r with
  | terminal => exact PEmpty.elim k
  | sym r0 four L target =>
    exact budget_family (symmetricFourfoldOccurrences r0) (CyclicChoice.live (symmetricFourfoldOccurrences r0) L)
      (symmetricListDenominator r0 target) _ _ _ hC hcode hw hwalk
  | thr r0 four L target =>
    exact budget_family (thresholdFourfoldOccurrences r0) (CyclicChoice.live (thresholdFourfoldOccurrences r0) L)
      (CloseoutFinalC10ThresholdRows.listDenominator a r0 target) _ _ _ hC hcode hw hwalk

end
end NearCubicWires.PacketsConstruction.Residual
