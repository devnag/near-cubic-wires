import Proof.CaseAnalysis.FinalLedgerAssembly

namespace NearCubicWires.RepairSource.CloseoutFinal.C10LedgerBounds

open RepairOrdinary SourceInterfaces SelectedRecoveryIntegration
open RepairOrdinary.CloseoutFinalC10StageSeam (dockedFuel)
open RepairOrdinary.CloseoutFinalC10WorkerDock (joinScalarWidth dockBudget)
open RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-! ## Section 1  `hrows` -- the clause-address count against a power of the width -/

/-! ## Section 2  `hrow` -- one external row against one residual table factor -/

/-! ## Section 3  `hdriver` -- the words stage against a power of the width -/

/-- `CompetitorDimensions.budget` (`Proof/Hierarchy/CompetitorDimensions.lean`) is
quadratic: its dominant summand is `WilliamsUnaryProduct.budget ((b+1)*(b+1)) 4096`. -/
theorem dimensions_budget_le (b : ℕ) :
    CompetitorDimensions.budget b ≤ 25000 * (b + 1) ^ 2 := by
  unfold CompetitorDimensions.budget CompetitorDimensions.bootstrapBudget
    WilliamsUnaryProduct.budget
  nlinarith

/-- The join width (`Proof/CaseAnalysis/FinalWorkerDock.lean`) is bilinear in
the record width and the call count. -/
theorem joinScalarWidth_le (ew cc : ℕ) :
    joinScalarWidth ew cc ≤ 3 * (ew + cc + 1) ^ 2 := by
  unfold joinScalarWidth CompetitorSumWidth.width CompetitorRationalDecision.width
  nlinarith

/-- **The words stage's fuel is quartic in the record width plus the call count.**
Every one of `wordsFuel`'s seventeen engine budgets
(`Proof/CaseAnalysis/FinalWordsStage.lean`) is at most quadratic in the join
width, and the join width is quadratic in `ew + cc + 1`. -/
theorem wordsFuel_le (ew cc : ℕ) :
    CloseoutFinalC10WordsStage.wordsFuel ew cc ≤ 560000 * (ew + cc + 1) ^ 4 := by
  have hm : 1 ≤ ew + cc + 1 := by omega
  have hF1 : 1 ≤ (ew + cc + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hsq : (ew + cc + 1) ^ 2 ≤ (ew + cc + 1) ^ 4 :=
    Nat.pow_le_pow_right hm (by norm_num)
  have hlin : ew + cc + 1 ≤ (ew + cc + 1) ^ 4 := by
    refine le_trans ?_ hsq
    nlinarith
  have hJ : joinScalarWidth ew cc ≤ 3 * (ew + cc + 1) ^ 4 :=
    (joinScalarWidth_le ew cc).trans (Nat.mul_le_mul_left 3 hsq)
  have hJsq : (joinScalarWidth ew cc + 1) ^ 2 ≤ 16 * (ew + cc + 1) ^ 4 := by
    have h1 : joinScalarWidth ew cc + 1 ≤ 4 * (ew + cc + 1) ^ 2 := by
      have := joinScalarWidth_le ew cc
      nlinarith
    calc (joinScalarWidth ew cc + 1) ^ 2 ≤ (4 * (ew + cc + 1) ^ 2) ^ 2 :=
          Nat.pow_le_pow_left h1 2
      _ = 16 * (ew + cc + 1) ^ 4 := by ring
  have hA1 : CompetitorDimensions.budget ew ≤ 25000 * (ew + cc + 1) ^ 4 := by
    refine (dimensions_budget_le ew).trans (Nat.mul_le_mul_left 25000 ?_)
    exact le_trans (Nat.pow_le_pow_left (by omega : ew + 1 ≤ ew + cc + 1) 2) hsq
  have hA2 : CompetitorDimensions.budget (joinScalarWidth ew cc)
      ≤ 400000 * (ew + cc + 1) ^ 4 := by
    refine (dimensions_budget_le _).trans ?_
    calc 25000 * (joinScalarWidth ew cc + 1) ^ 2 ≤ 25000 * (16 * (ew + cc + 1) ^ 4) :=
          Nat.mul_le_mul_left 25000 hJsq
      _ = 400000 * (ew + cc + 1) ^ 4 := by ring
  have hA3 : CompetitorReusableDecision.capacity (joinScalarWidth ew cc)
      ≤ 65536 * (ew + cc + 1) ^ 4 := by
    unfold CompetitorReusableDecision.capacity
    calc 4096 * (joinScalarWidth ew cc + 1) ^ 2 ≤ 4096 * (16 * (ew + cc + 1) ^ 4) :=
          Nat.mul_le_mul_left 4096 hJsq
      _ = 65536 * (ew + cc + 1) ^ 4 := by ring
  have hA4 : ProjectionNormalization.Counter.budget cc
      ≤ 10 * (ew + cc + 1) ^ 4 + 13 := by
    unfold ProjectionNormalization.Counter.budget
    omega
  have hWq : CompetitorRationalDecision.width ew ≤ 2 * (ew + cc + 1) ^ 4 := by
    unfold CompetitorRationalDecision.width
    omega
  have hWJ : CompetitorRationalDecision.width (joinScalarWidth ew cc)
      ≤ 8 * (ew + cc + 1) ^ 4 := by
    unfold CompetitorRationalDecision.width
    omega
  have hP1 : (CompetitorRationalDecision.width ew + 1) * (2 * cc + 3)
      ≤ 9 * (ew + cc + 1) ^ 4 := by
    refine le_trans ?_ (Nat.mul_le_mul_left 9 hsq)
    unfold CompetitorRationalDecision.width
    nlinarith
  have hP2 : (CompetitorRationalDecision.width ew + 1) * cc
      + (CompetitorRationalDecision.width ew + 1) ≤ 3 * (ew + cc + 1) ^ 4 := by
    refine le_trans ?_ (Nat.mul_le_mul_left 3 hsq)
    unfold CompetitorRationalDecision.width
    nlinarith
  have ho : ([true] : List Bool).length = 1 := rfl
  have hp3 : ([true, true, false] : List Bool).length = 3 := rfl
  unfold CloseoutFinalC10WordsStage.wordsFuel
  omega

/-! ## Section 4  `hrest` -- the docked body and the tail against `A * (N+1)` -/

/-- **`dockedFuel` sees the input length ONLY through `emitFuel`.**  Every other
summand is a function of the record width and the call count alone
(`Proof/CaseAnalysis/FinalStageSeam.lean`).  This is the structural reason
`hrest`'s hard-coded exponent `a := 1` is a statement about the WIDTH SCHEDULE
and not about the dock. -/
theorem dockedFuel_eq (emitFuel : ℕ → ℕ) (ew cc n : ℕ) :
    dockedFuel emitFuel ew cc n
      = dockBudget ew cc + CompetitorCountRecordAppend.budget (joinScalarWidth ew cc)
        + emitFuel n + 2 := by
  unfold dockedFuel
  omega

/-- `CompetitorCountRecordAppend.budget` (`Proof/Hierarchy/CompetitorCountRecordAppend.lean`)
is `CompetitorDimensions.budget` plus a linear term. -/
theorem countRecordAppend_le (b : ℕ) :
    CompetitorCountRecordAppend.budget b ≤ 25120 * (b + 1) ^ 2 := by
  have h := dimensions_budget_le b
  unfold CompetitorCountRecordAppend.budget CompetitorCountRecordPrepare.budget
    CompetitorRationalDecision.width
  nlinarith

/-- **The dock's budget is quintic**: one `CompetitorMonomialStream.bodyBudget`
and one `CompetitorSumFold.bodyBudget` -- both quadratic in the join width -- per
emitted record. -/
theorem dockBudget_le (ew cc : ℕ) :
    dockBudget ew cc ≤ 68692 * (cc + 1) * (joinScalarWidth ew cc + 1) ^ 2 := by
  have hG : 1 ≤ (joinScalarWidth ew cc + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hJ : joinScalarWidth ew cc ≤ (joinScalarWidth ew cc + 1) ^ 2 := by nlinarith
  unfold dockBudget CompetitorMonomialEntry.readyBudget CompetitorMonomialEntry.budget
    CompetitorMonomialStream.loopBudget CompetitorMonomialStream.bodyBudget
    CompetitorSumEntry.budget CompetitorSumFold.loopBudget CompetitorSumFold.bodyBudget
    CompetitorReusableDecision.capacity
  nlinarith

/-- **`dockedFuel` is quintic in the record width plus the call count**, plus the
loader's own `emitFuel N`. -/
theorem dockedFuel_le (emitFuel : ℕ → ℕ) (ew cc n : ℕ) :
    dockedFuel emitFuel ew cc n ≤ 1600000 * (ew + cc + 1) ^ 5 + emitFuel n := by
  obtain ⟨F, hF⟩ : ∃ F, F = (ew + cc + 1) ^ 5 := ⟨_, rfl⟩
  have hm : 1 ≤ ew + cc + 1 := by omega
  have hF1 : 1 ≤ F := by rw [hF]; exact Nat.one_le_pow _ _ (by omega)
  have hcc4 : (cc + 1) * (ew + cc + 1) ^ 4 ≤ F := by
    rw [hF]
    calc (cc + 1) * (ew + cc + 1) ^ 4 ≤ (ew + cc + 1) * (ew + cc + 1) ^ 4 :=
          Nat.mul_le_mul_right _ (by omega)
      _ = (ew + cc + 1) ^ 5 := by ring
  have hJsq : (joinScalarWidth ew cc + 1) ^ 2 ≤ 16 * (ew + cc + 1) ^ 4 := by
    have h1 : joinScalarWidth ew cc + 1 ≤ 4 * (ew + cc + 1) ^ 2 := by
      have := joinScalarWidth_le ew cc
      nlinarith
    calc (joinScalarWidth ew cc + 1) ^ 2 ≤ (4 * (ew + cc + 1) ^ 2) ^ 2 :=
          Nat.pow_le_pow_left h1 2
      _ = 16 * (ew + cc + 1) ^ 4 := by ring
  have hdock : dockBudget ew cc ≤ 1099072 * F := by
    refine (dockBudget_le ew cc).trans ?_
    calc 68692 * (cc + 1) * (joinScalarWidth ew cc + 1) ^ 2
        ≤ 68692 * (cc + 1) * (16 * (ew + cc + 1) ^ 4) :=
          Nat.mul_le_mul_left _ hJsq
      _ = 1099072 * ((cc + 1) * (ew + cc + 1) ^ 4) := by ring
      _ ≤ 1099072 * F := Nat.mul_le_mul_left _ hcc4
  have happ : CompetitorCountRecordAppend.budget (joinScalarWidth ew cc) ≤ 401920 * F := by
    refine (countRecordAppend_le _).trans ?_
    have hle : (ew + cc + 1) ^ 4 ≤ F := by
      refine le_trans ?_ hcc4
      nlinarith
    calc 25120 * (joinScalarWidth ew cc + 1) ^ 2 ≤ 25120 * (16 * (ew + cc + 1) ^ 4) :=
          Nat.mul_le_mul_left _ hJsq
      _ = 401920 * (ew + cc + 1) ^ 4 := by ring
      _ ≤ 401920 * F := Nat.mul_le_mul_left _ hle
  rw [dockedFuel_eq, ← hF]
  omega

/-! ## Section 5  `hrest` at `a := 1`, from a polylogarithmic width schedule -/

/-! ## Section 6  The native width really is logarithmic in `N` -/

/-- **The native width is at most a constant times the bit length of the
hierarchy clock.**  `HierarchySourceCost.width_bound`
(`Proof/Hierarchy/HierarchySourceOutputBounds.lean`) at the route's own padding
`max H.coefficient (k+3)` (`Proof/Assembly/SelectedRecoveryIntegration.lean`), whose two
side conditions are the two `max` inequalities `outer` itself already supplies
(`Proof/Assembly/SelectedRecoveryIntegration.lean`). -/
theorem nativeWidth_le_time_bits (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n ^ (k + 2))) (N : ℕ) :
    (outer sources k clock).result.pcp.nativeWidth N
      ≤ ProjectionNormalization.HierarchySourceCost.widthCoefficient
            (fixedProjection sources)
            (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy
            (padding sources k clock)
          * (natBitLength
              ((sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy.time N) + 1) :=
  ProjectionNormalization.HierarchySourceCost.width_bound (fixedProjection sources)
    (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy (padding sources k clock)
    (Nat.le_max_left _ _) (Nat.le_max_right _ _) N

/-- **`nativeWidth N = O(log N)`, with explicit constants.**  The hierarchy clock
is `H.time N = H.coefficient * (N ^ (k+2) + 1)` (`Proof/Foundations/SourceCore.lean`), so its
bit length is `natBitLength H.coefficient + (k+2) * natBitLength N + 1`.  Together
with `nativeWidth_ge` (`Proof/CaseAnalysis/FinalLedgerAssembly.lean`), which gives
the matching lower bound `T <= nativeWidth N` whenever `2 ^ T <= N`, this pins
`nativeWidth N = Theta (log N)` -- so a schedule polynomial in the native width IS
polylogarithmic in `N`, which is exactly what
`hrest_of_logarithmic_schedule` consumes. -/
theorem nativeWidth_le_log (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n ^ (k + 2))) (N : ℕ) :
    (outer sources k clock).result.pcp.nativeWidth N
      ≤ ProjectionNormalization.HierarchySourceCost.widthCoefficient
            (fixedProjection sources)
            (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy
            (padding sources k clock)
          * (natBitLength (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy.coefficient
              + (k + 2) * natBitLength N + 2) := by
  refine (nativeWidth_le_time_bits sources k clock N).trans (Nat.mul_le_mul_left _ ?_)
  have hb : natBitLength ((sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy.time N)
      ≤ natBitLength (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy.coefficient
        + natBitLength (N ^ (k + 2) + 1) :=
    CloseoutNativeWidth.bits_mul_bound _ _ _ (le_of_eq rfl)
  have hp : natBitLength (N ^ (k + 2) + 1) ≤ (k + 2) * natBitLength N + 1 := by
    have h1 : N < 2 ^ natBitLength N := Nat.lt_pow_succ_log_self (by decide) N
    have h2 : N ^ (k + 2) < 2 ^ ((k + 2) * natBitLength N) := by
      calc N ^ (k + 2) < (2 ^ natBitLength N) ^ (k + 2) :=
            Nat.pow_lt_pow_left h1 (by omega)
        _ = 2 ^ (natBitLength N * (k + 2)) := by rw [← pow_mul]
        _ = 2 ^ ((k + 2) * natBitLength N) := by rw [Nat.mul_comm]
    have hpos : 1 ≤ 2 ^ ((k + 2) * natBitLength N) := Nat.one_le_pow _ _ (by norm_num)
    have hdouble : 2 ^ ((k + 2) * natBitLength N) + 2 ^ ((k + 2) * natBitLength N)
        = 2 ^ ((k + 2) * natBitLength N + 1) := by rw [pow_succ]; ring
    have h3 : N ^ (k + 2) + 1 < 2 ^ ((k + 2) * natBitLength N + 1) := by omega
    have h4 : Nat.log 2 (N ^ (k + 2) + 1) < (k + 2) * natBitLength N + 1 :=
      Nat.log_lt_of_lt_pow (by omega) h3
    change Nat.log 2 (N ^ (k + 2) + 1) + 1 ≤ (k + 2) * natBitLength N + 1
    omega
  omega

/-- `natBitLength n = Nat.log 2 n + 1` is below `logScale n = Nat.clog 2 (n + 2)`
(`Proof/Foundations/Semantics.lean`). -/
theorem natBitLength_le_logScale (N : ℕ) : natBitLength N ≤ logScale N := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    unfold natBitLength logScale
    norm_num
  · have hle : N + 2 ≤ 2 ^ Nat.clog 2 (N + 2) := Nat.le_pow_clog (by norm_num) _
    have hlt : N < 2 ^ Nat.clog 2 (N + 2) := by omega
    have h := Nat.log_lt_of_lt_pow (by omega : N ≠ 0) hlt
    change Nat.log 2 N + 1 ≤ Nat.clog 2 (N + 2)
    omega

/-- **The bridge from Section 6 to Section 5**: `nativeWidth N + 1` is at most a
CONSTANT times `logScale N`.  A schedule polynomial in `nativeWidth N + 1` is
therefore polynomial in `logScale N`, which is exactly the hypothesis
`hrest_of_logarithmic_schedule` consumes -- so `hrest` at `a := 1` is reachable
from a width-indexed schedule and needs no re-parameterisation of
`ledger_of_parts`. -/
theorem nativeWidth_succ_le_logScale (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n ^ (k + 2))) (N : ℕ) :
    (outer sources k clock).result.pcp.nativeWidth N + 1
      ≤ (ProjectionNormalization.HierarchySourceCost.widthCoefficient
            (fixedProjection sources)
            (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy
            (padding sources k clock)
          * (natBitLength (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy.coefficient
              + k + 4) + 1) * logScale N := by
  have hL : 1 ≤ logScale N := by
    unfold logScale
    exact Nat.clog_pos (by norm_num) (by omega)
  have hb := natBitLength_le_logScale N
  have h := nativeWidth_le_log sources k clock N
  have hstep :
      natBitLength (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy.coefficient
          + (k + 2) * natBitLength N + 2
        ≤ (natBitLength (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy.coefficient
            + k + 4) * logScale N := by
    have e1 : (natBitLength (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy.coefficient
          + k + 4) * logScale N
        = natBitLength (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy.coefficient
            * logScale N + (k + 2) * logScale N + 2 * logScale N := by ring
    have e2 : natBitLength (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy.coefficient
        * 1 ≤ natBitLength (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy.coefficient
          * logScale N := Nat.mul_le_mul_left _ hL
    have e3 : (k + 2) * natBitLength N ≤ (k + 2) * logScale N := Nat.mul_le_mul_left _ hb
    omega
  calc (outer sources k clock).result.pcp.nativeWidth N + 1
      ≤ ProjectionNormalization.HierarchySourceCost.widthCoefficient (fixedProjection sources)
            (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy (padding sources k clock)
          * (natBitLength (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy.coefficient
              + (k + 2) * natBitLength N + 2) + 1 := by omega
    _ ≤ ProjectionNormalization.HierarchySourceCost.widthCoefficient (fixedProjection sources)
            (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy (padding sources k clock)
          * ((natBitLength
                (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy.coefficient
              + k + 4) * logScale N) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hstep) 1
    _ ≤ ProjectionNormalization.HierarchySourceCost.widthCoefficient (fixedProjection sources)
            (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy (padding sources k clock)
          * ((natBitLength
                (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy.coefficient
              + k + 4) * logScale N) + logScale N := by omega
    _ = (ProjectionNormalization.HierarchySourceCost.widthCoefficient (fixedProjection sources)
            (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy (padding sources k clock)
          * (natBitLength
                (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy.coefficient
              + k + 4) + 1) * logScale N := by ring

end
end NearCubicWires.RepairSource.CloseoutFinal.C10LedgerBounds
