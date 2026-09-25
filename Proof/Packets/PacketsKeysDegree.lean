import Proof.Packets.PacketsKeysDegreeSpec
import Proof.Packets.PacketsWalk
import Proof.Packets.PacketsSetupWords

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsKeys.Degree
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch

namespace PredM

/-- States: 0 skip the first cell, 1 copy, 2 halt. -/
def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q b =>
    if q.val = 0 then
      if b 0 then some ⟨1, fun _ => none, fun i => if i.val = 0 then .right else .stay⟩
      else some ⟨2, fun _ => none, fun _ => .stay⟩
    else if q.val = 1 then
      if b 0 then some ⟨1, fun i => if i.val = 1 then some true else none, fun _ => .right⟩
      else some ⟨2, fun _ => none, fun _ => .stay⟩
    else none

def cfg (x : ℕ) (q : Fin 3) (i o : ℕ) : Configuration 2 3 :=
  ⟨q, ![i, o], ![List.replicate x true, List.replicate o true]⟩

theorem step0 (x : ℕ) (hx : 0 < x) : step machine (cfg x 0 0 0) = some (cfg x 1 1 0) := by
  have hr : readTapeBit (List.replicate x true) 0 = true := by simp [readTapeBit, List.getD, hx]
  simp only [step, machine, cfg, Configuration.scanned]
  simp [hr]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem step1 (x i o : ℕ) (hi : i < x) : step machine (cfg x 1 i o) = some (cfg x 1 (i + 1) (o + 1)) := by
  have hr : readTapeBit (List.replicate x true) i = true := by simp [readTapeBit, List.getD, hi]
  simp only [step, machine, cfg, Configuration.scanned]
  simp [hr]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem stop0 : step machine (cfg 0 0 0 0) = some (cfg 0 2 0 0) := by
  simp only [step, machine, cfg, Configuration.scanned]
  simp [readTapeBit]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem stop1 (x o : ℕ) : step machine (cfg x 1 x o) = some (cfg x 2 x o) := by
  have hr : readTapeBit (List.replicate x true) x = false := by simp [readTapeBit, List.getD]
  simp only [step, machine, cfg, Configuration.scanned]
  simp [hr]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem loop (x m i o : ℕ) (h : i + m = x) : Timed machine (m + 1) (cfg x 1 i o) (cfg x 2 x (o + m)) := by
  induction m generalizing i o with
  | zero =>
    have hi : i = x := by omega
    subst hi
    exact Timed.single (by rfl) (stop1 i o)
  | succ m ih =>
    have h2 := ih (i + 1) (o + 1) (by omega)
    have e3 : o + 1 + m = o + (m + 1) := by ring
    rw [e3] at h2
    have e : m + 1 + 1 = 1 + (m + 1) := by ring
    rw [e]
    exact (Timed.single (by rfl) (step1 x i o (by omega))).trans h2

theorem timed (x : ℕ) : Timed machine (x + 1) (cfg x 0 0 0) (cfg x 2 x (x - 1)) := by
  cases x with
  | zero => exact Timed.single (by rfl) stop0
  | succ k =>
    have h := (Timed.single (p := machine) (by rfl) (step0 (k + 1) (by omega))).trans (loop (k + 1) k 1 0 (by omega))
    have e : 1 + (k + 1) = k + 1 + 1 := by ring
    rw [e, Nat.zero_add] at h
    exact h

theorem run (x : ℕ) :
    Step machine (x + 1) (fun _ => 0) ![List.replicate x true, []] ![x, x - 1]
      ![List.replicate x true, List.replicate (x - 1) true] := by
  obtain ⟨r, hr, hf, _⟩ := (timed x).run (by rfl)
  have hc : cfg x 0 0 0 = (⟨machine.start, fun _ => 0, ![List.replicate x true, []]⟩ : Configuration 2 3) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hc] at hr
  exact Step.of_run hr (by rw [hf]; rfl) (by rw [hf]; rfl)

end PredM

open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrime NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketsGlue NearCubicWires.PacketsGlue.RequestMeta
noncomputable section

def predMap : UnaryMap (fun x => x - 1) where
  extra := 1
  states := 3 + 2
  machine := MaskedReset.machine PredM.machine (fun _ => true)
  cost := fun x => 2 * (x + 1) + 2
  run := by
    intro x
    obtain ⟨k, hm⟩ := step_mask0 (PredM.run x) (fun _ => true) (by intro i _; rfl)
    refine ⟨_, _, hm.congr_in ?_ ?_, ?_, ?_⟩
    · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
    · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Fin.addCases_left]; fin_cases j <;> rfl
      · simp [unIn]
    · rfl
    · rfl

theorem pred_cost (x : ℕ) : predMap.cost x ≤ 4 * (x + 3) ^ 1 := by
  change 2 * (x + 1) + 2 ≤ _
  rw [pow_one]; omega

theorem isZero_cost (x : ℕ) : isZeroMap.cost x ≤ 4 * (x + 3) ^ 0 := by
  change 2 * 1 + 2 ≤ _
  simp

/-! ## The stages -/

section Stages
variable (a : DecompositionAlgorithm)

/-- `[thrFlag = 0] · #circuits` (the SYM factor; `0` on THR and on the terminal sentinel). -/
def symS : UnaryStage a (fun r => isZ (thrFlag r) * Native.nCirc r) :=
  ((thrFlagStage a).thenMapP isZeroMap 4 0 isZero_cost).pairP (Native.circuitsStage a) mulMap2 8 2 mul_cost

variable (cutS : UnaryStage a (cutoffOf a)) (thrSel : UnaryStage a (RowsInit.Count.thrSelOf a))

/-- The largest prime `≤ cutoff`: `primeAt cutoff (π(cutoff) - 1)`. -/
def pmaxS : UnaryStage a (pmaxOf a) :=
  cutS.pairP ((primeCountStage a cutS).thenMapP predMap 4 1 pred_cost) primeOfIndexMap 14 3 primeIdx_cost

/-- Its digit count `clog₂ (pmax + 1) = modulusDigitCount pmax`. -/
def digS : UnaryStage a (fun r => Nat.clog 2 (pmaxOf a r + 1)) :=
  ((pmaxS a cutS).thenMapP (plusMap 1) (2 * 1 + 4) 1 (plus_cost 1)).thenMapP clogMap 62 1 clog_cost

/-- `[|Sel| ≠ 0]`. -/
def selS : UnaryStage a (fun r => isZ (isZ (RowsInit.Count.thrSelOf a r))) :=
  (thrSel.thenMapP isZeroMap 4 0 isZero_cost).thenMapP isZeroMap 4 0 isZero_cost

/-- The THR factor `thrFlag · ([|Sel| ≠ 0] · digits(pmax))`. -/
def thrS : UnaryStage a (fun r => thrFlag r * (isZ (isZ (RowsInit.Count.thrSelOf a r)) * Nat.clog 2 (pmaxOf a r + 1))) :=
  (thrFlagStage a).pairP ((selS a thrSel).pairP (digS a cutS) mulMap2 8 2 mul_cost) mulMap2 8 2 mul_cost

/-- The per-kind factor `facOf`. -/
def facS : UnaryStage a (facOf a) :=
  (symS a).pairP (thrS a cutS thrSel) addMap2 6 1 add_cost

/-- The coordinate degree `walkLength · (windowSum · 2)`. -/
def coordS : UnaryStage a (fun r => walkLength a r * (windowSum a r * 2)) :=
  (walkStage a cutS thrSel).pairP ((windowSumStage a).thenMapP (scaleMap 2) (4 * 2 + 12) 2 (scale_cost 2))
    mulMap2 8 2 mul_cost

/-- **`degS : UnaryStage a (degree a)`** — ONE fixed machine for the request degree (`Request.degree`). -/
def degStage : UnaryStage a (degree a) :=
  ((facS a cutS thrSel).pairP (coordS a cutS thrSel) mulMap2 8 2 mul_cost).ofEq (fun r => (degree_eq a r).symm)

end Stages

end
end NearCubicWires.PacketsKeys.Degree

