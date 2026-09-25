import Proof.Rows.CellGate
import Proof.Rows.MinimumAssignment

/-! Generalize the inspected HardwireBounds arithmetic to any actual full mask.
No evaluator machine changes; the emitted minimizing assignment is an instance. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 550000
namespace PCJ45bee56da9f34d5a_FullGateBounds
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.P1Closure NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open C10NaturalHardwireScore (positiveSum selectedSum)
open CloseoutRowsPoolMinimum (negSum liveSum)
open C10NaturalHardwireTarget (pPart nPart)
open OffsetSourceGate (items)
open scoped BigOperators
noncomputable section
private theorem part_le (z : Int) : z.toNat ≤ z.natAbs := by
  cases z <;> simp

private theorem negative_part_le (z : Int) : (-z).toNat ≤ z.natAbs := by
  simpa only [Int.natAbs_neg] using part_le (-z)

theorem score_bounds {q : Nat} (g : NormalizedThresholdGate q)
    (x : BitInput q) :
    positiveSum (items g x) ≤ ∑ i, (g.weight i).natAbs ∧
    negSum (items g x) ≤ ∑ i, (g.weight i).natAbs ∧
    selectedSum (items g x) ≤ ∑ i, (g.weight i).natAbs ∧
    liveSum (items g x) ≤ ∑ i, (g.weight i).natAbs := by
  simp only [positiveSum,negSum,selectedSum,liveSum,items,List.map_ofFn,List.sum_ofFn,
    Function.comp_apply]
  refine ⟨?_,?_,?_,?_⟩
  · exact Finset.sum_le_sum (fun i _ => part_le (g.weight i))
  · exact Finset.sum_le_sum (fun i _ => negative_part_le (g.weight i))
  · apply Finset.sum_le_sum
    intro i _
    split
    · exact part_le (g.weight i)
    · exact Nat.zero_le _
  · apply Finset.sum_le_sum
    intro i _
    split
    · exact negative_part_le (g.weight i)
    · exact Nat.zero_le _

theorem of_magnitude {q : Nat} (g : NormalizedThresholdGate q)
    (x : BitInput q) (w : Nat) (hw : 0 < w)
    (hm : (g.threshold-1).natAbs + (∑ i, (g.weight i).natAbs) < 2^w) :
    (∀ item ∈ items g x, natBitLength item.1.natAbs ≤ w) ∧
    positiveSum (items g x) < 2^w ∧
    negSum (items g x) < 2^w ∧
    natBitLength (g.threshold-1).natAbs ≤ w ∧
    pPart (g.threshold-1) (liveSum (items g x)) < 2^w ∧
    nPart (g.threshold-1) (selectedSum (items g x)) < 2^w := by
  obtain ⟨hp,hn,hsp,hsn⟩ := score_bounds g x
  have ht : natBitLength (g.threshold-1).natAbs ≤ w :=
    CompactCacheCost.bit_bound (g.threshold-1) w hw (by omega)
  refine ⟨?_,by omega,by omega,ht,?_,?_⟩
  · intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    have hi := Finset.single_le_sum (fun j _ => Nat.zero_le (g.weight j).natAbs)
      (Finset.mem_univ i)
    exact CompactCacheCost.bit_bound (g.weight i) w hw (by omega)
  · unfold pPart
    have := part_le (g.threshold-1)
    omega
  · unfold nPart
    have := negative_part_le (g.threshold-1)
    omega


theorem score_loop {q : Nat} (g : NormalizedThresholdGate q) (x : BitInput q) (w : Nat) :
    C10NaturalHardwireScore.loopBudget (items g x) w (HardwireBudget.C w)=HardwireBudget.D q w := by
  simp only [C10NaturalHardwireScore.loopBudget,items,List.length_ofFn,
    CloseoutRowsPoolMinimum.uniformBudget,HardwireBudget.D]

theorem negative_loop {q : Nat} (g : NormalizedThresholdGate q) (x : BitInput q) (w : Nat) :
    CloseoutRowsPoolMinimum.loopBudget (items g x) w (HardwireBudget.C w)=HardwireBudget.D q w := by
  simp only [CloseoutRowsPoolMinimum.loopBudget,items,List.length_ofFn,
    CloseoutRowsPoolMinimum.uniformBudget,HardwireBudget.D]

theorem worker_bound {q : Nat} (g : NormalizedThresholdGate q) (x : BitInput q) (w : Nat)
    (hw : 0 < w) (hm : (g.threshold-1).natAbs+(∑i,(g.weight i).natAbs) < 2^w) :
    OffsetSourceGate.budget (items g x) (g.threshold-1) w (HardwireBudget.C w) ≤ 132*q*w+222*q+44*w+88 := by
  have hz:=CompactCacheCost.bit_bound (g.threshold-1) w hw (by omega)
  change natBitLength (g.threshold-1).natAbs ≤ w at hz
  simp only [OffsetSourceGate.budget,C10NaturalHardwireScoreInputs.budget]
  rw [score_loop,negative_loop]
  unfold C10NaturalHardwireTarget.pairBudget CloseoutRowsPoolMagnitude.budget RowPowerNativeReset.rawTime
  unfold HardwireBudget.D HardwireBudget.C
  nlinarith

def source {q : Nat} (g : NormalizedThresholdGate q) :=
  (List.ofFn g.weight).flatMap intWord++intWord (g.threshold-1)
def reserve {q : Nat} (g : NormalizedThresholdGate q) (x : BitInput q) (w : Nat) :=
  OffsetSourceGate.capacity (items g x) (g.threshold-1) [] [] w (HardwireBudget.C w) (HardwireBudget.D q w)

theorem reserve_bound {q : Nat} (g : NormalizedThresholdGate q) (x : BitInput q) (B w : Nat)
    (hw : 0 < w) (hb : (source g).length ≤ B)
    (hm : (g.threshold-1).natAbs+(∑i,(g.weight i).natAbs) < 2^w) :
    reserve g x w ≤ 1024*(B+q+w+1)^2 := by
  have hr:=worker_bound g x w hw hm
  unfold HardwireBudget.C at hr
  have he : (items g x).length=q := List.length_ofFn
  have hs : (CloseoutRowsPoolWeight.word (items g x)++intWord (g.threshold-1)++[]).length ≤ B := by
    simpa only [OffsetSourceGate.items_word,List.append_nil,source] using hb
  have hmask : (CloseoutRowsPoolWeight.mask (items g x)++[]).length=q := by
    simp [OffsetSourceGate.items_mask]
  unfold reserve OffsetSourceGate.capacity
  rw [hmask,he]
  unfold HardwireBudget.D HardwireBudget.C
  nlinarith
end
end PCJ45bee56da9f34d5a_FullGateBounds
