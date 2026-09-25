import Proof.Rows.ClosureOffsetSourceGateReusable

/-! Pin the executed native gate comparison to the paper's frozen C_i and
the count table's actual row/column convention. No alternative split is used. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.OffsetSourceGate
open RepairOrdinary RepairRepresentation RepairSource.CloseoutFinal SupplierPipeline SupplierEstimator
open RepairSource.CloseoutRowsUniversal CloseoutRowsPoolWeight
open scoped BigOperators

def items {q : Nat} (g : NormalizedThresholdGate q) (x : BitInput q) : List Item :=
  List.ofFn (fun i=>(g.weight i,x i))

theorem items_word {q : Nat} (g : NormalizedThresholdGate q) (x : BitInput q) :
    word (items g x)=(List.ofFn g.weight).flatMap intWord := by
  change (List.ofFn (fun i=>(g.weight i,x i))).flatMap (fun v=>intWord v.1)=_
  rw [←List.flatMap_map,List.map_ofFn]
  rfl

theorem items_mask {q : Nat} (g : NormalizedThresholdGate q) (x : BitInput q) :
    mask (items g x)=List.ofFn x := by
  simp [mask,items,List.map_ofFn,Function.comp_def]

theorem items_signed {q : Nat} (g : NormalizedThresholdGate q) (x : BitInput q) :
    C10NaturalHardwireScore.signedSum (items g x)=
      ∑ i,g.weight i*(if x i then 1 else 0) := by
  simp only [C10NaturalHardwireScore.signedSum,items,List.map_ofFn,List.sum_ofFn]
  change (∑ i,if x i then g.weight i else 0)=_
  apply Finset.sum_congr rfl
  intro i _
  cases x i <;>simp

theorem bit_eval {q : Nat} (g : NormalizedThresholdGate q) (x : BitInput q) :
    bit (items g x) (g.threshold-1)=g.eval x := by
  rw [bit,C10NaturalHardwireScore.selected_difference,items_signed]
  unfold NormalizedThresholdGate.eval
  apply decide_eq_decide.mpr
  omega

end NearCubicWires.P1Closure.OffsetSourceGate
