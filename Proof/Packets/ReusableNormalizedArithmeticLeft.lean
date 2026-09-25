import Proof.Packets.ReusableNormalizedArithmetic
import Proof.Packets.ReusableArithmeticLeft
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ReusableArithmetic
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.ProjectionNormalization

theorem result_left_eq_state (B R : Nat) (right answer : List (List Bool)) (b : Fin 30 → List Bool)
    (hR : 1≤R)
    (h13 : b 13=UnaryTemplate.tape (2*B+3)) (h24 : b 24=UnaryTemplate.tape B)
    (h26 : b 26=right.flatten) (h27 : b 27=CompareMachine.word right.length)
    (h20 : b 20=answer.flatten) (h21 : b 21=CompareMachine.word answer.length) :
    resultLeft R (padded R b)=padded R (data B answer right) := by
  have hz : ZeroPadding.pad R [false]=List.replicate R false := by
    change List.replicate 1 false++List.replicate (R-1) false=List.replicate R false
    rw [←List.replicate_add,show 1+(R-1)=R by omega]
  funext i
  fin_cases i <;> simp [resultLeft,cleared,replaced,keep,padded,data,NormalizedMultiply.data,
    NormalizedMultiply.extras,NormalizeCold.data,Fin.addCases,Normalize.records,
    SuffixScan.stream,CompareMachine.word,Function.update,h13,h24,h26,h27,h20,h21,
    hz,show ZeroPadding.pad R []=List.replicate R false from by simp [ZeroPadding.pad]]

theorem add_run_left (B R : Nat) (left right : List (List Bool))
    (hl : ∀ bits∈left,bits.length=B) (hr : ∀ bits∈right,bits.length=B)
    (ha : ∀ i,(data B left right i).length≤R)
    (hcap : NormalizedAddition.budget B left right+3≤R) :
    Step (machineLeft NormalizedAddition.machine) (budget (NormalizedAddition.budget B left right) R)
      heads (state B R left right) heads
      (state B R (NormalizerOrder.ordered (left.reverse++right)) right) := by
  obtain ⟨r,h,hs,h20,_,h21,_,h13,h24,_,_,h26,h27⟩ := NormalizedAddition.run_both B left right hl hr
  have he : NormalizedAddition.heads=localHeads := by funext i;fin_cases i <;>rfl
  have hd : NormalizedAddition.data B left right []=data B left right := by
    funext i;fin_cases i <;>rfl
  have hp : Step NormalizedAddition.machine (NormalizedAddition.budget B left right)
      localHeads (data B left right) r.final.heads r.final.tapes := by
    refine ⟨r,?_,rfl,rfl,hs⟩
    simpa only [NormalizedAddition.entry,Normalize.started,he,hd] using h
  have whole := run_left hp ha hcap
  exact whole.congr rfl (congrArg (bank R) (result_left_eq_state B R right _ r.final.tapes
    (by omega) h13 h24 h26 h27 h20 h21))

end PCJ9eff70d512234a4c_Fixed.Materializer.ReusableArithmetic
