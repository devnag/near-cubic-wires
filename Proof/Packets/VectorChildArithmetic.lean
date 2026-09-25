import Proof.Packets.VectorAccumulator

/-! The closed arithmetic body of one bottom-up right contribution:
left packet times right packet, followed by accumulator plus that term.
The resulting accumulator is physically saved on ports34/35. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorChildArithmetic
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def term (left right : List (List Bool)) := NormalizerOrder.ordered (MaskProduct.unions left right)
def multiply := TapeEmbedding.machine 2 (ReusableArithmetic.machine NormalizedMultiply.machine)
def machine := Composition.machine multiply VectorAccumulator.machine
def budget (B R : Nat) (left right acc : List (List Bool)) :=
  ReusableArithmetic.budget (NormalizedMultiply.budget B left right) R+1+
    VectorAccumulator.budget B R acc (term left right)

theorem left_fits (B R : Nat) (left right : List (List Bool))
    (ha : ∀ i,(ReusableArithmetic.data B left right i).length≤R) : VectorAccumulator.Fits R left := by
  constructor
  · exact ha 25
  · have h:=ha 28
    change (CompareMachine.word left.length).length≤R at h
    simpa [CompareMachine.word] using h

theorem term_width (B : Nat) (left right : List (List Bool))
    (hd : ∀ bits∈left,bits.length=B) (hc : ∀ bits∈right,bits.length=B) :
    ∀ bits∈term left right,bits.length=B := by
  intro bits hb
  change bits∈(MaskProduct.unions left right).dedup.reverse.filter _ at hb
  have hm : bits∈MaskProduct.unions left right := by
    simpa only [List.mem_reverse,List.mem_dedup] using (List.mem_filter.mp hb).1
  exact NormalizedMultiply.unions_width B left right hd hc bits hm

theorem run (B R : Nat) (left right acc : List (List Bool))
    (hd : ∀ bits∈left,bits.length=B) (hc : ∀ bits∈right,bits.length=B)
    (ha : ∀ bits∈acc,bits.length=B)
    (hmd : ∀ i,(ReusableArithmetic.data B left right i).length≤R)
    (hmc : NormalizedMultiply.budget B left right+3≤R)
    (had : ∀ i,(ReusableArithmetic.data B acc (term left right) i).length≤R)
    (hac : NormalizedAddition.budget B acc (term left right)+3≤R) :
    Step machine (budget B R left right acc) VectorAccumulator.heads
      (VectorAccumulator.tapes B R left right acc) VectorAccumulator.heads
      (VectorAccumulator.tapes B R (VectorAccumulator.answer acc (term left right))
        (term left right) (VectorAccumulator.answer acc (term left right))) := by
  have first:=(ReusableArithmetic.mul_run B R left right hd hc hmd hmc).embed
    (fun _ : Fin 2=>0)
    (![ZeroPadding.pad R acc.flatten,ZeroPadding.pad R (CompareMachine.word acc.length)] : Fin 2→List Bool)
  have second:=VectorAccumulator.run B R left (term left right) acc
    (left_fits B R left right hmd) (left_fits B R acc (term left right) had)
    ha (term_width B left right hd hc) had hac
  exact first.seq second

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorChildArithmetic
