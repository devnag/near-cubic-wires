import Proof.Packets.VectorAccumulatorCopies

/-! Exact forward-child accumulator transaction. Load the stored accumulator,
add the current right operand, then physically store the new accumulator. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorAccumulator
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def add := TapeEmbedding.machine 2 (ReusableArithmetic.machineLeft NormalizedAddition.machine)
def machine := Composition.machine load (Composition.machine add save)
def budget (B R : Nat) (stored term : List (List Bool)) :=
  copyBudget R+1+(ReusableArithmetic.budget (NormalizedAddition.budget B stored term) R+1+copyBudget R)
def answer (stored term : List (List Bool)) := NormalizerOrder.ordered (stored.reverse++term)

theorem answer_fits (B R : Nat) (stored term : List (List Bool))
    (hs : ∀ bits∈stored,bits.length=B) (ht : ∀ bits∈term,bits.length=B)
    (ha : ∀ i,(ReusableArithmetic.data B stored term i).length≤R)
    (hcap : NormalizedAddition.budget B stored term+3≤R) : Fits R (answer stored term) := by
  obtain ⟨r,h,hr,h20,_,h21,_,_,_,_,_,_,_⟩:=NormalizedAddition.run_both B stored term hs ht
  have he : NormalizedAddition.heads=ReusableArithmetic.localHeads := by funext i;fin_cases i <;>rfl
  have hd : NormalizedAddition.data B stored term []=ReusableArithmetic.data B stored term := by
    funext i;fin_cases i <;>rfl
  have hp : Step NormalizedAddition.machine (NormalizedAddition.budget B stored term)
      ReusableArithmetic.localHeads (ReusableArithmetic.data B stored term)
      r.final.heads r.final.tapes := by
    refine ⟨r,?_,rfl,rfl,hr⟩
    simpa only [NormalizedAddition.entry,Normalize.started,he,hd] using h
  have fit:=ReusableArithmetic.output_fits hp ha hcap
  constructor
  · have hfit:=fit 20
    simp only [ReusableArithmetic.padded,h20,ZeroPadding.pad_length] at hfit
    exact (le_max_right R (answer stored term).flatten.length).trans_eq hfit
  · have hfit:=fit 21
    simp only [ReusableArithmetic.padded,h21,ZeroPadding.pad_length,CompareMachine.word,
      List.length_cons,List.length_replicate] at hfit
    exact (le_max_right R ((answer stored term).length+1)).trans_eq hfit

theorem run (B R : Nat) (oldLeft term stored : List (List Bool))
    (hl : Fits R oldLeft) (hsfit : Fits R stored)
    (hs : ∀ bits∈stored,bits.length=B) (ht : ∀ bits∈term,bits.length=B)
    (ha : ∀ i,(ReusableArithmetic.data B stored term i).length≤R)
    (hcap : NormalizedAddition.budget B stored term+3≤R) :
    Step machine (budget B R stored term) heads (tapes B R oldLeft term stored)
      heads (tapes B R (answer stored term) term (answer stored term)) := by
  have first:=load_run B R oldLeft term stored hl hsfit
  have second:=(ReusableArithmetic.add_run_left B R stored term hs ht ha hcap).embed
    (fun _ : Fin 2=>0)
    (![ZeroPadding.pad R stored.flatten,ZeroPadding.pad R (CompareMachine.word stored.length)] : Fin 2→List Bool)
  have third:=save_run B R (answer stored term) term stored (answer_fits B R stored term hs ht ha hcap) hsfit
  exact first.seq (second.seq third)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorAccumulator
