import Proof.Packets.ArithmeticPacketLookup

/-! One executed substitution product: fetch the actual atom from the resident
packet table, then multiply it on the left of the running product. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionAtom
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

noncomputable def multiply := TapeEmbedding.machine 3
  (ReusableArithmetic.machine NormalizedMultiply.machine)
noncomputable def machine := Composition.machine ArithmeticLookup.machine multiply
def budget (B R index : Nat) (atom accumulator : List (List Bool)) :=
  ArithmeticLookup.budget R index+1+ReusableArithmetic.budget (NormalizedMultiply.budget B atom accumulator) R

theorem multiply_run (B R index : Nat) (atom accumulator : List (List Bool)) (source : List Bool)
    (hAtom : ∀ bits∈atom,bits.length=B) (hAcc : ∀ bits∈accumulator,bits.length=B)
    (ha : ∀ i,(ReusableArithmetic.data B atom accumulator i).length≤R)
    (hcap : NormalizedMultiply.budget B atom accumulator+3≤R) :
    Step multiply (ReusableArithmetic.budget (NormalizedMultiply.budget B atom accumulator) R)
      (ArithmeticLookup.H 0) (ArithmeticLookup.A B R index atom accumulator source)
      (ArithmeticLookup.H 0)
      (ArithmeticLookup.A B R index atom (NormalizerOrder.ordered (MaskProduct.unions atom accumulator)) source) := by
  have h := (ReusableArithmetic.mul_run B R atom accumulator hAtom hAcc ha hcap).embed
    (![0,1,0] : Fin 3→Nat)
    (![source,ZeroPadding.pad R (CompareMachine.word index),List.replicate R false] : Fin 3→List Bool)
  have hh : Fin.addCases (m:=34) (n:=3) (motive:=fun _=>Nat) ReusableArithmetic.heads
      (![0,1,0] : Fin 3→Nat)=ArithmeticLookup.H 0 := by funext i;fin_cases i <;>rfl
  exact (h.congr_in hh rfl).congr hh rfl

theorem run (B R index : Nat) (left atom accumulator : List (List Bool)) (pre post : List Bool)
    (hpre : pre.length=2*index*R)
    (hleft : left.flatten.length≤R) (hleftCount : left.length+1≤R)
    (hatom : atom.flatten.length≤R) (hatomCount : atom.length+1≤R)
    (hAtom : ∀ bits∈atom,bits.length=B) (hAcc : ∀ bits∈accumulator,bits.length=B)
    (ha : ∀ i,(ReusableArithmetic.data B atom accumulator i).length≤R)
    (hcap : NormalizedMultiply.budget B atom accumulator+3≤R) :
    let source := pre++ZeroPadding.pad R atom.flatten++
      ZeroPadding.pad R (CompareMachine.word atom.length)++post
    Step machine (budget B R index atom accumulator)
      (ArithmeticLookup.H 0) (ArithmeticLookup.A B R index left accumulator source)
      (ArithmeticLookup.H 0)
      (ArithmeticLookup.A B R index atom (NormalizerOrder.ordered (MaskProduct.unions atom accumulator)) source) := by
  have fetch := ArithmeticLookup.run B R index left accumulator atom pre post
    hpre hleft hleftCount hatom hatomCount
  exact fetch.seq (multiply_run B R index atom accumulator _ hAtom hAcc ha hcap)

/-- A coarse quadratic bound is useful while looping over descending literal
codes; the reserve itself is produced by an ordinary machine. -/
theorem budget_bound (B R index : Nat) (atom accumulator : List (List Bool))
    (hi : index≤R) (hcap : NormalizedMultiply.budget B atom accumulator≤R) :
    budget B R index atom accumulator≤64*(R+1)^2 := by
  unfold budget ArithmeticLookup.budget PacketBank.lookupBudget ReusableArithmetic.budget
  have hmul : index*R≤R*R := Nat.mul_le_mul_right R hi
  nlinarith

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionAtom
