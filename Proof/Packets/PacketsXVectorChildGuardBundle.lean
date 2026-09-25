import Proof.Packets.PacketsXCycleBoundedArithmetic
import Proof.Packets.PacketsXSubstitutionSemanticGuard
import Proof.Packets.PacketsXVectorParentPrefix

/-! Uniform semantic discharge of all guards in the actual child loop.
The fixed support may be the original literal-code set; no substitution or
change of normalized list order is used. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorChildGuardBundle
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport Theorem25Completion.CycleBounds SubstitutionCensus
abbrev Poly:=Ring.Poly Nat
def masks (C : Nat) (P : Poly):=P.map (maskNat C)

structure Guards (C R : Nat) (ps : List Poly) (delta : Nat→Poly) : Prop where
  packet : ∀P∈ps,VectorAccumulator.Fits R (masks C P)
  code : ∀P∈ps,Fits C P
  deltaCode : ∀i,i<ps.length→Fits C (delta i)
  prefixFits : ∀i,i≤ps.length→VectorAccumulator.Fits R (masks C (VectorParentPrefix.value ps delta i))
  term : ∀i : Fin ps.length,VectorAccumulator.Fits R (masks C (Ring.mul ps[i.val] (delta i.val)))
  mulData : ∀i : Fin ps.length,∀j,(ReusableArithmetic.data C (masks C ps[i.val]) (masks C (delta i.val)) j).length≤R
  mulFuel : ∀i : Fin ps.length,NormalizedMultiply.budget C (masks C ps[i.val]) (masks C (delta i.val))+3≤R
  addData : ∀i : Fin ps.length,∀j,(ReusableArithmetic.data C
    (masks C (VectorParentPrefix.value ps delta i.val)) (masks C (Ring.mul ps[i.val] (delta i.val))) j).length≤R
  addFuel : ∀i : Fin ps.length,NormalizedAddition.budget C
    (masks C (VectorParentPrefix.value ps delta i.val)) (masks C (Ring.mul ps[i.val] (delta i.val)))+3≤R

theorem guards (C w d a b : Nat) (S : Finset Nat) (ps : List Poly) (delta : Nat→Poly)
    (hS : ∀j∈S,j<C) (hps : ∀P∈ps,Bounded S a P)
    (hd : ∀i,i<ps.length→Bounded S b (delta i)) (hab : a+b≤d)
    (hfit : (S.card+1)^d≤2^w) (hw : 1≤w) :
    Guards C (commonReserve C w) ps delta := by
  have hc : ∀P∈ps,Bounded S d P:=fun P hP=>NormalizedIntermediate.mono (hps P hP) (by omega)
  have hdelta : ∀i,i<ps.length→Bounded S d (delta i):=
    fun i hi=>NormalizedIntermediate.mono (hd i hi) (by omega)
  have hterm : ∀i : Fin ps.length,Bounded S d (Ring.mul ps[i.val] (delta i.val)):=
    fun i=>NormalizedIntermediate.mono
      (NormalizedIntermediate.mul (hps _ (List.getElem_mem i.isLt)) (hd i.val i.isLt)) hab
  have hpref : ∀i,Bounded S d (VectorParentPrefix.value ps delta i):=
    fun i=>VectorParentPrefix.bounded S d ps delta hterm i
  have hcensus : ∀{P : Poly},Bounded S d P→P.length≤2^w:=fun hP=>(NormalizedIntermediate.census hP).trans hfit
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro P hP;exact (bounded_packet C w d S P (hc P hP) hfit).2
  · intro P hP;exact fits_of_bounded C S hS (hps P hP)
  · intro i hi;exact fits_of_bounded C S hS (hd i hi)
  · intro i _;exact (bounded_packet C w d S _ (hpref i) hfit).2
  · intro i;exact (bounded_packet C w d S _ (hterm i) hfit).2
  · intro i;exact (ReusableArithmetic.bounded_guards C w _ _
      (hcensus (hc _ (List.getElem_mem i.isLt))) (hcensus (hdelta i.val i.isLt)) hw).1
  · intro i;exact (ReusableArithmetic.bounded_guards C w _ _
      (hcensus (hc _ (List.getElem_mem i.isLt))) (hcensus (hdelta i.val i.isLt)) hw).2.1
  · intro i;exact (ReusableArithmetic.bounded_guards C w _ _ (hcensus (hpref i.val)) (hcensus (hterm i)) hw).1
  · intro i;exact (ReusableArithmetic.bounded_guards C w _ _ (hcensus (hpref i.val)) (hcensus (hterm i)) hw).2.2

theorem transaction_budget (C R i : Nat) (P Q acc : Poly)
    (hP : Fits C P) (hQ : Fits C Q) (hi : i≤R)
    (hm : NormalizedMultiply.budget C (masks C P) (masks C Q)+3≤R)
    (ha : NormalizedAddition.budget C (masks C acc) (masks C (Ring.mul P Q))+3≤R) :
    VectorChildTransaction.budget C R i (masks C Q) (masks C P) (masks C acc)≤128*(R+1)^2 := by
  have termEq:=VectorChildTransaction.term_nat C P Q hP hQ
  unfold VectorChildTransaction.budget VectorChildArithmetic.budget VectorAccumulator.budget
  rw [show VectorChildArithmetic.term (masks C P) (masks C Q)=masks C (Ring.mul P Q) from termEq]
  unfold ReusableArithmetic.budget PacketBank.lookupBudget VectorAccumulator.copyBudget
  have hmul:=Nat.mul_le_mul_right R hi
  nlinarith

end PCJ9eff70d512234a4c_Fixed.Materializer.VectorChildGuardBundle
