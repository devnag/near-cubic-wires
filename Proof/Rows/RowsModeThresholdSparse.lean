import Proof.Supplier.RowThresholdSelections

/-! Exact sparse coefficients of the paper's canonical stack. Original
circuit occurrence segments are disjoint even when circuits repeat. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeThresholdSparse
open SupplierPipeline SupplierEstimator SupplierPrime RepairRepresentation
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def start (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (i : Fin r.circuits.length):=
  ((r.circuits.take i.val).flatMap thresholdCircuitOccurrences).length

theorem embedding_val (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (i : Fin r.circuits.length)
    (j : Fin (r.circuits.get i).top.support.card) :
    (thresholdCircuitEmbedding r i j).val=start r i+j.val:=rfl

theorem end_le (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (i j : Fin r.circuits.length)
    (hij : i.val < j.val) : start r i+(r.circuits.get i).top.support.card ≤ start r j:=by
  have h:=((List.take_sublist_take_left (l:=r.circuits) (show i.val+1 ≤ j.val by omega)).flatMap thresholdCircuitOccurrences).length_le
  rw [List.take_succ_eq_append_getElem i.isLt] at h
  simpa only [List.flatMap_append,List.flatMap_singleton,List.length_append,thresholdCircuitOccurrences,
    List.length_ofFn,List.get_eq_getElem,start] using h

theorem embedding_ne (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (i j : Fin r.circuits.length)
    (hi : i≠j) (x : Fin (r.circuits.get i).top.support.card) (y : Fin (r.circuits.get j).top.support.card) :
    thresholdCircuitEmbedding r i x≠thresholdCircuitEmbedding r j y:=by
  intro he
  have hv:=congrArg Fin.val he
  rw [embedding_val,embedding_val] at hv
  have hx:=x.isLt
  have hy:=y.isLt
  have hne:i.val≠j.val:=by intro h;exact hi (Fin.ext h)
  rcases lt_or_gt_of_ne hne with h | h
  · have hb:=end_le r i j h;omega
  · have hb:=end_le r j i h;omega

theorem own_weight (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (i : Fin r.circuits.length)
    (child : ExactThresholdGate (r.circuits.get i).top.support.card) (x : Fin (r.circuits.get i).top.support.card) :
    (thresholdChildEquation r i child).weights (thresholdCircuitEmbedding r i x)=child.weight x:=by
  unfold thresholdChildEquation embeddedWeight
  dsimp only
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    exact if_neg (fun h=>hy ((thresholdCircuitEmbedding r i).injective h))
  · intro h;exact (h (Finset.mem_univ _)).elim

theorem other_weight (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (i j : Fin r.circuits.length)
    (hij : i≠j) (child : ExactThresholdGate (r.circuits.get i).top.support.card)
    (x : Fin (r.circuits.get j).top.support.card) :
    (thresholdChildEquation r i child).weights (thresholdCircuitEmbedding r j x)=0:=by
  unfold thresholdChildEquation embeddedWeight
  dsimp only
  apply Finset.sum_eq_zero
  intro y _
  exact if_neg (embedding_ne r i j hij y x)

theorem stack_weights {Carrier : Type} (base : Int) {n : Nat} (es : Fin n→LabelledEquation Carrier) (x : Carrier) :
    (stackEquations base (List.ofFn es)).weights x=
      ∑ i : Fin n,base^i.val*(es i).weights x:=by
  induction n with
  | zero=>simp [stackEquations]
  | succ n ih=>
    rw [List.ofFn_succ,Fin.sum_univ_succ]
    change (es 0).weights x+base*(stackEquations base (List.ofFn (fun i : Fin n=>es i.succ))).weights x=_
    rw [ih,Finset.mul_sum]
    simp only [Fin.val_zero,pow_zero,one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [Fin.val_succ,pow_succ]
    ring

theorem coefficient (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (sel : ThresholdRows.Selection a r) (i : Fin r.circuits.length)
    (x : Fin (r.circuits.get i).top.support.card) :
    (ThresholdRows.equation a r sel).weights (thresholdCircuitEmbedding r i x)=
      equationListBase (ThresholdRows.equations a r sel)^i.val*
        ((ThresholdRows.children a (r.circuits.get i)).get (sel i)).weight x:=by
  unfold ThresholdRows.equation canonicalEquationStack ThresholdRows.equations
  rw [stack_weights]
  rw [Finset.sum_eq_single i]
  · simp only [own_weight]
  · intro j _ hj
    simp only [other_weight r j i hj,mul_zero]
  · intro h;exact (h (Finset.mem_univ _)).elim

theorem residue (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (sel : ThresholdRows.Selection a r) (i : Fin r.circuits.length)
    (x : Fin (r.circuits.get i).top.support.card) (p : Nat) :
    modularCoefficientResidue (ThresholdRows.equation a r sel) p (thresholdCircuitEmbedding r i x)=
      (((equationListBase (ThresholdRows.equations a r sel)^i.val % (p : Int))*
        (((ThresholdRows.children a (r.circuits.get i)).get (sel i)).weight x % (p : Int))) % (p : Int)).toNat:=by
  unfold modularCoefficientResidue
  rw [coefficient,Int.mul_emod]

end NearCubicWires.RepairOrdinary.CloseoutRowsModeThresholdSparse
