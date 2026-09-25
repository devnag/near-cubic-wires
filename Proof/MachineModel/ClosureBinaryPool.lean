import Proof.MachineModel.ClosureLiveEnumeration
import Proof.MachineModel.ClosureCompactSharedInput
import Proof.CaseAnalysis.FinalSupplierTable

/-! A.12 enumerates every live assignment once; its column count is independent
of that enumeration order. This pool uses the physical binary order while
keeping the existing sentinel, offsets, raw bank and pool cardinality. The
exported equality is at the count consumer, not merely a list permutation.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryPool
open RepairRepresentation RepairOrdinary SupplierPipeline SupplierEstimator SupplierPrinter
open ThresholdCompiler CanonicalFourfoldRowProgram RepairSource CloseoutFinal
open C10SupplierRowInput
open scoped BigOperators

noncomputable section
variable {q : Nat} (a : DecompositionAlgorithm) (live : Finset (Fin q))
  (occ : List (SupportedNormalizedGate q)) (s : Nat)

def assignmentAt (k : Nat) : BitInput live.card :=
  (LiveEnumeration.binary live.card).getD k (fun _ => false)

def poolFn (harity : (s+1)/2+s/2 = liveᶜ.card) (k : Nat) :
    ExactThresholdGate ((s+1)/2+s/2) :=
  castGate harity (hardwire live
    ((childList a live occ).getD (k % (childList a live occ).length) falseChild)
    (assignmentAt live (k / (childList a live occ).length)))

def pool (harity : (s+1)/2+s/2 = liveᶜ.card) : List (ExactThresholdGate ((s+1)/2+s/2)) :=
  falseGate ((s+1)/2+s/2) ::
    List.ofFn (fun k : Fin ((liveList live).length * (childList a live occ).length) =>
      poolFn a live occ s harity k.val)

theorem pool_length (harity : (s+1)/2+s/2 = liveᶜ.card) :
    (pool a live occ s harity).length = (C10SupplierRowInput.pool a live occ s harity).length := by
  simp only [pool,C10SupplierRowInput.pool,List.length_cons,List.length_ofFn]

theorem sum_assignmentAt {M : Type} [AddCommMonoid M] (f : BitInput live.card → M) :
    (∑ yi : Fin (liveList live).length, f (assignmentAt live yi.val)) =
      ∑ y : BitInput live.card, f y := by
  have hlen := (LiveEnumeration.binary_perm live).length_eq
  have he : List.ofFn (fun yi : Fin (liveList live).length => assignmentAt live yi.val) =
      LiveEnumeration.binary live.card := by
    apply List.ext_getElem
    · simpa only [List.length_ofFn] using hlen.symm
    · intro i hi hj
      simp only [List.getElem_ofFn,assignmentAt,List.getD_eq_getElem _ _ hj]
  rw [← List.sum_ofFn]
  change (List.ofFn (f ∘ fun yi : Fin (liveList live).length => assignmentAt live yi.val)).sum = _
  rw [← List.map_ofFn,he,LiveEnumeration.sum_binary]
  exact Finset.sum_map_toList _ _

theorem pool_index_eval (harity : (s+1)/2+s/2 = liveᶜ.card)
    (yi : Fin (liveList live).length) (c : Nat) (x : BitInput ((s+1)/2+s/2)) :
    ((pool a live occ s harity).get
      (Fin.cast (pool_length a live occ s harity).symm (poolIndex a live occ s harity yi c))).eval x =
      CloseoutRowsUniversal.assignment a live occ
        (joinInput live (assignmentAt live yi.val) (residualPoint live s harity x)) c := by
  rw [List.get_eq_getElem]
  simp only [Fin.val_cast]
  by_cases h : c < (childList a live occ).length
  · have hpos : 0 < (childList a live occ).length := Nat.lt_of_le_of_lt (Nat.zero_le c) h
    have hval : (poolIndex a live occ s harity yi c).val =
        (childList a live occ).length * yi.val + c + 1 := by
      unfold poolIndex
      rw [dif_pos h]
    have hmod : ((childList a live occ).length * yi.val + c) %
        (childList a live occ).length = c := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt h]
    have hdiv : ((childList a live occ).length * yi.val + c) /
        (childList a live occ).length = yi.val := by
      rw [Nat.mul_add_div hpos, Nat.div_eq_of_lt h]
      omega
    have h' : c < (ExtDecompositionBatch.GS a (CloseoutRowsUniversal.pool live occ)).length := h
    simp only [pool,hval,List.getElem_cons_succ,List.getElem_ofFn,poolFn,hmod,hdiv,
      List.getD_eq_getElem (childList a live occ) falseChild h,castGate_eval,hardwire_eval]
    unfold CloseoutRowsUniversal.assignment encodedFiniteBooleanAssignment residualPoint
    rw [dif_pos h']
    simp only [List.get_eq_getElem]
    rfl
  · have hval : (poolIndex a live occ s harity yi c).val = 0 := by
      unfold poolIndex
      rw [dif_neg h]
    have h' : ¬ c < (ExtDecompositionBatch.GS a (CloseoutRowsUniversal.pool live occ)).length := h
    simp only [pool,hval,List.getElem_cons_zero,falseGate_eval]
    unfold CloseoutRowsUniversal.assignment encodedFiniteBooleanAssignment
    rw [dif_neg h']

end
end NearCubicWires.P1Closure.BinaryPool
