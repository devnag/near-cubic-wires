import Proof.Packets.PacketsKeysStageOn
import Proof.Rows.RowsModeThresholdScalars

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.PacketsKeys.Thr
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction NearCubicWires.PacketsConstruction.Residual
open PCJd4d1d9d7d1fa4313_Production NearCubicWires.ThresholdAlignedEnvelope
noncomputable section

/-! ## `List.ofFn` over consecutive blocks -/

theorem take_sum_lt {α : Type} (g : α → ℕ) (L : List α) (c : Fin L.length) (x : ℕ) (hx : x < g (L.get c)) :
    ((L.take c.val).map g).sum + x < (L.map g).sum := by
  have h2 : ((L.map g).take (c.val + 1)).sum ≤ (L.map g).sum :=
    List.Sublist.sum_le_sum (List.take_sublist _ _) (fun _ _ => Nat.zero_le _)
  rw [List.sum_take_succ _ _ (by simp)] at h2
  simp only [List.getElem_map, List.map_take] at h2 ⊢
  simp only [List.get_eq_getElem] at hx
  omega

theorem ofFn_blocks {α β : Type} (g : α → ℕ) : ∀ (L : List α) (f : Fin (L.map g).sum → β),
    List.ofFn f = (List.ofFn (fun c : Fin L.length => List.ofFn (fun x : Fin (g (L.get c)) =>
      f ⟨((L.take c.val).map g).sum + x.val, take_sum_lt g L c x.val x.isLt⟩))).flatten
  | [], f => by simp
  | a :: L, f => by
    have ih := ofFn_blocks (β := β) g L
    have e1 := @List.ofFn_add β (g a) (L.map g).sum f
    refine e1.trans ?_
    rw [List.ofFn_succ, List.flatten_cons, ih]
    congr 1
    · congr 1
      funext x
      congr 1
      apply Fin.ext
      simp
    · congr 1
      congr 1
      funext c
      congr 1
      funext x
      congr 1
      apply Fin.ext
      simp only [Fin.natAdd, List.take_succ_cons, List.map_cons, List.sum_cons, List.length_cons, Fin.val_succ]
      omega

/-! ## The residues of the selected equation -/

open NearCubicWires.RepairOrdinary.CloseoutRowsModeThresholdSparse in
/-- The stack base, as a natural number. -/
def baseN (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (sel : ThresholdRows.Selection a r) : ℕ :=
  (∑ i : Fin r.circuits.length, childMagnitude ((ThresholdRows.children a (r.circuits.get i)).get (sel i))) + 1

/-- Bit `j` of the residue of the weight `w` scaled by `B^c`, modulo `p`. -/
def wbit (B c p j : ℕ) (w : ℤ) : Bool := ((B ^ c % p * (w % (p : ℤ)).toNat) % p).testBit j

/-- **The THR mask word**: circuit by circuit, weight by weight. -/
def thrBits (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (sel : ThresholdRows.Selection a r) (p j : ℕ) : List Bool :=
  (List.ofFn (fun c : Fin r.circuits.length => List.ofFn (fun x : Fin (r.circuits.get c).top.support.card =>
    wbit (baseN a r sel) c.val p j (((ThresholdRows.children a (r.circuits.get c)).get (sel c)).weight x)))).flatten

theorem thrOcc_length (r : FourfoldRequest NormalizedThresholdThresholdCircuit) :
    (thresholdFourfoldOccurrences r).length = (r.circuits.map (fun c => c.top.support.card)).sum := by
  unfold thresholdFourfoldOccurrences
  rw [List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro c _
  simp [thresholdCircuitOccurrences]

theorem residue_nat (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (sel : ThresholdRows.Selection a r) (c : Fin r.circuits.length) (x : Fin (r.circuits.get c).top.support.card)
    (p : ℕ) (hp : 0 < p) :
    modularCoefficientResidue (ThresholdRows.equation a r sel) p (thresholdCircuitEmbedding r c x) =
      (baseN a r sel ^ c.val % p * ((((ThresholdRows.children a (r.circuits.get c)).get (sel c)).weight x) %
        (p : ℤ)).toNat) % p := by
  rw [CloseoutRowsModeThresholdSparse.residue, CloseoutRowsModeThresholdSparse.canonical_base]
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  set w := ((ThresholdRows.children a (r.circuits.get c)).get (sel c)).weight x with hw
  have hw0 : 0 ≤ w % (p : ℤ) := Int.emod_nonneg _ (by omega)
  have e1 : (((∑ i : Fin r.circuits.length, childMagnitude ((ThresholdRows.children a (r.circuits.get i)).get (sel i)))
      + 1 : ℕ) : ℤ) ^ c.val % (p : ℤ) = ((baseN a r sel ^ c.val % p : ℕ) : ℤ) := by
    unfold baseN
    push_cast
    rfl
  rw [e1]
  have e2 : w % (p : ℤ) = ((w % (p : ℤ)).toNat : ℤ) := (Int.toNat_of_nonneg hw0).symm
  rw [e2]
  norm_cast

theorem thr_bits (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) (k : rcKey a (.thr r four L target)) (j : ℕ)
    (hj : j < modulusDigitCount k.prime.val) :
    (maskBitsList a (.thr r four L target) k).getD j [] = thrBits a r k.selection k.prime.val j := by
  have hp : 0 < k.prime.val := (Nat.Prime.pos (mem_primesUpTo.mp k.prime.property).1)
  have hl : j < (thrMasks a r L target k).length := by simp [thrMasks]; exact hj
  simp only [maskBitsList]
  rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map]
  simp only [thrMasks, List.getElem_ofFn]
  unfold MaskCoord.maskBits
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, Bool.decide_eq_true]
  rw [List.ofFn_congr (thrOcc_length r),
    ofFn_blocks (fun c : NormalizedThresholdThresholdCircuit r.q => c.top.support.card) r.circuits]
  unfold thrBits
  congr 1
  apply congrArg List.ofFn
  funext c
  apply congrArg List.ofFn
  funext x
  have he : (Fin.cast (thrOcc_length r).symm ⟨((r.circuits.take c.val).map (fun c => c.top.support.card)).sum + x.val,
      take_sum_lt (fun c : NormalizedThresholdThresholdCircuit r.q => c.top.support.card) r.circuits c x.val x.isLt⟩ :
      Fin (thresholdFourfoldOccurrences r).length) = thresholdCircuitEmbedding r c x := by
    apply Fin.ext
    rw [CloseoutRowsModeThresholdSparse.embedding_val]
    simp only [Fin.val_cast, CloseoutRowsModeThresholdSparse.start, List.length_flatMap]
    congr 2
    apply List.map_congr_left
    intro c _
    simp [thresholdCircuitOccurrences]
  rw [he, residue_nat a r k.selection c x k.prime.val hp]
  rfl

end
end NearCubicWires.PacketsKeys.Thr

