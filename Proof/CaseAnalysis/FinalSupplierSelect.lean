import Proof.CaseAnalysis.FinalPrinterBridge
import Proof.CaseAnalysis.RowsDegreeLoop
import Proof.CaseAnalysis.RowsEstimatorRecord
import Proof.MachineModel.Runs

set_option autoImplicit false

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.LocalBitMultitape
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrinter
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch (Step)
open NearCubicWires.RepairOrdinary.CompetitorCountMask (mask selected)
open NearCubicWires.RepairOrdinary.CompetitorFinalTable (lowerColumn)
open NearCubicWires.RepairSource.CloseoutFinal

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SupplierSelect

section Offsets

variable (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) (liveScale : ℕ)

/-- \(\mathbf F(z)=\bigl(C_i(z)\bigr)_i\) (A.3 :1970-1974), a function of the residual
column `z` ALONE (`C10PrinterBridge.residualOffset_spec`). -/
noncomputable def offsetOf
    (z : BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card)
    (circuitIndex : Fin request.circuits.length) : ℕ :=
  C10PrinterBridge.residualOffset request liveScale z circuitIndex

end Offsets

section Selector

end Selector

section MaskWord

/-- Physical columns of the cropped cell grid (`CompetitorSelectedCells.cells`: an odd
residual arity crops the column half to `u / 2` through `lowerColumn`). -/
def maskColumns (odd : Bool) (u : ℕ) : ℕ := if odd then u / 2 else u

/-- Physical cells of the cropped grid; `cellCount_eq` identifies it with \(2^{q-K}\). -/
def cellCount (odd : Bool) (u : ℕ) : ℕ := u * maskColumns odd u

theorem ofFn_val {α : Type} (v : ℕ) (g : ℕ → α) :
    (List.ofFn fun j : Fin v => g j.val) = (List.range v).map g := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp

theorem flatten_ofFn {α : Type} (u : ℕ) (h : ℕ → List α) :
    (List.ofFn fun i : Fin u => h i.val).flatten = (List.range u).flatMap h := by
  rw [ofFn_val, List.flatMap_def]

theorem range_mul_map {α : Type} (v : ℕ) (g : ℕ → ℕ → α) (u : ℕ) :
    (List.range (u * v)).map (fun k => g (k / v) (k % v)) =
      (List.range u).flatMap (fun a => (List.range v).map (g a)) := by
  induction u with
  | zero => simp
  | succ u ih =>
    have hsplit : (u + 1) * v = u * v + v := by ring
    rw [hsplit, List.range_add, List.map_append, ih, List.range_succ, List.flatMap_append]
    congr 1
    rw [List.map_map]
    have hstep : ∀ b ∈ List.range v,
        ((fun k => g (k / v) (k % v)) ∘ fun x => u * v + x) b = g u b := by
      intro b hb
      have hbv : b < v := List.mem_range.mp hb
      have hv : 0 < v := Nat.lt_of_le_of_lt (Nat.zero_le b) hbv
      have hdiv : (u * v + b) / v = u := by
        rw [Nat.add_comm, Nat.add_mul_div_right b u hv, Nat.div_eq_of_lt hbv, Nat.zero_add]
      have hmod : (u * v + b) % v = b := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hbv]
      simp only [Function.comp_apply, hdiv, hmod]
    rw [List.map_congr_left hstep]
    simp

theorem mask_rect {u v : ℕ} (f : Fin u → Fin v → ℕ) (s : Fin u → Fin v → Bool) :
    mask (CompetitorSelectedCells.rect f s) =
      (List.ofFn fun i => List.ofFn fun j => s i j).flatten := by
  simp [mask, CompetitorSelectedCells.rect, List.map_flatten, List.map_ofFn, Function.comp_def]

/-- Row-major scan of a rectangle of Boolean cells whose value depends on the two
addresses only through their numerals. -/
theorem mask_rect_range {u v : ℕ} (sel : Fin u → Fin v → Bool) (G : ℕ → ℕ → Bool)
    (hsel : ∀ (i : Fin u) (j : Fin v), sel i j = G i.val j.val) :
    mask (CompetitorSelectedCells.rect (fun _ _ => (0 : ℕ)) sel) =
      (List.range (u * v)).map (fun k => G (k / v) (k % v)) := by
  have hrow : ∀ i : Fin u, (List.ofFn fun j : Fin v => sel i j) = (List.range v).map (G i.val) := by
    intro i
    rw [show (fun j : Fin v => sel i j) = fun j : Fin v => G i.val j.val from
      funext fun j => hsel i j]
    exact ofFn_val v (G i.val)
  calc mask (CompetitorSelectedCells.rect (fun _ _ => (0 : ℕ)) sel)
      = (List.ofFn fun i : Fin u => List.ofFn fun j : Fin v => sel i j).flatten :=
        mask_rect _ _
    _ = (List.ofFn fun i : Fin u => (List.range v).map (G i.val)).flatten := by
        rw [show (fun i : Fin u => List.ofFn fun j : Fin v => sel i j) =
          fun i : Fin u => (List.range v).map (G i.val) from funext hrow]
    _ = (List.range u).flatMap fun a => (List.range v).map (G a) :=
        flatten_ofFn u fun a => (List.range v).map (G a)
    _ = (List.range (u * v)).map (fun k => G (k / v) (k % v)) := (range_mul_map v G u).symm

end MaskWord

section Reindex

theorem sum_fin_congr {a b : ℕ} (h : a = b) (F : ℕ → ℕ) :
    ∑ j : Fin a, F j.val = ∑ j : Fin b, F j.val := by
  subst h
  rfl

/-- The cropped physical grid IS the product of the two external half-cubes: `u = 2^{|right|}`
rows and `2^{|left|}` columns, the odd case cropping through `lowerColumn`. -/
theorem total_eq_sum_half {q : ℕ} (live : Finset (Fin q)) (G : ℕ → ℕ → ℕ) (u : ℕ) (odd : Bool)
    (hu : u = 2 ^ normalizedExternalRightCount live)
    (hodd : odd = decide (liveᶜ.card % 2 = 1)) :
    RowExternalSelection.total odd (fun i j : Fin u => G i.val j.val) =
      ∑ i : Fin (2 ^ normalizedExternalRightCount live),
        ∑ j : Fin (2 ^ normalizedExternalLeftCount live), G i.val j.val := by
  subst hu
  cases odd with
  | false =>
    have hpar : liveᶜ.card % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one liveᶜ.card with h | h
      · exact h
      · rw [h] at hodd
        simp at hodd
    have hRL : normalizedExternalRightCount live = normalizedExternalLeftCount live := by
      unfold normalizedExternalRightCount normalizedExternalLeftCount
      omega
    simp only [RowExternalSelection.total, Bool.false_eq_true, if_false]
    refine Finset.sum_congr rfl ?_
    intro i _
    exact sum_fin_congr (by rw [hRL]) fun b => G i.val b
  | true =>
    have hpar : liveᶜ.card % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one liveᶜ.card with h | h
      · rw [h] at hodd
        simp at hodd
      · exact h
    have hR : normalizedExternalRightCount live = normalizedExternalLeftCount live + 1 := by
      unfold normalizedExternalRightCount normalizedExternalLeftCount
      omega
    have hhalf : 2 ^ normalizedExternalRightCount live / 2 =
        2 ^ normalizedExternalLeftCount live := by
      rw [hR, pow_succ, Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
    simp only [RowExternalSelection.total, if_true]
    refine Finset.sum_congr rfl ?_
    intro i _
    exact sum_fin_congr hhalf fun b => G i.val b

end Reindex

section SelectedSum

end SelectedSum

section Corollary

end Corollary

section Writer

end Writer

section Run

variable (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) (liveScale : ℕ)

/-- The loop driver's added counter tape is the last one: the body's slots are unchanged. -/
theorem cfg_tapes_castAdd {t s : ℕ} (phase : Fin 5) (data : Configuration t s)
    (total head : ℕ) (i : Fin t) :
    (RepairSource.VerifierDecoding.RepeatMachine.cfg phase data total head).tapes
        (i.castAdd 1) = data.tapes i := by
  simp [RepairSource.VerifierDecoding.RepeatMachine.cfg, controlConfig, TapeEmbedding.config]

end Run

section Consumer

end Consumer

section ExternalRows

variable (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) (liveScale : ℕ)

/-- A.3 :1976 "every possible \(f\in\{0,\ldots,M\}\)": the finite set of offset tuples one
external row is printed for.  It is the corpus's own offset family
(`RowOffsets.SymmetricOffsets`, `Proof/Supplier/RowOffsetFamilies.lean`) read as ℕ. -/
noncomputable def offsetRange : Finset (Fin request.circuits.length → ℕ) :=
  Finset.image (fun w : RowOffsets.SymmetricOffsets request => fun c => (w c).val) Finset.univ

theorem offsetOf_mem_offsetRange
    (z : BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card) :
    offsetOf request liveScale z ∈ offsetRange request := by
  refine Finset.mem_image.mpr ⟨RowOffsets.symmetricOffsets request liveScale
    (C10PrinterBridge.inputOf request liveScale (fun _ => false) z), Finset.mem_univ _, rfl⟩

/-- **A.13.9 :3155-3164, the whole column sum.**  Summing the per-offset external rows over
the offset range restores \(\sum_zT_{e,\mathbf F(z)}(z)\): each residual column is charged
to exactly the one printed row whose offset is its own \(\mathbf F(z)\). -/
theorem offsets_partition
    (T : (Fin request.circuits.length → ℕ) →
      BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card → ℕ) :
    (∑ f ∈ offsetRange request, ∑ z, if offsetOf request liveScale z = f then T f z else 0) =
      ∑ z, T (offsetOf request liveScale z) z := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro z _
  rw [Finset.sum_ite_eq (offsetRange request) (offsetOf request liveScale z)
    (fun f => T f z)]
  exact if_pos (offsetOf_mem_offsetRange request liveScale z)

end ExternalRows


end NearCubicWires.RepairSource.CloseoutFinal.C10SupplierSelect