import Proof.Rows.RowsInitBinWords
import Proof.Rows.RowsInitThrInitRun
import Proof.Packets.PacketsMetaSeedCount

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace RowsInit.C5
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJd4d1d9d7d1fa4313_Production NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.BlockPlatform
open NearCubicWires.PacketFamilyParent RowsConstruction.ThrCell
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierWalkBridge
open RowsConstruction RowsConstruction.BaseLayout RowsInit.VecDock RowsInit.BinWords RowsInit.LoopWords
open RowsInit.ThrInitRun (fan_dock fin_out inst_at inst_off pad_nil)
open RowsInit.ThrLoop (wp wp_val vmap vmap_val vmap_inj rw_eq)
noncomputable section

/-! ## 1. The four words -/

section Words
variable (a : DecompositionAlgorithm)

abbrev seedS : UnaryStage a (seedCount a) := NearCubicWires.PacketsMeta.Seed.seedCountStage a

/-- `S = seedScratch N = 2·natBitLength N + 1`. -/
def scrS : UnaryStage a (fun r => seedScratch (seedCount a r)) :=
  (((bitLenS (seedS a)).thenMapP (scaleMap 2) (4 * 2 + 12) 2 (scale_cost 2)).thenMapP (plusMap 1) (2 * 1 + 4) 1
    (plus_cost 1)).ofEq (fun r => by simp only [seedScratch]; ring)

/-- The C5 words: `seedWords 0 N` (0, 1), `1^cut` (2), and the scratch driver `1^S` (3). -/
def c5Word (j : Fin 4) (r : Request) : List Bool :=
  match j.val with
  | 0 => frame (SignedSortKey.binary (natBitLength (seedCount a r)) 0)
  | 1 => frame (SignedSortKey.binary (natBitLength (seedCount a r)) (seedCount a r))
  | 2 => List.replicate (cutoffOf a r) true
  | _ => List.replicate (seedScratch (seedCount a r)) true

/-- **The C5 words by ONE fixed machine.** -/
def c5Vec :=
  ((((VecStage.nil a (fun _ _ => [])).snoc ((bitLenS (seedS a)).thenWordP zeroWordMap 8 1 zero_cost)).snoc
    (binWordS (bitLenS (seedS a)) (seedS a) (fun r => lt_bitLen (seedCount a r)))).snoc
    (NearCubicWires.PacketsMeta.cutoffStage a).toWord).snoc (scrS a).toWord

end Words

/-! ## 2. Slot maps -/

theorem c5_val (NI : ℕ) (i : Fin 16) : (c5Port NI i).val = 2 + NI + 594 + i.val := by
  simp [c5Port, fixPort, MT] <;> omega

/-- The vector stage: request (pub 0), words to C5 ports 0, 1, 2 and 11, scratch from `init oC`. -/
def g1 (NI oC v : ℕ) : ℕ :=
  if v = 0 then 0 else if v ≤ 3 then 2 + NI + 594 + (v - 1) else if v = 4 then 2 + NI + 594 + 11 else 2 + oC + (v - 5)
/-- The fanout: four blanks (C5 7–10), driver (C5 11), log (C5 12). -/
def gF (NI v : ℕ) : ℕ := 2 + NI + 594 + 7 + v

section Maps
variable (a : DecompositionAlgorithm) (NI oC : ℕ)

def needC : ℕ := (c5Vec a).extra + 1
def s1 (NI oC : ℕ) := vmap NI (1 + 4 + (c5Vec a).extra + 1) (g1 NI oC)
def sF (NI : ℕ) := vmap NI (0 + (4 + 1) + 1) (gF NI)
/-- No source. -/
def selC (_ : Fin 4) : Option (Fin 0) := none

variable (hC : oC + needC a ≤ NI)
include hC

theorem bd1 : ∀ v, v < 1 + 4 + (c5Vec a).extra + 1 → g1 NI oC v < 2 + rowsWork NI := by
  intro v hv; unfold needC at hC; rw [rw_eq]; unfold g1; split_ifs <;> omega
omit hC in
theorem bdF : ∀ v, v < 0 + (4 + 1) + 1 → gF NI v < 2 + rowsWork NI := by
  intro v hv; rw [rw_eq]; unfold gF; omega
theorem i1 : Function.Injective (s1 a NI oC) := vmap_inj (bd1 a NI oC hC) (by
  intro v w _ _ h; unfold needC at hC; unfold g1 at h; split_ifs at h <;> omega)
omit hC in
theorem iF : Function.Injective (sF NI) := vmap_inj (bdF NI) (by
  intro v w _ _ h; unfold gF at h; omega)

end Maps

/-! ## 3. The machine and the run -/

def machine (a : DecompositionAlgorithm) (NI oC : ℕ) :=
  Composition.machine (RecoveryFocus.machine (s1 a NI oC) (MaskedReset.machine (c5Vec a).machine (fun _ => true)))
    (RecoveryFocus.machine (sF NI) (ExtIncidence.NativeFanout.machine selC))

def cost (a : DecompositionAlgorithm) (r : Request) : ℕ :=
  (2 * (c5Vec a).cost r + 2) + 1 + (2 * seedScratch (seedCount a r) + 4)

/-- **The C5 writer.** Entry: pub 0 = framed request, C5 ports 0–2, 7–12 and the scratch `[oC, oC + needC)` blank, heads
`0`. Exit: C5 0, 1, 2 = `c5Word 0..2`, C5 7–10 = `0^S`, 11 = `1^S`, 12 = `0^(S+1)`; nothing outside C5 and the scratch
changes (pub 0 kept). -/
theorem run (a : DecompositionAlgorithm) (NI oC : ℕ) (hC : oC + needC a ≤ NI)
    (r : Request) (A : Fin (2 + rowsWork NI) → List Bool) (h0 : A (pubPort NI 0) = frame (r.input a))
    (hb : ∀ i : Fin 16, (i.val ≤ 2 ∨ (7 ≤ i.val ∧ i.val ≤ 12)) → A (c5Port NI i) = [])
    (hS : ∀ x : Fin (2 + rowsWork NI), 2 + oC ≤ x.val → x.val < 2 + oC + needC a → A x = []) :
    ∃ A' : Fin (2 + rowsWork NI) → List Bool,
      Step (machine a NI oC) (cost a r) (fun _ => 0) A (fun _ => 0) A' ∧
      (∀ j : Fin 3, A' (c5Port NI ⟨j.val, by omega⟩) = c5Word a ⟨j.val, by omega⟩ r) ∧
      (∀ i : Fin 16, 7 ≤ i.val → i.val ≤ 10 → A' (c5Port NI i) = List.replicate (seedScratch (seedCount a r)) false) ∧
      A' (c5Port NI 11) = List.replicate (seedScratch (seedCount a r)) true ∧
      A' (c5Port NI 12) = List.replicate (seedScratch (seedCount a r) + 1) false ∧
      (∀ i : Fin 16, (3 ≤ i.val ∧ i.val ≤ 6) ∨ 13 ≤ i.val → A' (c5Port NI i) = A (c5Port NI i)) ∧
      (∀ x : Fin (2 + rowsWork NI), ¬ (2 + NI + 594 ≤ x.val ∧ x.val < 2 + NI + 610) →
        ¬ (2 + oC ≤ x.val ∧ x.val < 2 + oC + needC a) → A' x = A x) := by
  have hb1 := bd1 a NI oC hC
  have hbF := bdF NI
  have hi1 := i1 a NI oC hC
  have hiF := iF NI
  have hn := hC
  unfold needC at hn hS
  have cv : ∀ i : Fin 16, c5Port NI i = wp NI (2 + NI + 594 + i.val) := fun i =>
    Fin.ext (by rw [c5_val, wp_val (by rw [rw_eq]; have := i.isLt; omega)])
  obtain ⟨B, s1r, b0, bj⟩ := vec_dock (c5Vec a) r (s1 a NI oC) hi1 (fun _ => 0) A (fun _ => rfl)
    (by rw [show s1 a NI oC ⟨0, by omega⟩ = pubPort NI 0 from Fin.ext (by rw [s1, vmap_val hb1]; rfl), h0])
    (by
      intro j hj
      have hv : (s1 a NI oC j).val = g1 NI oC j.val := vmap_val hb1 j
      have hl := j.isLt
      unfold g1 at hv
      rw [if_neg hj] at hv
      by_cases h3 : j.val ≤ 3
      · rw [if_pos h3] at hv
        have e : s1 a NI oC j = c5Port NI ⟨j.val - 1, by omega⟩ := Fin.ext (by rw [hv, c5_val])
        rw [e]
        exact hb _ (Or.inl (by simp only; omega))
      · rw [if_neg h3] at hv
        by_cases h4 : j.val = 4
        · rw [if_pos h4] at hv
          rw [show s1 a NI oC j = c5Port NI 11 from Fin.ext (by rw [hv, c5_val]; rfl)]
          exact hb _ (Or.inr (by decide))
        · rw [if_neg h4] at hv
          exact hS _ (by omega) (by omega))
  have key : ∀ j : Fin 4, B ⟨j.val + 1, by omega⟩ = c5Word a j r := by
    intro j; fin_cases j <;> exact bj _ (by omega)
  set A1 := install (s1 a NI oC) A B with hA1
  have a1_off : ∀ x : Fin (2 + rowsWork NI), x.val ≠ 0 → ¬ (2 + NI + 594 ≤ x.val ∧ x.val < 2 + NI + 610) →
      ¬ (2 + oC ≤ x.val ∧ x.val < 2 + oC + needC a) → A1 x = A x := by
    intro x h0' hx1 hx2
    unfold needC at hx2
    refine inst_off hb1 A B x (fun v hv h => ?_)
    unfold g1 at h; split_ifs at h <;> omega
  have hF : Step (RecoveryFocus.machine (sF NI) (ExtIncidence.NativeFanout.machine selC))
      (2 * seedScratch (seedCount a r) + 4) (fun _ => 0) A1 (fun _ => 0)
      (install (sF NI) A1 (ExtIncidence.NativeFanout.output selC (fun i : Fin 0 => i.elim0)
        (seedScratch (seedCount a r)))) := by
    refine fan_dock selC (fun i : Fin 0 => i.elim0) _ (sF NI) hiF (fun i => i.elim0) (fun _ => 0) A1 (fun _ => rfl)
      (fun v hv => absurd hv (Nat.not_lt_zero _)) ?_ ?_
    · have e : sF NI ⟨0 + 4, by omega⟩ = s1 a NI oC ⟨4, by omega⟩ := by
        apply Fin.ext
        rw [sF, s1, vmap_val hbF, vmap_val hb1]
        simp [gF, g1]
      rw [e, hA1, install_slot _ hi1]
      exact key 3
    · intro v hv _ h2
      have hx : (sF NI ⟨v, hv⟩).val = 2 + NI + 594 + 7 + v := vmap_val hbF ⟨v, hv⟩
      have e1 : A1 (sF NI ⟨v, hv⟩) = A (sF NI ⟨v, hv⟩) := by
        refine inst_off hb1 A B _ (fun w hw h => ?_)
        rw [hx] at h; unfold g1 at h; split_ifs at h <;> omega
      have e : sF NI ⟨v, hv⟩ = c5Port NI ⟨7 + v, by omega⟩ := Fin.ext (by
        have := c5_val NI ⟨7 + v, by omega⟩; simp only at this; omega)
      rw [e1, e]
      exact hb _ (Or.inr (by simp only; omega))
  set A2 := install (sF NI) A1 (ExtIncidence.NativeFanout.output selC (fun i : Fin 0 => i.elim0)
    (seedScratch (seedCount a r))) with hA2
  have a2_off : ∀ x : Fin (2 + rowsWork NI), ¬ (2 + NI + 601 ≤ x.val ∧ x.val ≤ 2 + NI + 606) → A2 x = A1 x := by
    intro x hx
    refine inst_off hbF A1 _ x (fun v hv h => ?_)
    unfold gF at h; omega
  refine ⟨A2, (s1r.seq hF).congr rfl rfl, fun j => ?_, fun i h7 h10 => ?_, ?_, ?_, fun i hi => ?_, fun x hx1 hx2 => ?_⟩
  · have hj := j.isLt
    have hw : 2 + NI + 594 + j.val < 2 + rowsWork NI := by rw [rw_eq]; omega
    have hpv : (wp NI (2 + NI + 594 + j.val)).val = 2 + NI + 594 + j.val := wp_val hw
    have hf : (wp NI (2 + NI + 594 + j.val)).val = g1 NI oC (j.val + 1) := by
      rw [hpv]; unfold g1; rw [if_neg (by omega), if_pos (by omega)]; omega
    have e2 : A2 (wp NI (2 + NI + 594 + j.val)) = A1 (wp NI (2 + NI + 594 + j.val)) := a2_off _ (by rw [hpv]; omega)
    rw [cv, e2, hA1, s1, inst_at hb1 hi1 A B _ (j.val + 1) (by omega) hf]
    exact key ⟨j.val, by omega⟩
  · have hl := i.isLt
    have hw : 2 + NI + 594 + i.val < 2 + rowsWork NI := by rw [rw_eq]; omega
    have hf : (wp NI (2 + NI + 594 + i.val)).val = gF NI (i.val - 7) := by rw [wp_val hw]; unfold gF; omega
    rw [cv, hA2, sF, inst_at hbF hiF A1 _ _ (i.val - 7) (by omega) hf, fin_out, dif_neg (by omega), dif_pos (by omega)]
    simp only [selC, Option.elim, pad_nil]
  · have hw : 2 + NI + 594 + 11 < 2 + rowsWork NI := by rw [rw_eq]; omega
    have e : c5Port NI 11 = wp NI (2 + NI + 594 + 11) := Fin.ext (by
      have := c5_val NI 11; rw [show ((11 : Fin 16) : ℕ) = 11 from rfl] at this; rw [wp_val hw]; omega)
    have hf : (wp NI (2 + NI + 594 + 11)).val = gF NI 4 := by rw [wp_val hw]; rfl
    rw [e, hA2, sF, inst_at hbF hiF A1 _ _ 4 (by omega) hf, fin_out, dif_neg (by omega), dif_neg (by omega), if_pos rfl]
  · have hw : 2 + NI + 594 + 12 < 2 + rowsWork NI := by rw [rw_eq]; omega
    have e : c5Port NI 12 = wp NI (2 + NI + 594 + 12) := Fin.ext (by
      have := c5_val NI 12; rw [show ((12 : Fin 16) : ℕ) = 12 from rfl] at this; rw [wp_val hw]; omega)
    have hf : (wp NI (2 + NI + 594 + 12)).val = gF NI 5 := by rw [wp_val hw]; rfl
    rw [e, hA2, sF, inst_at hbF hiF A1 _ _ 5 (by omega) hf, fin_out, dif_neg (by omega), dif_neg (by omega),
      if_neg (by omega)]
  · have hl := i.isLt
    have hv := c5_val NI i
    have e2 : A2 (c5Port NI i) = A1 (c5Port NI i) := a2_off _ (by omega)
    rw [e2]
    refine inst_off hb1 A B _ (fun w hw h => ?_)
    rw [hv] at h; unfold g1 at h; split_ifs at h <;> omega
  · have e2 : A2 x = A1 x := a2_off _ (by omega)
    rw [e2]
    by_cases hx0 : x.val = 0
    · have hf : x.val = g1 NI oC 0 := by rw [hx0]; rfl
      rw [hA1, s1, inst_at hb1 hi1 A B _ 0 (by omega) hf, b0, show x = pubPort NI 0 from Fin.ext hx0, h0]
    · exact a1_off _ hx0 hx1 hx2

/-! ## 4. THR: the first key's seed is seed `0`, and `|thrSeeds| = seedCount` -/

theorem head_flatMap {α β : Type} (P : β → Prop) (l : List α) (f : α → List β)
    (h : ∀ x ∈ l, ∀ y ∈ (f x).head?, P y) : ∀ y ∈ (l.flatMap f).head?, P y := by
  induction l with
  | nil => simp
  | cons x l ih =>
    intro y hy
    rw [List.flatMap_cons, List.head?_append] at hy
    cases hfx : (f x).head? with
    | none =>
      rw [hfx] at hy
      exact ih (fun z hz => h z (List.mem_cons_of_mem _ hz)) y (by simpa using hy)
    | some z =>
      rw [hfx] at hy
      simp only [Option.some_or, Option.mem_def, Option.some.injEq] at hy
      subst hy
      exact h x (List.mem_cons_self ..) z hfx

theorem head_ofFn_flatMap {α β : Type} {n : ℕ} (h : Fin n → α) (g : α → List β)
    (hlen : ∀ s t, (g s).length = (g t).length) :
    ∀ y ∈ ((List.ofFn h).flatMap g).head?, ∃ hn : 0 < n, y ∈ (g (h ⟨0, hn⟩)).head? := by
  cases n with
  | zero => simp
  | succ m =>
    intro y hy
    rw [List.ofFn_succ, List.flatMap_cons, List.head?_append] at hy
    refine ⟨Nat.succ_pos m, ?_⟩
    show y ∈ (g (h 0)).head?
    cases hz : (g (h 0)).head? with
    | some z =>
      rw [hz] at hy
      simp only [Option.some_or] at hy
      exact hy
    | none =>
      exfalso
      have h0 : g (h 0) = [] := List.head?_eq_none_iff.mp hz
      have hall : ∀ t, g t = [] := fun t => List.eq_nil_of_length_eq_zero (by rw [hlen t (h 0), h0]; rfl)
      have hnil : ∀ l : List α, l.flatMap g = [] := by
        intro l
        induction l with
        | nil => rfl
        | cons x l ih => rw [List.flatMap_cons, hall x, ih]; rfl
      rw [hnil] at hy
      simp [hz] at hy

section Thr
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : ℕ)

theorem thrSeeds_len : (thrSeeds a r L target).length = seedCount a (.thr r four L target) := rfl

/-- **The first THR key's seed index is `0`.** -/
theorem thrSeedIdx_head (k : RCFive.RowKeys.ThrKey a r L target) (hk : thrKeyAt a r L target 0 = some k) :
    thrSeedIdx a r L target k = 0 := by
  have hh : k ∈ (RCFive.RowKeys.thrKeys a r L target).head? := by
    unfold thrKeyAt at hk
    rw [Nat.zero_mod, ← List.head?_eq_getElem?] at hk
    exact hk
  refine head_flatMap (fun k => thrSeedIdx a r L target k = 0) _ _ (fun sel _ => ?_) k hh
  refine head_flatMap (fun k => thrSeedIdx a r L target k = 0) _ _ (fun pr _ => ?_)
  intro y hy
  unfold PCJ9eff70d512234a4c_Fixed.Packets.seedList at hy
  obtain ⟨hn, hy0⟩ := head_ofFn_flatMap _ _ (fun s t => by simp) y hy
  rw [List.head?_map] at hy0
  obtain ⟨res, -, rfl⟩ := Option.mem_map.mp hy0
  simp [thrSeedIdx]

/-- **The THR C5 block in consumer form** (`thrBase … 0`'s C5 words at the first key `k₀`). -/
theorem thr_block (NI : ℕ) (A' : Fin (2 + rowsWork NI) → List Bool) (k : RCFive.RowKeys.ThrKey a r L target)
    (hk : thrKeyAt a r L target 0 = some k)
    (h012 : ∀ j : Fin 3, A' (c5Port NI ⟨j.val, by omega⟩) = c5Word a ⟨j.val, by omega⟩ (.thr r four L target))
    (h7 : ∀ i : Fin 16, 7 ≤ i.val → i.val ≤ 10 →
      A' (c5Port NI i) = List.replicate (seedScratch (seedCount a (.thr r four L target))) false)
    (h11 : A' (c5Port NI 11) = List.replicate (seedScratch (seedCount a (.thr r four L target))) true)
    (h12 : A' (c5Port NI 12) = List.replicate (seedScratch (seedCount a (.thr r four L target)) + 1) false)
    (hz : ∀ i : Fin 16, (3 ≤ i.val ∧ i.val ≤ 6) ∨ 13 ≤ i.val → A' (c5Port NI i) = []) (i : Fin 16) :
    A' (c5Port NI i) = c5Words (seedWords (thrSeedIdx a r L target k) (thrSeeds a r L target).length)
      (List.replicate (NearCubicWires.RepairOrdinary.CloseoutFinalC10ThresholdRows.primeCutoff a r target) true)
      (fun _ => []) (seedScratch (thrSeeds a r L target).length) i := by
  rw [thrSeedIdx_head a r L target k hk, thrSeeds_len a r four L target]
  obtain ⟨i, hi⟩ := i
  interval_cases i
  · exact h012 ⟨0, by decide⟩
  · exact h012 ⟨1, by decide⟩
  · exact h012 ⟨2, by decide⟩
  · exact hz ⟨3, hi⟩ (Or.inl (by simp))
  · exact hz ⟨4, hi⟩ (Or.inl (by simp))
  · exact hz ⟨5, hi⟩ (Or.inl (by simp))
  · exact hz ⟨6, hi⟩ (Or.inl (by simp))
  · exact h7 ⟨7, hi⟩ (by simp) (by simp)
  · exact h7 ⟨8, hi⟩ (by simp) (by simp)
  · exact h7 ⟨9, hi⟩ (by simp) (by simp)
  · exact h7 ⟨10, hi⟩ (by simp) (by simp)
  · exact h11
  · exact h12
  · exact hz ⟨13, hi⟩ (Or.inr (by simp))
  · exact hz ⟨14, hi⟩ (Or.inr (by simp))
  · exact hz ⟨15, hi⟩ (Or.inr (by simp))

end Thr

end
end RowsInit.C5
