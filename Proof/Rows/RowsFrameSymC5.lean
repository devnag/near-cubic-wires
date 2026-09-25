import Proof.Rows.RowsFrameSymWords

/-! # Rows initializer: the C5 block of `symBase … 0` (first key: seed `0`, offsets `0`) in consumer form

**Consumer.** `Parts.initial` → `Family.entry`'s work block `baseOf … (.sym r four L target) 0 = symBase … 0`
(`Proof/Rows/RowsBaseLayout.lean`): at the first key `k₀` its C5 block is
`c5Words (seedWords (symSeedIdx k₀) N) [] (symOffWords … T k₀) (seedScratch N)`, `N = |symSeeds|`. Its ports 0, 1, 2, 7–12 are
written by RX's `RowsInit.C5.run` (every request; on SYM the cutoff word is `1^0 = []`), its offsets 3–6 by
`RowsFrameSymWords.words_run` (`fb (T+3) 0`). This module proves the two facts about the first key that make those words
exact: `symSeedIdx k₀ = 0` (the first seed of `seedList = List.ofFn e.symm`) and `k₀.offset = 0` (the first tuple of the
lexicographic `finiteProduct`), and assembles the block (`sym_block`), the SYM twin of RX's `RowsInit.C5.thr_block`.

**Paper.** `paper.tex:1193-1196` (rows enumerated by seed, then by the offset tuple; row 0 = the first seed and the zero tuple).
**Budget.** None (value lemmas).
-/
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace RowsInit.FrameSymC5
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open PCJd4d1d9d7d1fa4313_Production NearCubicWires.PacketsGlue.RequestMeta
open RowsConstruction RowsConstruction.BaseLayout
noncomputable section

/-! ## 1. Heads of the enumerations -/

theorem flatMap_nil_of {α β : Type} (g : α → List β) (hall : ∀ s, g s = []) : ∀ t : List α, t.flatMap g = []
  | [] => rfl
  | u :: t => by rw [List.flatMap_cons, hall u, flatMap_nil_of g hall t]; rfl

/-- The head of a `flatMap` whose blocks all have the same length is the head of the first block. -/
theorem head_flatMap_unif {α β : Type} (l : List α) (g : α → List β) (hlen : ∀ s t, (g s).length = (g t).length) :
    ∀ y ∈ (l.flatMap g).head?, ∃ x ∈ l.head?, y ∈ (g x).head? := by
  cases l with
  | nil => simp
  | cons x t =>
    intro y hy
    rw [List.flatMap_cons, List.head?_append] at hy
    refine ⟨x, rfl, ?_⟩
    cases hz : (g x).head? with
    | some z =>
      rw [hz] at hy
      simpa using hy
    | none =>
      exfalso
      have h0 : g x = [] := List.head?_eq_none_iff.mp hz
      have hall : ∀ s, g s = [] := fun s => List.eq_nil_of_length_eq_zero (by rw [hlen s x, h0]; rfl)
      have hnil : t.flatMap g = [] := flatMap_nil_of g hall t
      rw [hz, hnil] at hy
      simp at hy

theorem finRange_head (m : ℕ) : ∀ x ∈ (List.finRange m).head?, x.val = 0 := by
  cases m with
  | zero => simp
  | succ m =>
    intro x hx
    rw [List.finRange_succ, List.head?_cons, Option.mem_def, Option.some.injEq] at hx
    rw [← hx]
    rfl

theorem ofFn_head {α : Type} {m : ℕ} (f : Fin m → α) : ∀ y ∈ (List.ofFn f).head?, ∃ h : 0 < m, y = f ⟨0, h⟩ := by
  cases m with
  | zero => simp
  | succ m =>
    intro y hy
    rw [List.ofFn_succ, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    exact ⟨Nat.succ_pos m, hy.symm⟩

/-- **The first tuple of the lexicographic finite product is the zero tuple.** -/
theorem fp_head : ∀ (n : ℕ) (bounds : Fin n → ℕ),
    ∀ y ∈ (PCJ9eff70d512234a4c_Fixed.Packets.finiteProduct n bounds).head?, ∀ i, (y i).val = 0
  | 0, _, _, _, i => i.elim0
  | n + 1, bounds, y, hy, i => by
    rw [PCJ9eff70d512234a4c_Fixed.Packets.finiteProduct] at hy
    obtain ⟨x, hx, hy'⟩ := head_flatMap_unif _ _ (fun s t => by simp) y hy
    rw [List.head?_map] at hy'
    obtain ⟨t, ht, rfl⟩ := Option.mem_map.mp hy'
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [Fin.cons_zero]
      exact finRange_head _ x hx
    · rw [Fin.cons_succ]
      exact fp_head n _ t ht j

/-! ## 2. The first SYM key -/

section Sym
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : ℕ)

/-- **The first SYM key: seed index `0`, every offset `0`.** -/
theorem key_head (k : RCFive.RowKeys.SymKey r L target) (hk : symKeyAt r L target 0 = some k) :
    symSeedIdx r L target k = 0 ∧ ∀ i, k.offset i = 0 := by
  have hh : k ∈ (RCFive.RowKeys.symKeys r L target).head? := by
    unfold symKeyAt at hk
    rw [Nat.zero_mod, ← List.head?_eq_getElem?] at hk
    exact hk
  unfold RCFive.RowKeys.symKeys at hh
  obtain ⟨s, hs, hk'⟩ := head_flatMap_unif _ _ (fun s t => by simp) k hh
  rw [List.head?_map] at hk'
  obtain ⟨o, ho, rfl⟩ := Option.mem_map.mp hk'
  refine ⟨?_, fun i => ?_⟩
  · unfold PCJ9eff70d512234a4c_Fixed.Packets.seedList at hs
    obtain ⟨hn, rfl⟩ := ofFn_head _ s hs
    simp [symSeedIdx]
  · unfold PCJ9eff70d512234a4c_Fixed.Packets.symOffsetList at ho
    rw [List.head?_map] at ho
    obtain ⟨f, hf, rfl⟩ := Option.mem_map.mp ho
    exact fp_head _ _ f hf i

theorem symSeedIdx_head (k : RCFive.RowKeys.SymKey r L target) (hk : symKeyAt r L target 0 = some k) :
    symSeedIdx r L target k = 0 :=
  (key_head r L target k hk).1

/-- The first key's C5 offset words are `fb (T+3) 0`. -/
theorem symOff_head (T : ℕ) (k : RCFive.RowKeys.SymKey r L target) (hk : symKeyAt r L target 0 = some k) (c : Fin 4) :
    symOffWords r L target T k c = frame (SignedSortKey.binary (T + 3) 0) := by
  unfold symOffWords
  split_ifs with h
  · rw [(key_head r L target k hk).2]
  · rfl

theorem symSeeds_len : (symSeeds r L target).length = seedCount a (.sym r four L target) := rfl

/-- **The SYM C5 block in consumer form** (`symBase … 0`'s C5 words at the first key `k₀`): RX's `C5.run` exit on ports 0–2, 7–12,
`words_run`'s offsets on 3–6, blanks on 13–15. -/
theorem sym_block (NI : ℕ) (A' : Fin (2 + rowsWork NI) → List Bool) (k : RCFive.RowKeys.SymKey r L target)
    (hk : symKeyAt r L target 0 = some k)
    (h012 : ∀ j : Fin 3, A' (c5Port NI ⟨j.val, by omega⟩) = RowsInit.C5.c5Word a ⟨j.val, by omega⟩ (.sym r four L target))
    (h7 : ∀ i : Fin 16, 7 ≤ i.val → i.val ≤ 10 →
      A' (c5Port NI i) = List.replicate (seedScratch (seedCount a (.sym r four L target))) false)
    (h11 : A' (c5Port NI 11) = List.replicate (seedScratch (seedCount a (.sym r four L target))) true)
    (h12 : A' (c5Port NI 12) = List.replicate (seedScratch (seedCount a (.sym r four L target)) + 1) false)
    (hoff : ∀ i : Fin 16, 3 ≤ i.val → i.val ≤ 6 →
      A' (c5Port NI i) = frame (SignedSortKey.binary ((Request.input a (.sym r four L target)).length + 3) 0))
    (hz : ∀ i : Fin 16, 13 ≤ i.val → A' (c5Port NI i) = []) (i : Fin 16) :
    A' (c5Port NI i) = c5Words (seedWords (symSeedIdx r L target k) (symSeeds r L target).length) []
      (symOffWords r L target (symT a r four L target) k) (seedScratch (symSeeds r L target).length) i := by
  rw [symSeedIdx_head r L target k hk, symSeeds_len a r four L target]
  have ho := symOff_head r L target (symT a r four L target) k hk
  obtain ⟨i, hi⟩ := i
  interval_cases i
  · exact h012 ⟨0, by decide⟩
  · exact h012 ⟨1, by decide⟩
  · exact h012 ⟨2, by decide⟩
  · exact (hoff ⟨3, hi⟩ (by simp) (by simp)).trans (ho 0).symm
  · exact (hoff ⟨4, hi⟩ (by simp) (by simp)).trans (ho 1).symm
  · exact (hoff ⟨5, hi⟩ (by simp) (by simp)).trans (ho 2).symm
  · exact (hoff ⟨6, hi⟩ (by simp) (by simp)).trans (ho 3).symm
  · exact h7 ⟨7, hi⟩ (by simp) (by simp)
  · exact h7 ⟨8, hi⟩ (by simp) (by simp)
  · exact h7 ⟨9, hi⟩ (by simp) (by simp)
  · exact h7 ⟨10, hi⟩ (by simp) (by simp)
  · exact h11
  · exact h12
  · exact hz ⟨13, hi⟩ (by simp)
  · exact hz ⟨14, hi⟩ (by simp)
  · exact hz ⟨15, hi⟩ (by simp)

end Sym

end
end RowsInit.FrameSymC5
