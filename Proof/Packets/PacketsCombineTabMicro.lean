import Proof.Packets.PacketsCombineTabMeaning

/-! # P2 (iii) table writer, part 1: the small fixed machines and their exact runs

Consumer: the THR selection-table writer (`ThrMeta`'s tape 15, `Proof/Packets/PacketsCombineThrLocal.lean`), whose
acceptance bit is `modularTupleAccepts prime residue 2` (A.13.7, `paper.tex:3113-3142`; charged in
`T_prep`, `paper.tex:1197-1200`). Every machine here is a few states; each exact run is proved by its
transitions. A residue register modulo `p = P+1` is the head position `x ≤ P` on the unary word
`CompareMachine.word P` (read `false` exactly at `0` and past `P`).

* `moveAll`, `writeMove`: one step on every tape of a group;
* `rewAll`: walk a group left until its marker tape (tape 0) reads `true` (the group's left end);
* `copyOut neg`: append the scanned source bit (negated if `neg`) to an output tape;
* `rewReg`: walk a residue register back to `0`;
* `skipSeg`: pass one unary segment `true^w false` of the segment tape;
* `addSeg`: pass one segment while adding its length to a residue register modulo `P+1`.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsCombine.Tab
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

/-! ## Timed runs with an upper bound -/

/-- A run of at most `B` steps between two configurations. -/
def TimedLe {t s : ℕ} (p : Machine t s) (B : ℕ) (c d : Configuration t s) : Prop :=
  ∃ n, n ≤ B ∧ Timed p n c d

theorem TimedLe.refl {t s : ℕ} (p : Machine t s) (c : Configuration t s) : TimedLe p 0 c c :=
  ⟨0, le_rfl, Timed.refl p c⟩

theorem TimedLe.trans {t s B1 B2 : ℕ} {p : Machine t s} {c d e : Configuration t s}
    (h1 : TimedLe p B1 c d) (h2 : TimedLe p B2 d e) : TimedLe p (B1 + B2) c e := by
  obtain ⟨n1, hn1, t1⟩ := h1
  obtain ⟨n2, hn2, t2⟩ := h2
  exact ⟨n1 + n2, Nat.add_le_add hn1 hn2, t1.trans t2⟩

theorem TimedLe.mono {t s B B' : ℕ} {p : Machine t s} {c d : Configuration t s}
    (h : TimedLe p B c d) (hB : B ≤ B') : TimedLe p B' c d := by
  obtain ⟨n, hn, t⟩ := h
  exact ⟨n, hn.trans hB, t⟩

theorem TimedLe.single {t s : ℕ} {p : Machine t s} {c d : Configuration t s}
    (hn : p.halted c.control = false) (hs : LocalBitMultitape.step p c = some d) : TimedLe p 1 c d :=
  ⟨1, le_rfl, Timed.single hn hs⟩

theorem TimedLe.toStep {t s B : ℕ} {p : Machine t s} {H H' : Fin t → ℕ} {A A' : Fin t → List Bool}
    {q : Fin s} (h : TimedLe p B ⟨p.start, H, A⟩ ⟨q, H', A'⟩) (hq : p.halted q = true) :
    Step p B H A H' A' := by
  obtain ⟨n, hn, ht⟩ := h
  obtain ⟨r, hr, hf, _⟩ := ht.run hq
  exact (Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)).enlarge hn

/-! ## Reading unary words and appending -/

theorem word_read (P k : ℕ) : readTapeBit (CompareMachine.word P) k = decide (1 ≤ k ∧ k ≤ P) := by
  rcases k with _ | k
  · rfl
  · simp only [readTapeBit, CompareMachine.word, List.getD_cons_succ]
    by_cases h : k < P
    · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_replicate]
      symm
      rw [decide_eq_true_iff]
      omega
    · rw [List.getD_eq_default _ _ (by simp only [List.length_replicate]; omega)]
      symm
      rw [decide_eq_false_iff_not]
      omega

/-! ## One step on a whole group -/

/-! ## Rewinding a group to its marker -/

/-- The marker `[true]` reads `true` only at the left end. -/
theorem marker_read (k : ℕ) (hk : 1 ≤ k) : readTapeBit [true] k = false := by
  rcases k with _ | k
  · omega
  · rfl

/-! ## Appending one bit to an output tape -/

/-! ## Rewinding a residue register -/

/-! ## Unary segments -/

end NearCubicWires.PacketsCombine.Tab

