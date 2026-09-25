import Proof.Packets.PacketsCombineTabMeta

/-! # P2 (iii) table writer, part 9: `UnaryTemplate.tape X` reads as `word X` (input adapter for the `ThrMeta` assembler)

Consumer: `PacketsCombineTabMeta.writer_thr`'s six inputs (`ReadsWord A X`). `ThrMeta` writes its templates of
`K = D*(pop+1)` (tapes 12, 13) and `N = (pop+1)^D` (tape 14) as `UnaryTemplate.tape`, and PG/PK stages write unary
values in the same codec; this lemma lets them feed the writer directly. Paper and budget: as `writer_thr` (no cost).
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsCombine.Tab
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary

theorem readsWord_template (X : ℕ) : ReadsWord (UnaryTemplate.tape X) X := by
  intro k
  rcases k with _ | k
  · rfl
  · simp only [readTapeBit, UnaryTemplate.tape, List.getD_cons_succ]
    by_cases h : k < X
    · rw [List.getD_append _ _ _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h),
        List.getElem_replicate]
      symm
      rw [decide_eq_true_iff]
      omega
    · rw [List.getD_append_right _ _ _ _ (by simp only [List.length_replicate]; omega)]
      simp only [List.length_replicate]
      rcases Nat.lt_or_ge (k - X) 1 with h1 | h1
      · rw [show k - X = 0 by omega]
        symm
        simp only [List.getD_cons_zero, decide_eq_false_iff_not]
        omega
      · rw [List.getD_eq_default _ _ (by simp only [List.length_singleton]; omega)]
        symm
        rw [decide_eq_false_iff_not]
        omega

end NearCubicWires.PacketsCombine.Tab

