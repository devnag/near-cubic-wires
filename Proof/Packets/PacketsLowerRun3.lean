import Proof.Packets.PacketsLowerRun2

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.LowerCore
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairRepresentation
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
noncomputable section

theorem join_heads (j : Fin 58) : MajorityComplete.PacketAtomsJoin.heads j = if j.val = 33 then 1 else 0 := by
  fin_cases j <;> rfl

theorem template_word (n : ℕ) : UnaryTemplate.tape n = CompareMachine.word n ++ [false] := by
  simp [UnaryTemplate.tape, CompareMachine.word]

theorem pad_word_zero (Rb R : ℕ) (hR : 1 ≤ R) (h : R ≤ Rb) :
    ZeroPadding.pad Rb (ZeroPadding.pad R (CompareMachine.word 0)) = ZeroPadding.pad Rb [] := by
  rw [Dock.pad_monotone R Rb _ h]
  exact Dock.pad_zeros Rb 1 (by omega)

theorem pad_snoc_false (Rb : ℕ) (x : List Bool) (h : x.length + 1 ≤ Rb) :
    ZeroPadding.pad Rb (x ++ [false]) = ZeroPadding.pad Rb x :=
  Dock.pad_append_zeros Rb 1 x h

theorem cache_eq {q : ℕ} (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupplierPipeline.SupportedNormalizedGate q)) :
    CloseoutRowsRawPairSeek.cacheWord (RepairSource.CloseoutRowsUniversal.pairs a live occ) =
      CloseoutRowsRawAtomBatch.atoms 0 (ExtDecompositionBatch.counts a (RepairSource.CloseoutRowsUniversal.pool live occ)) :=
  (RepairSource.CloseoutRowsUniversal.pairs_word a live occ).trans (CloseoutRowsRawAtomCache.source_word a _)

theorem arith_slot (i : Fin 34) : (Fin.castAdd 12 (MajorityComplete.PacketAtoms.arithmeticSlots i)).val =
    if i.val < 30 then i.val else i.val + 2 := by
  simp only [Fin.val_castAdd, MajorityComplete.PacketAtoms.arithmeticSlots]
  split_ifs <;> rfl

variable {q L : ℕ} (a : DecompositionAlgorithm) (F : Packets.Family q L) (row : Packets.Row F.occurrences L)

/-- **Stage 7: the join.** -/
theorem stage7 (Rb C w : ℕ) (input : List Bool) (H : Fin 302 → ℕ) (A : Fin 302 → List Bool)
    (hC : 1 ≤ C) (hocc : F.occurrences.length ≤ C) (hchild : MajorityComplete.PacketMeaning.childCount a F ≤ C) (hw : 1 ≤ w)
    (hfit : (MajorityComplete.PacketMeaning.childCount a F + 1) ^ row.degree ≤ 2 ^ w)
    (hfitAtom : MajorityComplete.PacketMeaning.childCount a F + 1 ≤ 2 ^ w)
    (hP : SubstitutionInvariant.Good C row.polynomial) (hdeg : Ring.Degree row.degree row.polynomial)
    (hcount : row.polynomial.length ≤ 2 ^ w)
    (hRb : PolyKit.reserve C w ≤ Rb) (hpop : F.occurrences.length + 2 ≤ Rb)
    (f : Facts6 Rb C w F.occurrences.length input
      (PacketVector.entry (PolyKit.reserve C w) (row.polynomial.map (NormalizedFiniteTransport.maskNat C)))
      (CloseoutRowsRawAtomBatch.atoms 0
        (ExtDecompositionBatch.counts a (RepairSource.CloseoutRowsUniversal.pool (Packets.live F) F.occurrences)))
      (row.polynomial.map (NormalizedFiniteTransport.maskNat C)) H A) :
    ∃ (H' : Fin 302 → ℕ) (A' : Fin 302 → List Bool),
      Step joinStep (MajorityComplete.PacketAtomsJoin.budget C (PolyKit.reserve C w) F.occurrences.length
        row.polynomial (Packets.lowered a F row)) H A H' A' ∧
      A' 0 = input ∧ H' 0 = 0 ∧
      A' 1 = ZeroPadding.pad Rb (PacketVector.entry (PolyKit.reserve C w)
        (row.polynomial.map (NormalizedFiniteTransport.maskNat C))) ∧ H' 1 = 0 ∧
      A' 2 = ZeroPadding.pad Rb (ExtIncidence.stream (Ring.norm (Packets.lowered a F row))) ∧ H' 2 = 0 := by
  obtain ⟨fa0, fh0, fa1, fh1, fa2, fh2, fa6, fh6, farena, fa278, fh278, fa288, fh288, fa289, fh289, ffree⟩ := f
  have hres : PolyKit.reserve C w = Theorem25Completion.CycleBounds.commonReserve C w := rfl
  rw [hres] at fa1 farena fa288 fa289 hRb ⊢
  set R := Theorem25Completion.CycleBounds.commonReserve C w with hRdef
  have hR1 : 1 ≤ R := by
    rw [hRdef]; unfold Theorem25Completion.CycleBounds.commonReserve
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have run := MajorityComplete.PacketAtomsJoin.run C w a F row hC hocc hchild hw hfit hfitAtom hP hdeg hcount
  have fresh : ∀ (j : Fin 58) (i : Fin 302), joinSlots j = i → 242 ≤ i.val → i.val ≠ 278 → i.val ≠ 288 →
      i.val ≠ 289 → i.val ≠ 300 → i.val ≠ 301 → A (joinSlots j) = ZeroPadding.pad Rb [] ∧ H (joinSlots j) = 0 := by
    intro j i h h1 h2 h3 h4 h5 h6
    rw [h]; exact ffree i h1 h2 h3 h4 h5 h6
  obtain ⟨H', A', st, o, kp⟩ := Dock.lift run joinSlots joinSlots_injective (fun _ => Rb) H A (by
    intro j
    have hv := joinSlots_val j
    have hj58 := j.isLt
    rw [join_heads]
    by_cases hlo : j.val < 30
    · -- arena, low part
      have ea : joinSlots j = arenaTape ⟨j.val, by omega⟩ :=
        Fin.ext (by rw [hv, arenaTape_val]; simp [hlo]; omega)
      have ej : j = Fin.castAdd 12 (MajorityComplete.PacketAtoms.arithmeticSlots ⟨j.val, by omega⟩) :=
        Fin.ext (by rw [arith_slot]; simp [hlo])
      rw [ea, (farena _).1, (farena _).2]
      refine ⟨?_, ?_⟩
      · unfold ReusableArithmetic.heads
        rw [if_neg (fun e => by have := congrArg Fin.val e; simp at this; omega), if_neg (by omega)]
      · conv_rhs => rw [ej, LowerWords.join_arena C R _ _ hR1]
    by_cases hmid : 32 ≤ j.val ∧ j.val ≤ 35
    · have ea : joinSlots j = arenaTape ⟨j.val - 2, by omega⟩ :=
        Fin.ext (by rw [hv, arenaTape_val]; dsimp only; split_ifs <;> omega)
      have ej : j = Fin.castAdd 12 (MajorityComplete.PacketAtoms.arithmeticSlots ⟨j.val - 2, by omega⟩) :=
        Fin.ext (by rw [arith_slot]; dsimp only; split_ifs <;> omega)
      rw [ea, (farena _).1, (farena _).2]
      refine ⟨?_, ?_⟩
      · unfold ReusableArithmetic.heads
        by_cases h33 : j.val = 33
        · rw [if_pos (Fin.ext (by simp; omega)), if_pos h33]
        · rw [if_neg (fun e => h33 (by have := congrArg Fin.val e; simp at this; omega)), if_neg h33]
      · conv_rhs => rw [ej, LowerWords.join_arena C R _ _ hR1]
    by_cases h36 : j.val = 36
    · obtain rfl : j = 36 := Fin.ext h36
      have e : joinSlots 36 = 278 := Fin.ext (by rw [joinSlots_val]; rfl)
      rw [e, fa278, fh278, LowerWords.join_36, Dock.pad_monotone R Rb _ hRb, cache_eq]
      exact ⟨rfl, rfl⟩
    by_cases h45 : j.val = 45
    · obtain rfl : j = 45 := Fin.ext h45
      have e : joinSlots 45 = 6 := Fin.ext (by rw [joinSlots_val]; rfl)
      rw [e, fa6, fh6, LowerWords.join_45, Dock.pad_monotone R Rb _ hRb, template_word,
        pad_snoc_false Rb _ (by simp [CompareMachine.word]; omega),
        RepairSource.CloseoutRowsUniversal.pairs_length]
      exact ⟨rfl, rfl⟩
    by_cases h46 : j.val = 46
    · obtain rfl : j = 46 := Fin.ext h46
      have e : joinSlots 46 = 288 := Fin.ext (by rw [joinSlots_val]; rfl)
      rw [e, fa288, fh288, LowerWords.join_46]
      exact ⟨rfl, rfl⟩
    by_cases h47 : j.val = 47
    · obtain rfl : j = 47 := Fin.ext h47
      have e : joinSlots 47 = 289 := Fin.ext (by rw [joinSlots_val]; rfl)
      rw [e, fa289, fh289, LowerWords.join_47]
      exact ⟨rfl, rfl⟩
    by_cases h57 : j.val = 57
    · obtain rfl : j = 57 := Fin.ext h57
      have e : joinSlots 57 = 2 := Fin.ext (by rw [joinSlots_val]; rfl)
      rw [e, fa2, fh2, LowerWords.join_57]
      exact ⟨rfl, rfl⟩
    -- every other join tape is fresh scratch holding an all-false entry word
    have hval : (joinSlots j).val = 242 + j.val := by
      rw [hv]; split_ifs <;> omega
    have hf := fresh j (joinSlots j) rfl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [hf.1, hf.2]
    refine ⟨by simp; omega, ?_⟩
    have hcase : j.val = 30 ∨ j.val = 31 ∨ (37 ≤ j.val ∧ j.val ≤ 44) ∨ (48 ≤ j.val ∧ j.val ≤ 56) := by omega
    rcases hcase with h | h | h | h
    · obtain rfl : j = 30 := Fin.ext h
      rw [LowerWords.join_30, Dock.pad_zeros Rb R hRb]
    · obtain rfl : j = 31 := Fin.ext h
      rw [LowerWords.join_31, Dock.pad_zeros Rb R hRb]
    · have hc : j.val = 37 ∨ j.val = 38 ∨ j.val = 39 ∨ j.val = 40 ∨ j.val = 41 ∨ j.val = 42 ∨ j.val = 43 ∨
          j.val = 44 := by omega
      rcases hc with h | h | h | h | h | h | h | h
      · obtain rfl : j = 37 := Fin.ext h; rw [LowerWords.join_37, Dock.pad_zeros Rb R hRb]
      · obtain rfl : j = 38 := Fin.ext h; rw [LowerWords.join_38, Dock.pad_zeros Rb R hRb]
      · obtain rfl : j = 39 := Fin.ext h; rw [LowerWords.join_39, Dock.pad_zeros Rb R hRb]
      · obtain rfl : j = 40 := Fin.ext h; rw [LowerWords.join_40]
      · obtain rfl : j = 41 := Fin.ext h; rw [LowerWords.join_41, pad_word_zero Rb R hR1 hRb]
      · obtain rfl : j = 42 := Fin.ext h; rw [LowerWords.join_42]
      · obtain rfl : j = 43 := Fin.ext h; rw [LowerWords.join_43, Dock.pad_zeros Rb R hRb]
      · obtain rfl : j = 44 := Fin.ext h; rw [LowerWords.join_44, pad_word_zero Rb R hR1 hRb]
    · have hc : j.val = 48 ∨ j.val = 49 ∨ j.val = 50 ∨ j.val = 51 ∨ j.val = 52 ∨ j.val = 53 ∨ j.val = 54 ∨
          j.val = 55 ∨ j.val = 56 := by omega
      rcases hc with h | h | h | h | h | h | h | h | h
      · obtain rfl : j = 48 := Fin.ext h; rw [LowerWords.join_48]
      · obtain rfl : j = 49 := Fin.ext h; rw [LowerWords.join_49]
      · obtain rfl : j = 50 := Fin.ext h; rw [LowerWords.join_50]
      · obtain rfl : j = 51 := Fin.ext h; rw [LowerWords.join_51]
      · obtain rfl : j = 52 := Fin.ext h; rw [LowerWords.join_52]
      · obtain rfl : j = 53 := Fin.ext h; rw [LowerWords.join_53]
      · obtain rfl : j = 54 := Fin.ext h; rw [LowerWords.join_54]
      · obtain rfl : j = 55 := Fin.ext h; rw [LowerWords.join_55]
      · obtain rfl : j = 56 := Fin.ext h; rw [LowerWords.join_56])
  have keep : ∀ i : Fin 302, i.val < 2 → A' i = A i ∧ H' i = H i := by
    intro i hi
    have := kp i (joinSlots_ne i (by omega))
    exact ⟨this.2, this.1⟩
  have e57 : joinSlots 57 = 2 := Fin.ext (by rw [joinSlots_val]; rfl)
  have o57 := o 57
  rw [e57] at o57
  refine ⟨H', A', st, (keep 0 (by decide)).1.trans fa0, (keep 0 (by decide)).2.trans fh0,
    (keep 1 (by decide)).1.trans fa1, (keep 1 (by decide)).2.trans fh1, ?_, ?_⟩
  · rw [o57.2, MajorityComplete.PacketAtomsJoin.output_word]
  · rw [o57.1]; rfl

end
end NearCubicWires.PacketsConstruction.LowerCore
