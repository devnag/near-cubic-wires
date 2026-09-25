import Proof.Packets.PacketsLowerRun1

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

def Facts6 (Rb C w pop : ℕ) (input reg cache : List Bool) (m : List (List Bool))
    (H : Fin 302 → ℕ) (A : Fin 302 → List Bool) : Prop :=
  A 0 = input ∧ H 0 = 0 ∧ A 1 = ZeroPadding.pad Rb reg ∧ H 1 = 0 ∧ A 2 = ZeroPadding.pad Rb [] ∧ H 2 = 0 ∧
  A 6 = ZeroPadding.pad Rb (UnaryTemplate.tape pop) ∧ H 6 = 0 ∧
  (∀ i : Fin 34, A (arenaTape i) = ZeroPadding.pad Rb (ReusableArithmetic.state C (PolyKit.reserve C w) [] [] i) ∧
    H (arenaTape i) = ReusableArithmetic.heads i) ∧
  A 278 = ZeroPadding.pad Rb cache ∧ H 278 = 0 ∧
  A 288 = ZeroPadding.pad Rb (PacketVector.payload (PolyKit.reserve C w) m) ∧ H 288 = 0 ∧
  A 289 = ZeroPadding.pad Rb (PacketVector.count (PolyKit.reserve C w) m) ∧ H 289 = 0 ∧
  ∀ i : Fin 302, 242 ≤ i.val → i.val ≠ 278 → i.val ≠ 288 → i.val ≠ 289 → i.val ≠ 300 → i.val ≠ 301 →
    A i = ZeroPadding.pad Rb [] ∧ H i = 0

theorem state_31 (C R : ℕ) : ReusableArithmetic.state C R [] [] 31 = UnaryTemplate.tape R := rfl

theorem arenaTape_31 : arenaTape 31 = 209 := Fin.ext (by rw [arenaTape_val]; rfl)

/-- A move of the two driver heads 289/300, frame form. -/
theorem moves (d : HeadMove) (H : Fin 302 → ℕ) (A : Fin 302 → List Bool) :
    ∃ (H' : Fin 302 → ℕ) (A' : Fin 302 → List Bool), Step (moveStep d) 1 H A H' A' ∧
      H' 289 = d.apply (H 289) ∧ H' 300 = d.apply (H 300) ∧ (∀ i, A' i = A i) ∧
      ∀ i : Fin 302, i.val ≠ 289 → i.val ≠ 300 → H' i = H i := by
  obtain ⟨H', A', st, o, kp⟩ := Dock.lift (Completion.PhysicalDriverMoves.run d (fun k => H (moveSlots k))
    (fun k => A (moveSlots k))) moveSlots moveSlots_injective (fun _ => 0) H A
    (fun k => ⟨rfl, (ZeroPadding.pad_zero _).symm⟩)
  have e0 : moveSlots 0 = 289 := Fin.ext (by rw [moveSlots_val]; rfl)
  have e1 : moveSlots 1 = 300 := Fin.ext (by rw [moveSlots_val]; rfl)
  have o0 := o 0
  have o1 := o 1
  rw [e0] at o0
  rw [e1] at o1
  refine ⟨H', A', st, o0.1, o1.1, ?_, ?_⟩
  · intro i
    by_cases h : ∃ k, moveSlots k = i
    · obtain ⟨k, rfl⟩ := h
      rw [(o k).2, ZeroPadding.pad_zero]
    · have := kp i (fun k hk => h ⟨k, hk⟩)
      exact this.2
  · intro i h1 h2
    exact (kp i (moveSlots_ne i ⟨h1, h2⟩)).1

theorem stage456 (Rb C w pop : ℕ) (input cache : List Bool) (m : List (List Bool))
    (H : Fin 302 → ℕ) (A : Fin 302 → List Bool)
    (hfits : PacketVector.Fits (PolyKit.reserve C w) m) (h2R : 2 * PolyKit.reserve C w ≤ Rb)
    (f : Facts3 Rb C w pop input (PacketVector.entry (PolyKit.reserve C w) m) cache H A) :
    ∃ (H' : Fin 302 → ℕ) (A' : Fin 302 → List Bool),
      Step loadStep
        (1 + 1 + (PacketBank.lookupBudget (PolyKit.reserve C w) 0 + 1 + 1)) H A H' A' ∧
      Facts6 Rb C w pop input (PacketVector.entry (PolyKit.reserve C w) m) cache m H' A' := by
  obtain ⟨fa0, fh0, fa1, fh1, fa2, fh2, fa6, fh6, farena, fa278, fh278, ffree⟩ := f
  set R := PolyKit.reserve C w with hRdef
  have hR1 : 1 ≤ R := by
    rw [hRdef]; unfold PolyKit.reserve Theorem25Completion.CycleBounds.commonReserve
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hp := PacketVector.payload_length hfits
  have hc := PacketVector.count_length hfits
  -- moves right
  obtain ⟨H1, A1, s1, m289, m300, mA, mH⟩ := moves .right H A
  -- the lookup
  have look := PacketBank.lookup_run R 0 [] (PacketVector.payload R m) (PacketVector.count R m)
    (List.replicate (Rb - 2 * R) false) (List.replicate R false) (List.replicate R false)
    (by simp) hp hc (by simp) (by simp)
  have hbank : ZeroPadding.pad Rb (PacketVector.entry R m) =
      [] ++ PacketVector.payload R m ++ PacketVector.count R m ++ List.replicate (Rb - 2 * R) false := by
    unfold PacketVector.entry ZeroPadding.pad
    simp only [List.nil_append, List.length_append, hp, hc]
    congr 2
    omega
  obtain ⟨H2, A2, s2, o2, k2⟩ := Dock.lift look lookSlots lookSlots_injective
    (fun k => if k.val = 1 then 0 else Rb) H1 A1 (by
      intro k
      have hk6 := k.isLt
      by_cases h0 : k.val = 0
      · obtain rfl : k = 0 := Fin.ext h0
        have e : lookSlots 0 = arenaTape 31 := by rw [arenaTape_31]; exact Fin.ext (by rw [lookSlots_val]; rfl)
        rw [e, mH _ (by rw [arenaTape_31]; decide) (by rw [arenaTape_31]; decide), mA, (farena 31).1, (farena 31).2,
          state_31]
        exact ⟨rfl, rfl⟩
      by_cases h1 : k.val = 1
      · obtain rfl : k = 1 := Fin.ext h1
        have e : lookSlots 1 = 1 := Fin.ext (by rw [lookSlots_val]; rfl)
        rw [e, mH 1 (by decide) (by decide), mA, fa1, fh1]
        refine ⟨rfl, ?_⟩
        rw [if_pos (show ((1 : Fin 6) : ℕ) = 1 from rfl), ZeroPadding.pad_zero, hbank]; rfl
      by_cases h2 : k.val = 2
      · obtain rfl : k = 2 := Fin.ext h2
        have e : lookSlots 2 = 288 := Fin.ext (by rw [lookSlots_val]; rfl)
        rw [e, mH 288 (by decide) (by decide), mA, (ffree 288 (by decide) (by decide)).1,
          (ffree 288 (by decide) (by decide)).2]
        refine ⟨rfl, ?_⟩
        exact (Dock.pad_zeros Rb R (by omega)).symm
      by_cases h3 : k.val = 3
      · obtain rfl : k = 3 := Fin.ext h3
        have e : lookSlots 3 = 289 := Fin.ext (by rw [lookSlots_val]; rfl)
        rw [e, m289, mA, (ffree 289 (by decide) (by decide)).1, (ffree 289 (by decide) (by decide)).2]
        refine ⟨rfl, ?_⟩
        exact (Dock.pad_zeros Rb R (by omega)).symm
      by_cases h4 : k.val = 4
      · obtain rfl : k = 4 := Fin.ext h4
        have e : lookSlots 4 = 300 := Fin.ext (by rw [lookSlots_val]; rfl)
        rw [e, m300, mA, (ffree 300 (by decide) (by decide)).1, (ffree 300 (by decide) (by decide)).2]
        refine ⟨rfl, ?_⟩
        exact (Dock.pad_zeros Rb 1 (by omega)).symm
      · obtain rfl : k = 5 := Fin.ext (by omega)
        have e : lookSlots 5 = 301 := Fin.ext (by rw [lookSlots_val]; rfl)
        rw [e, mH 301 (by decide) (by decide), mA, (ffree 301 (by decide) (by decide)).1,
          (ffree 301 (by decide) (by decide)).2]
        exact ⟨rfl, rfl⟩)
  -- moves left
  obtain ⟨H3, A3, s3, n289, n300, nA, nH⟩ := moves .left H2 A2
  have keep2 : ∀ i : Fin 302,
      (i.val ≠ 209 ∧ i.val ≠ 1 ∧ i.val ≠ 288 ∧ i.val ≠ 289 ∧ i.val ≠ 300 ∧ i.val ≠ 301) →
      A2 i = A1 i ∧ H2 i = H1 i := by
    intro i hi
    have := k2 i (lookSlots_ne i hi)
    exact ⟨this.2, this.1⟩
  have o2at : ∀ (k : Fin 6) (i : Fin 302), lookSlots k = i →
      A2 i = ZeroPadding.pad (if k.val = 1 then 0 else Rb) (PacketBank.A R 0
        ([] ++ PacketVector.payload R m ++ PacketVector.count R m ++ List.replicate (Rb - 2 * R) false)
        (PacketVector.payload R m) (PacketVector.count R m) k) ∧ H2 i = PacketBank.H 0 1 k := by
    intro k i h
    rw [← h]
    exact ⟨(o2 k).2, (o2 k).1⟩
  refine ⟨H3, A3, s1.seq (s2.seq s3), ?_⟩
  have g : ∀ i : Fin 302, i.val ≠ 289 → i.val ≠ 300 → A3 i = A2 i ∧ H3 i = H2 i :=
    fun i h1 h2 => ⟨nA i, nH i h1 h2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(g 0 (by decide) (by decide)).1, (keep2 0 (by decide)).1, mA]; exact fa0
  · rw [(g 0 (by decide) (by decide)).2, (keep2 0 (by decide)).2, mH 0 (by decide) (by decide)]; exact fh0
  · rw [(g 1 (by decide) (by decide)).1, (o2at 1 1 (Fin.ext (by rw [lookSlots_val]; rfl))).1,
      if_pos (show ((1 : Fin 6) : ℕ) = 1 from rfl), ZeroPadding.pad_zero, hbank]; rfl
  · rw [(g 1 (by decide) (by decide)).2, (o2at 1 1 (Fin.ext (by rw [lookSlots_val]; rfl))).2]; rfl
  · rw [(g 2 (by decide) (by decide)).1, (keep2 2 (by decide)).1, mA]; exact fa2
  · rw [(g 2 (by decide) (by decide)).2, (keep2 2 (by decide)).2, mH 2 (by decide) (by decide)]; exact fh2
  · rw [(g 6 (by decide) (by decide)).1, (keep2 6 (by decide)).1, mA]; exact fa6
  · rw [(g 6 (by decide) (by decide)).2, (keep2 6 (by decide)).2, mH 6 (by decide) (by decide)]; exact fh6
  · intro i
    have hv := arenaTape_val i
    by_cases h31 : i = 31
    · subst h31
      rw [arenaTape_31, (g 209 (by decide) (by decide)).1, (g 209 (by decide) (by decide)).2,
        (o2at 0 209 (Fin.ext (by rw [lookSlots_val]; rfl))).1, (o2at 0 209 (Fin.ext (by rw [lookSlots_val]; rfl))).2,
        state_31]
      exact ⟨rfl, rfl⟩
    · have hi31 : i.val ≠ 31 := fun h => h31 (Fin.ext h)
      have hne : (arenaTape i).val ≠ 209 := by rw [hv]; split_ifs <;> omega
      have hsmall : (arenaTape i).val < 242 := by rw [hv]; split_ifs <;> omega
      have hbig : 174 ≤ (arenaTape i).val := by rw [hv]; split_ifs <;> omega
      rw [(g (arenaTape i) (by omega) (by omega)).1, (g (arenaTape i) (by omega) (by omega)).2,
        (keep2 (arenaTape i) ⟨hne, by omega, by omega, by omega, by omega, by omega⟩).1,
        (keep2 (arenaTape i) ⟨hne, by omega, by omega, by omega, by omega, by omega⟩).2,
        mA, mH (arenaTape i) (by omega) (by omega)]
      exact farena i
  · rw [(g 278 (by decide) (by decide)).1, (keep2 278 (by decide)).1, mA]; exact fa278
  · rw [(g 278 (by decide) (by decide)).2, (keep2 278 (by decide)).2, mH 278 (by decide) (by decide)]; exact fh278
  · rw [(g 288 (by decide) (by decide)).1, (o2at 2 288 (Fin.ext (by rw [lookSlots_val]; rfl))).1]; rfl
  · rw [(g 288 (by decide) (by decide)).2, (o2at 2 288 (Fin.ext (by rw [lookSlots_val]; rfl))).2]; rfl
  · rw [nA, (o2at 3 289 (Fin.ext (by rw [lookSlots_val]; rfl))).1]; rfl
  · rw [n289, (o2at 3 289 (Fin.ext (by rw [lookSlots_val]; rfl))).2]; rfl
  · intro i h242 h278 h288 h289 h300 h301
    rw [(g i h289 h300).1, (g i h289 h300).2, (keep2 i ⟨by omega, by omega, h288, h289, h300, h301⟩).1,
      (keep2 i ⟨by omega, by omega, h288, h289, h300, h301⟩).2, mA, mH i h289 h300]
    exact ffree i h242 h278

end
end NearCubicWires.PacketsConstruction.LowerCore
