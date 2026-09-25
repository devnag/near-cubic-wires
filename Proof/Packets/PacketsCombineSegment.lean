import Proof.Packets.PacketsXTranscriptColumnLookupFold

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsCombine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open NormalizedFiniteTransport Theorem25Completion.CycleBounds
noncomputable section

abbrev Poly := Ring.Poly ℕ

/-- The terms of the segment `[base, base+N)`: local candidate `i` contributes `ps[base+i]` when
bit `base+i` is set, and the zero polynomial otherwise. -/
def segTerms (ps : List Poly) (bits : List Bool) (base N : ℕ) : List Poly :=
  List.ofFn (fun i : Fin N =>
    TranscriptColumnLookupMeaning.term (ps.getD (base + i.val) []) (bits.getD (base + i.val) false))

theorem segTerms_length (ps : List Poly) (bits : List Bool) (base N : ℕ) :
    (segTerms ps bits base N).length = N := by
  simp only [segTerms, List.length_ofFn]

theorem segTerms_get (ps : List Poly) (bits : List Bool) (base N i : ℕ) (hi : i < N) :
    (segTerms ps bits base N).getD i [] =
      TranscriptColumnLookupMeaning.term (ps.getD (base + i) []) (bits.getD (base + i) false) := by
  rw [List.getD_eq_getElem _ _ (by simpa only [segTerms_length] using hi)]
  simp only [segTerms, List.getElem_ofFn]

theorem segTerms_bounded (S : Finset ℕ) (d : ℕ) (ps : List Poly) (bits : List Bool) (base N : ℕ)
    (hps : ∀ P ∈ ps, NormalizedIntermediate.Bounded S d P) :
    ∀ P ∈ segTerms ps bits base N, NormalizedIntermediate.Bounded S d P := by
  intro P hP
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hP
  unfold TranscriptColumnLookupMeaning.term
  split
  · by_cases h : base + i.val < ps.length
    · rw [List.getD_eq_getElem _ _ h]
      exact hps _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact NormalizedIntermediate.zero S d
  · exact NormalizedIntermediate.zero S d

/-- **The segment fold.** From index `base+N` (bit head `base+N`, empty accumulator, driver `N`),
the reused lookup-fold machine leaves the accumulator equal to the ordered parity of the segment's
terms, the index and bit head at `base`, and the bank, bits and driver unchanged. -/
theorem segment_run (C w : ℕ) (S : Finset ℕ) (d : ℕ) (ps : List Poly) (old : Poly)
    (bits : List Bool) (base N : ℕ)
    (hS : ∀ j ∈ S, j < C) (hps : ∀ P ∈ ps, NormalizedIntermediate.Bounded S d P)
    (hfit : (S.card + 1) ^ d ≤ 2 ^ w) (hseg : base + N ≤ ps.length) (hN : ps.length ≤ 2 ^ w)
    (ho : old.length ≤ 2 ^ w) (hw : 1 ≤ w) :
    Step TranscriptColumnLookupFold.machine (TranscriptColumnLookupFold.budget C w N)
      (TranscriptColumnLookupFold.H (base + N))
      (TranscriptColumnLookupFold.A C (commonReserve C w) (base + N) N old [] ps bits)
      (TranscriptColumnLookupFold.H base)
      (TranscriptColumnLookupFold.A C (commonReserve C w) base N
        (OrderedPacketFold.last (segTerms ps bits base N) old N)
        ((segTerms ps bits base N).foldr Ring.add []) ps bits) := by
  let fs := segTerms ps bits base N
  have hf : fs.length = N := segTerms_length ps bits base N
  have hfb := segTerms_bounded S d ps bits base N hps
  have hc : ∀ P ∈ fs, P.length ≤ 2 ^ w :=
    fun P hP => (NormalizedIntermediate.census (hfb P hP)).trans hfit
  have hcap := OrderedPacketFold.driver_fit C w ps.length hN
  let hs : ℕ → Fin 38 → ℕ := fun n => SelectedPairFetch.H (base + (N - n))
  let as : ℕ → Fin 38 → List Bool := fun n => SelectedPairFetch.A C (commonReserve C w)
    (base + (N - n)) (OrderedPacketFold.last fs old n) (OrderedPacketFold.value Ring.add fs [] n) ps bits
  have body : ∀ n, n < N → Step TranscriptColumnLookupBody.machine (TranscriptColumnLookupBody.budget C w)
      (hs n) (as n) (hs (n + 1)) (as (n + 1)) := by
    intro n hn
    let i := base + (N - (n + 1))
    have hi : i < ps.length := by dsimp only [i]; omega
    have hP : NormalizedIntermediate.Bounded S d (ps.getD i []) := by
      rw [List.getD_eq_getElem _ _ hi]
      exact hps _ (List.getElem_mem hi)
    have hAcc := NormalizedIntermediate.parity_prefix fs hfb n
    have run := TranscriptColumnLookupBody.run C w i ps
      (OrderedPacketFold.last fs old n) (OrderedPacketFold.value Ring.add fs [] n) bits
      (bits.getD i false) rfl hi (by dsimp only [i]; omega)
      (OrderedPacketFold.last_count fs old (2 ^ w) n ho hc)
      (fun P hP => (NormalizedIntermediate.census (hps P hP)).trans hfit)
      (SubstitutionCensus.fits_of_bounded C S hS hP)
      (SubstitutionCensus.fits_of_bounded C S hS hAcc) hP.1.1 hAcc.1.1
      ((NormalizedIntermediate.census hAcc).trans hfit) hw
    have hg : (if bits.getD i false then ps.getD i [] else []) = fs.getD (N - (n + 1)) [] := by
      rw [segTerms_get ps bits base N (N - (n + 1)) (by omega)]
      rfl
    dsimp only at run
    rw [hg] at run
    have hn' : n < fs.length := by omega
    have hlast : OrderedPacketFold.last fs old (n + 1) = fs.getD (N - (n + 1)) [] := by
      simp only [OrderedPacketFold.last, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, hf]
    have hval := OrderedPacketFold.value_succ Ring.add fs [] n hn'
    rw [hf] at hval
    dsimp only [hs, as]
    rw [hlast, hval]
    have e1 : base + (N - n) = i + 1 := by dsimp only [i]; omega
    rw [e1]
    exact run
  have result := PhysicalRepeatStep.run TranscriptColumnLookupBody.machine N
    (TranscriptColumnLookupBody.budget C w) hs as body
  dsimp only [hs, as] at result
  have hv : OrderedPacketFold.value Ring.add fs [] N = fs.foldr Ring.add [] := by
    have h := OrderedPacketFold.value_complete Ring.add fs []
    rw [hf] at h
    exact h
  have hl0 : OrderedPacketFold.last fs old 0 = old := by simp [OrderedPacketFold.last]
  have hv0 : OrderedPacketFold.value Ring.add fs [] 0 = [] := by simp [OrderedPacketFold.value]
  rw [hv, hl0, hv0, Nat.sub_zero, Nat.sub_self, show base + 0 = base from Nat.add_zero base] at result
  exact result

end
end NearCubicWires.PacketsCombine
