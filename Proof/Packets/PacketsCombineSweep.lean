import Proof.Packets.PacketsCombineSymEngine

/-! # P2 (iii) kit core: the bit-filtered product sweep (one radix-row tuple's conjunction)

Consumer: `ThrCombineStageK.run` (`Proof/Packets/PacketsRowPolySplitKit.lean`). By `rfl`
(`PacketsRowPolyPlan.thr_rowPoly`) the THR row polynomial is
`Normalized.structuralGF2ModularRadixRow p residue 2 coord`, whose accepted tuple `t` contributes
`structuralGF2FiniteConjunction (fun d => coord d (t d)) = foldr Ring.mul [[]] [coord 0 (t 0), …]`.
With the coordinate bank digit-major/candidate-minor (`coordsList`, `Proof/Packets/PacketsKitSeam.lean`), entry
`d*m + t d` is `coord d (t d)`; a descending sweep over the bank that multiplies exactly at the
positions whose selection bit is set therefore computes that product in the frozen order.
Paper: A.13.7 (`paper.tex:3113-3142`) — tuples are internal preprocessing; the row's canonical
polynomial expansion is charged in `T_prep` (`paper.tex:1197-1200`). Budget: source-polynomial.

REUSED machines: `SelectedFactorStep.move` (bit cursor), `SelectedPairFetch.retreat/fetch`,
`OrderedPacketStep.multiply`, `PhysicalBitCall.machine` (the bit decides whether the fetch and
multiply run at all: a skipped position must leave the accumulator's list untouched, because
`mul [[]] acc` is NOT `acc` as a list), `PhysicalRepeatStep` (the loop).
-/
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

/-! ## Semantics -/

/-- One filtered step at bank position `p` (selection bit at `base + p`). -/
def fstep (ps : List Poly) (bits : List Bool) (base p : ℕ) (acc : Poly) : Poly :=
  if bits.getD (base + p) false then Ring.mul (ps.getD p []) acc else acc

/-- The accumulator after the top `n` positions of `[0, K)` (descending). -/
def sweepAcc (ps : List Poly) (bits : List Bool) (base K : ℕ) (acc0 : Poly) (n : ℕ) : Poly :=
  ((List.range K).drop (K - n)).foldr (fstep ps bits base) acc0

/-- The left register after the top `n` positions. -/
def sweepLeft (ps : List Poly) (bits : List Bool) (base K : ℕ) (left0 : Poly) : ℕ → Poly
  | 0 => left0
  | n + 1 => if bits.getD (base + (K - (n + 1))) false then ps.getD (K - (n + 1)) []
      else sweepLeft ps bits base K left0 n

theorem sweepAcc_zero (ps : List Poly) (bits : List Bool) (base K : ℕ) (acc0 : Poly) :
    sweepAcc ps bits base K acc0 0 = acc0 := by
  unfold sweepAcc
  rw [Nat.sub_zero, List.drop_of_length_le (by simp)]
  rfl

theorem sweepAcc_succ (ps : List Poly) (bits : List Bool) (base K : ℕ) (acc0 : Poly) (n : ℕ) (hn : n < K) :
    sweepAcc ps bits base K acc0 (n + 1) =
      fstep ps bits base (K - (n + 1)) (sweepAcc ps bits base K acc0 n) := by
  unfold sweepAcc
  have hk : K - (n + 1) < (List.range K).length := by simp; omega
  rw [List.drop_eq_getElem_cons hk, List.foldr_cons, List.getElem_range]
  have he : K - (n + 1) + 1 = K - n := by omega
  rw [he]

/-! ## The filtered step machine -/

noncomputable def fmulCall := Composition.machine SelectedPairFetch.fetch SelectedFactorStep.multiply
noncomputable def fmulBody := Composition.machine SelectedFactorStep.move
  (Composition.machine SelectedPairFetch.retreat (PhysicalBitCall.machine (37 : Fin 38) fmulCall))
def fmulBudget (C w : ℕ) : ℕ := 160 * (commonReserve C w + 1) ^ 2

theorem fmul_run (C w j pos : ℕ) (ps : List Poly) (left acc : Poly) (bits : List Bool)
    (hj : j < ps.length) (hR : j + 2 ≤ commonReserve C w) (hl : left.length ≤ 2 ^ w)
    (hps : ∀ P ∈ ps, P.length ≤ 2 ^ w) (hp : Fits C (ps.getD j [])) (ha : Fits C acc)
    (hc : acc.length ≤ 2 ^ w) (hw : 1 ≤ w) :
    Step fmulBody (fmulBudget C w) (SelectedPairFetch.H (pos + 1))
      (SelectedPairFetch.A C (commonReserve C w) (j + 1) left acc ps bits) (SelectedPairFetch.H pos)
      (SelectedPairFetch.A C (commonReserve C w) j (if bits.getD pos false then ps.getD j [] else left)
        (if bits.getD pos false then Ring.mul (ps.getD j []) acc else acc) ps bits) := by
  have one := SelectedFactorStep.move_run C (commonReserve C w) (j + 1) pos left acc ps bits
  have two := SelectedPairFetch.retreat_run C (commonReserve C w) j pos left acc ps bits hR
  have hge : ps.getD j [] = ps[j] := List.getD_eq_getElem _ _ hj
  have hn : (ps.getD j []).length ≤ 2 ^ w := by rw [hge]; exact hps _ (List.getElem_mem hj)
  have small : ArithmeticLookup.budget (commonReserve C w) j + 1 + ReusableArithmetic.boundedBudget C w + 3 +
      (2 * j + 4) + 4 ≤ fmulBudget C w := by
    unfold fmulBudget ArithmeticLookup.budget PacketBank.lookupBudget ReusableArithmetic.boundedBudget
    have hm := Nat.mul_le_mul_right (commonReserve C w) (show j ≤ commonReserve C w by omega)
    nlinarith
  cases hb : bits.getD pos false with
  | false =>
    have three := PhysicalBitCall.run_false (p := fmulCall) (37 : Fin 38) (SelectedPairFetch.H pos)
      (SelectedPairFetch.A C (commonReserve C w) j left acc ps bits) hb
    have all := one.seq (two.seq three)
    exact all.enlarge (by omega)
  | true =>
    have f := SelectedPairFetch.fetch_run C w pos ps ⟨j, hj⟩ left acc bits hl hps
    have m := (OrderedPacketStep.multiply_run C w j (ps.getD j []) acc ps hp ha hn hc hw).embed
      (fun _ : Fin 1 => pos) (fun _ : Fin 1 => bits)
    dsimp only at f
    rw [← hge] at f
    have call := f.seq m
    have hb' : readTapeBit ((SelectedPairFetch.A C (commonReserve C w) j left acc ps bits) 37)
        ((SelectedPairFetch.H pos) 37) = true := hb
    have three := PhysicalBitCall.run_true (37 : Fin 38) (p := fmulCall) hb' call
    have all := one.seq (two.seq three)
    exact all.enlarge (by omega)

/-! ## The sweep -/

noncomputable def sweepM := RepeatMachine.machine fmulBody (fun _ _ => true)

/-- **The sweep.** From index `K` and bit cursor `base+K`, the accumulator runs through
`sweepAcc` and ends at `foldr fstep acc0 (range K)`; index `0`, bit cursor `base`. Bounds on every
intermediate accumulator are a hypothesis (the caller knows the selection structure). -/
theorem sweep_run (C w : ℕ) (S : Finset ℕ) (d : ℕ) (ps : List Poly) (bits : List Bool)
    (base K : ℕ) (left0 acc0 : Poly)
    (hS : ∀ j ∈ S, j < C) (hps : ∀ P ∈ ps, NormalizedIntermediate.Bounded S d P)
    (hfit : (S.card + 1) ^ d ≤ 2 ^ w) (hK : K ≤ ps.length) (hN : ps.length ≤ 2 ^ w)
    (hl0 : left0.length ≤ 2 ^ w)
    (hacc : ∀ n, n ≤ K → Fits C (sweepAcc ps bits base K acc0 n) ∧
      (sweepAcc ps bits base K acc0 n).length ≤ 2 ^ w) (hw : 1 ≤ w) :
    Step sweepM (K * (fmulBudget C w + 3) + 3)
      (TranscriptColumnLookupFold.H (base + K))
      (TranscriptColumnLookupFold.A C (commonReserve C w) K K left0 acc0 ps bits)
      (TranscriptColumnLookupFold.H base)
      (TranscriptColumnLookupFold.A C (commonReserve C w) 0 K (sweepLeft ps bits base K left0 K)
        (sweepAcc ps bits base K acc0 K) ps bits) := by
  have hcap := OrderedPacketFold.driver_fit C w ps.length hN
  have hpsc : ∀ P ∈ ps, P.length ≤ 2 ^ w :=
    fun P hP => (NormalizedIntermediate.census (hps P hP)).trans hfit
  have hleft : ∀ n, (sweepLeft ps bits base K left0 n).length ≤ 2 ^ w := by
    intro n
    induction n with
    | zero => exact hl0
    | succ n ih =>
      simp only [sweepLeft]
      split
      · by_cases h : K - (n + 1) < ps.length
        · rw [List.getD_eq_getElem _ _ h]
          exact hpsc _ (List.getElem_mem h)
        · rw [List.getD_eq_default _ _ (by omega)]
          simp
      · exact ih
  let hs : ℕ → Fin 38 → ℕ := fun n => SelectedPairFetch.H (base + (K - n))
  let as : ℕ → Fin 38 → List Bool := fun n => SelectedPairFetch.A C (commonReserve C w) (K - n)
    (sweepLeft ps bits base K left0 n) (sweepAcc ps bits base K acc0 n) ps bits
  have body : ∀ n, n < K → Step fmulBody (fmulBudget C w) (hs n) (as n) (hs (n + 1)) (as (n + 1)) := by
    intro n hn
    let j := K - (n + 1)
    have hj : j < ps.length := by dsimp only [j]; omega
    have hP : Fits C (ps.getD j []) := by
      rw [List.getD_eq_getElem _ _ hj]
      exact SubstitutionCensus.fits_of_bounded C S hS (hps _ (List.getElem_mem hj))
    have run := fmul_run C w j (base + j) ps (sweepLeft ps bits base K left0 n)
      (sweepAcc ps bits base K acc0 n) bits hj (by dsimp only [j]; omega) (hleft n) hpsc hP
      (hacc n (by omega)).1 (hacc n (by omega)).2 hw
    have e1 : K - n = j + 1 := by dsimp only [j]; omega
    have e2 : base + (K - n) = base + j + 1 := by dsimp only [j]; omega
    dsimp only [hs, as]
    rw [e2, e1, sweepAcc_succ ps bits base K acc0 n hn]
    have hl1 : sweepLeft ps bits base K left0 (n + 1) =
        if bits.getD (base + j) false then ps.getD j [] else sweepLeft ps bits base K left0 n := rfl
    rw [hl1]
    exact run
  have result := PhysicalRepeatStep.run fmulBody K (fmulBudget C w) hs as body
  dsimp only [hs, as] at result
  rw [Nat.sub_zero, Nat.sub_self, show base + 0 = base from Nat.add_zero base, sweepAcc_zero] at result
  exact result

end
end NearCubicWires.PacketsCombine
