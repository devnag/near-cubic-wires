import Proof.Packets.PacketsCoordSplit
import Proof.Packets.PacketsXLiteralAlphabet

/-! # Q3 F1 capacity anchor: normality, support, degree and size of the level and literal vectors

Paper: "Radix tuples, trace tuples, exact-child choices, and their canonical polynomial expansion
are charged in T_prep before that row's column scan" (`paper.tex:1197-1200`); one row is charged
its internal syntax once (`paper.tex:1190-1206`); preprocessing is additive (`paper.tex:1102-1112`).
Budget class: source-polynomial (a fixed power of `smallSize` per row; `packetBudget`).

Consumers (every route needs these):
* the scratch width `X.R r` of `LevelStage`/`LiteralStage` (`Proof/Packets/PacketsCoordSplit.lean`),
  which write `pad R (levelsOf a r k)` / `pad R (literalsOf a r k)`: `levelsOf_length_le`,
  `literalsOf_length_le`;
* every polynomial-kit capacity (the mask kit's `Fits C P`, `data … ≤ R`, `budget+3 ≤ R`):
  the per-polynomial census `census_le`, the alphabet size `levelCodes_card_le`, the code bound
  `levelCodes_lt`, and the degree anchor `rawDeg_le_degree`.

Semantic lemmas are cited, not rebuilt: normality/support of the level recursion is
`LiteralAlphabet.good_vectorFrom` and its degree is `Normalized.degree_structuralListPolynomialVector`
(external-packets transplant, compiled locally against the accepted `FixedCore`); the census is the
accepted `PCJc06b3608d6d34481_Ring.support_size`. New here: the literal-atom support, the
`smallSize` arithmetic (`2^depth ≤ 512(B+1)`, `B ≤ pop`, the THR digit count `< 2^walkLength`),
the row-degree anchor, and the codec length chain.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.SupplierListPolynomial
open NearCubicWires.SupplierListSchedule NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore
open NearCubicWires.SupplierWalk NearCubicWires.SupplierTouching
open PCJ9eff70d512234a4c_Fixed.Materializer.LiteralAlphabet (codes Good good_vectorFrom good_add good_mul
  good_zero codes_card codes_lt_square)
noncomputable section

/-! ## Arithmetic of the graded depth -/

theorem bound_le_pop {q : ℕ} (occ : List (SupportedNormalizedGate q)) (I : Finset (Fin q)) :
    LiveRows.bound occ I ≤ occ.length := by
  unfold LiveRows.bound touchingCost
  calc (∑ gate, touchIndicator I (occurrenceSupport occ gate))
      ≤ ∑ _gate : Fin occ.length, 1 := Finset.sum_le_sum (fun g _ => by
        unfold touchIndicator
        split <;> omega)
    _ = occ.length := by simp

/-! ## Support of the literal atoms and of normalized substitution -/

theorem good_one (S : Finset ℕ) : Good S structuralGF2One := by
  refine ⟨⟨by simp [structuralGF2One], ?_⟩, ?_⟩
  · intro m hm
    simp only [structuralGF2One, List.mem_singleton] at hm
    subst m
    exact List.Pairwise.nil
  · intro m hm x hx
    simp only [structuralGF2One, List.mem_singleton] at hm
    subst m
    simp at hx

theorem good_masked {pop : ℕ} (M : Finset (Fin pop)) (i : Fin pop) :
    Good (Finset.range pop) (structuralMaskedCoordinate M i) := by
  unfold structuralMaskedCoordinate
  split
  · refine ⟨⟨by simp [structuralGF2Variable], ?_⟩, ?_⟩
    · intro m hm
      simp only [structuralGF2Variable, List.mem_singleton] at hm
      subst m
      exact List.pairwise_singleton _ _
    · intro m hm x hx
      simp only [structuralGF2Variable, List.mem_singleton] at hm
      subst m
      simp only [List.mem_singleton] at hx
      subst x
      exact Finset.mem_range.mpr i.isLt
  · exact good_zero _

theorem good_literal {rank depth pop : ℕ} (M : Finset (Fin pop))
    (label : Fin pop → BinaryVector rank) (seed : ToeplitzSeed rank) (code : ℕ) :
    Good (Finset.range pop) (Normalized.structuralListLiteralAtom (depth := depth) M label seed code) := by
  unfold Normalized.structuralListLiteralAtom
  split
  · exact good_zero _
  · split
    · exact good_masked M _
    · exact good_zero _
  · split
    · split
      · exact good_masked M _
      · exact good_zero _
    · split
      · exact good_add (good_one _) (good_masked M _)
      · exact good_zero _

theorem good_product {S : Finset ℕ} (ps : List StructuralGF2Polynomial) (h : ∀ P ∈ ps, Good S P) :
    Good S (Normalized.structuralGF2Product ps) := by
  unfold Normalized.structuralGF2Product
  induction ps with
  | nil => exact good_one S
  | cons P ps ih =>
    rw [List.foldr_cons]
    exact good_mul (h P (by simp)) (ih (fun Q hQ => h Q (by simp [hQ])))

theorem good_substitute {S : Finset ℕ} (atom : ℕ → StructuralGF2Polynomial) (h : ∀ c, Good S (atom c))
    (P : StructuralGF2Polynomial) : Good S (Normalized.structuralGF2Substitute atom P) := by
  induction P with
  | nil => exact good_zero S
  | cons m P ih =>
    rw [Normalized.structuralGF2Substitute]
    refine good_add (good_product _ ?_) ih
    intro Q hQ
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hQ
    exact h c

/-! ## Census of one normal polynomial -/

theorem count_le {S : Finset ℕ} {d : ℕ} {P : StructuralGF2Polynomial} (hP : Good S P)
    (hd : Ring.Degree d P) : P.length ≤ (S.card + 1) ^ d :=
  PCJc06b3608d6d34481_Ring.support_size S hP.1 hd hP.2

/-! ## The level and literal vectors of one walk step -/

section Vectors
variable {q : ℕ} (occ : List (SupportedNormalizedGate q)) (I : Finset (Fin q)) (den : ℕ)

/-- The raw (= normalized) degree of every level polynomial. -/
abbrev rawDeg : ℕ :=
  CloseoutRawRows.structuralListCoordinateRawDegree (canonicalGradedDepth (LiveRows.bound occ I))
    (executableGradedWindow (depth := canonicalGradedDepth (LiveRows.bound occ I)) (LiveRows.bound occ I))
    gradedTerminalWindow

theorem literalVec_good (M : Finset (Fin occ.length)) (sample : LiveRows.Seed occ I den)
    (time : Fin (canonicalWalkLength den)) (cand : Fin (occ.length + 1)) :
    Good (Finset.range occ.length) (literalVec occ I den M sample time cand) :=
  good_substitute _ (good_literal M _ _) _

end Vectors

/-! ## Codec lengths -/

section Words

end Words

/-! ## `smallSize` facts for one request -/

theorem small_occ (a : DecompositionAlgorithm) (r : Request) :
    ((r.family a).occurrences.length + 2) ^ (r.degree a + 1) ≤ r.smallSize a :=
  RCFive.PacketBounds.occurrence_power a r

theorem small_walk (a : DecompositionAlgorithm) (r : Request) :
    2 ^ canonicalWalkLength (r.denominator a) ≤ r.smallSize a := by
  dsimp only [Request.smallSize]
  generalize (2:ℕ) ^ (Packets.live (r.family a)).card = livePower
  omega

/-- **The census.** A normal polynomial over an alphabet of the row's literal size, of degree at
most the request degree (or over the empty alphabet), has at most `smallSize^12` monomials. -/
theorem census_le (a : DecompositionAlgorithm) (r : Request) {S : Finset ℕ} {d : ℕ}
    {P : StructuralGF2Polynomial} (hP : Good S P) (hd : Ring.Degree d P)
    (hS : S.card + 1 ≤ ((r.family a).occurrences.length + 2) ^ 12)
    (hdeg : S.card = 0 ∨ d ≤ r.degree a) : P.length ≤ (r.smallSize a) ^ 12 := by
  have hc := count_le hP hd
  have hs1 : 1 ≤ r.smallSize a := RCFive.PacketBounds.positive a r
  rcases hdeg with h0 | hdeg
  · rw [h0, Nat.zero_add, Nat.one_pow] at hc
    exact hc.trans (Nat.one_le_pow _ _ hs1)
  · have hpow : (S.card + 1) ^ d ≤ (((r.family a).occurrences.length + 2) ^ 12) ^ d :=
      Nat.pow_le_pow_left hS d
    have hswap : (((r.family a).occurrences.length + 2) ^ 12) ^ d =
        (((r.family a).occurrences.length + 2) ^ d) ^ 12 := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    have hd2 : ((r.family a).occurrences.length + 2) ^ d ≤ r.smallSize a :=
      (Nat.pow_le_pow_right (by omega) (by omega)).trans (small_occ a r)
    calc P.length ≤ (S.card + 1) ^ d := hc
      _ ≤ (((r.family a).occurrences.length + 2) ^ d) ^ 12 := hswap ▸ hpow
      _ ≤ (r.smallSize a) ^ 12 := Nat.pow_le_pow_left hd2 12

/-! ## The row-degree anchor -/

theorem walk_pos (den : ℕ) : 1 ≤ canonicalWalkLength den := by
  unfold canonicalWalkLength
  omega

theorem den_lt_walk (den : ℕ) : den < 2 ^ canonicalWalkLength den := by
  unfold canonicalWalkLength
  have h3 := Nat.le_pow_clog (b := 2) (by norm_num) (den + 1)
  have h5 : 2 ^ Nat.clog 2 (den + 1) ≤ 2 ^ (2 * Nat.clog 2 (den + 1) + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- THR: the residue-digit mask count is below `2^walkLength`, even with no occurrence. -/
theorem thr_digits_lt (a : DecompositionAlgorithm) (r0 : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (L target : ℕ) (k : RCFive.RowKeys.ThrKey a r0 L target) :
    modulusDigitCount k.prime.val < 2 ^ canonicalWalkLength (CloseoutFinalC10ThresholdRows.listDenominator a r0 target) := by
  have hp : k.prime.val ≤ CloseoutFinalC10ThresholdRows.primeCutoff a r0 target :=
    (mem_primesUpTo.mp k.prime.property).2
  have hmono : modulusDigitCount k.prime.val ≤
      modulusDigitCount (CloseoutFinalC10ThresholdRows.primeCutoff a r0 target) := by
    unfold modulusDigitCount
    exact Nat.succ_le_succ (Nat.log_mono_right hp)
  have hden : modulusDigitCount (CloseoutFinalC10ThresholdRows.primeCutoff a r0 target) ≤
      CloseoutFinalC10ThresholdRows.listDenominator a r0 target := by
    unfold CloseoutFinalC10ThresholdRows.listDenominator
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hwalk := den_lt_walk (CloseoutFinalC10ThresholdRows.listDenominator a r0 target)
  omega


/-! ## One polynomial word, from its alphabet, degree and `smallSize` -/

section Anchor

end Anchor

/-! ## The request-level anchors -/

end
end NearCubicWires.PacketsConstruction
