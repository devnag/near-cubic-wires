import Proof.Packets.PacketsConeWindow
import Proof.Packets.PacketsXWalkLiteralProducedMajorityAllRun
import Proof.Packets.PacketsXVectorLiteralPaletteCost

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.ConeBounds
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.SupplierListSchedule
noncomputable section

theorem clog_le_self (n : ℕ) : Nat.clog 2 n ≤ n :=
  Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le

theorem depth_le (B : ℕ) : canonicalGradedDepth B ≤ B + 8 := by
  unfold canonicalGradedDepth
  apply Nat.clog_le_of_le_pow
  have h : B < 2 ^ B := Nat.lt_two_pow_self
  rw [Nat.pow_add]
  omega

theorem rank_le (pop B : ℕ) (hB : B ≤ pop) (hpop : 1 ≤ pop) : canonicalGradedRank pop B ≤ 9 * pop := by
  unfold canonicalGradedRank
  have h1 := depth_le B
  have h2 := clog_le_self pop
  exact max_le (by omega) (by omega)

/-- A positive rank forces an occurrence. -/
theorem pop_pos (pop B : ℕ) (hB : B ≤ pop) (h : 0 < canonicalGradedRank pop B) : 1 ≤ pop := by
  by_contra h0
  have hp : pop = 0 := by omega
  have hb : B = 0 := by omega
  subst hp
  subst hb
  simp [canonicalGradedRank, canonicalGradedDepth] at h

/-- The rank is zero exactly when there is no touching occurrence and at most one occurrence. -/
theorem rank_eq_zero_iff (pop B : ℕ) (hB : B ≤ pop) : canonicalGradedRank pop B = 0 ↔ B = 0 ∧ pop ≤ 1 := by
  unfold canonicalGradedRank canonicalGradedDepth
  constructor
  · intro h
    have h1 : Nat.clog 2 (256 * B) = 0 := by omega
    have h2 : Nat.clog 2 pop = 0 := by omega
    have h1' := (Nat.clog_le_iff_le_pow (b := 2) (by norm_num) (x := 256 * B) (y := 0)).1 (by omega)
    have h2' := (Nat.clog_le_iff_le_pow (b := 2) (by norm_num) (x := pop) (y := 0)).1 (by omega)
    simp only [pow_zero] at h1' h2'
    omega
  · rintro ⟨rfl, hp⟩
    have hc : Nat.clog 2 pop = 0 := Nat.clog_of_right_le_one hp 2
    simp [hc]

theorem root_le (B : ℕ) : ConeWindow.root B ≤ 64 * (B + 1) := by
  unfold ConeWindow.root
  by_contra h
  have h' : 64 * (B + 1) < natCeilSqrt (64 ^ 2 * B) := by omega
  have hs := sq_lt_of_lt_natCeilSqrt h'
  nlinarith

theorem window_le (B : ℕ) {depth : ℕ} (l : Fin depth) :
    executableGradedWindow B l ≤ 64 + ConeWindow.root B := by
  unfold executableGradedWindow ConeWindow.root
  have hd : 0 < 2 ^ (l.val / 3) := Nat.two_pow_pos _
  have hx : natCeilSqrt (64 ^ 2 * B) ≤ natCeilSqrt (64 ^ 2 * B) * 2 ^ (l.val / 3) :=
    Nat.le_mul_of_pos_right _ hd
  have hlt : (natCeilSqrt (64 ^ 2 * B) + 2 ^ (l.val / 3) - 1) / 2 ^ (l.val / 3) <
      natCeilSqrt (64 ^ 2 * B) + 1 := by
    rw [Nat.div_lt_iff_lt_mul hd, Nat.add_mul, Nat.one_mul]
    omega
  rw [Nat.ceilDiv_eq_add_pred_div]
  omega

theorem literal_base_le (pop B : ℕ) (hB : B ≤ pop) :
    pop * (2 * canonicalGradedDepth B + 1) + 2 ≤ (pop + 2) ^ 3 := by
  have hd := depth_le B
  have h1 : pop * (2 * canonicalGradedDepth B + 1) ≤ pop * (2 * pop + 17) :=
    Nat.mul_le_mul_left _ (by omega)
  have h3 : (pop + 2) ^ 3 = pop * pop * pop + 6 * (pop * pop) + 12 * pop + 8 := by ring
  have h4 : 5 * pop ≤ 4 * (pop * pop) + 6 := by
    rcases Nat.lt_or_ge pop 2 with h | h
    · interval_cases pop <;> omega
    · have : 2 * pop ≤ pop * pop := Nat.mul_le_mul_right pop h
      omega
  have h5 : pop * (2 * pop + 17) = 2 * (pop * pop) + 17 * pop := by ring
  omega

theorem reserve_ge (C w : ℕ) : 65536 * (C + 1) ≤ Theorem25Completion.CycleBounds.commonReserve C w := by
  unfold Theorem25Completion.CycleBounds.commonReserve
  have h1 : C + 1 ≤ (C + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
  have h2 : 1 ≤ 2 ^ (8 * w) := Nat.one_le_two_pow
  calc 65536 * (C + 1) ≤ 65536 * (C + 1) ^ 4 := Nat.mul_le_mul_left _ h1
    _ = 65536 * (C + 1) ^ 4 * 1 := by ring
    _ ≤ 65536 * (C + 1) ^ 4 * 2 ^ (8 * w) := Nat.mul_le_mul_left _ h2

/-! ## The `Bounds` structure at family level -/

/-- **All twenty `Bounds` fields**, from the route-A code bound, the kit's code bound, a positive rank, and three
census facts. -/
theorem bounds {q : ℕ} (occ : List (SupportedNormalizedGate q)) (I : Finset (Fin q)) (C w : ℕ)
    (hrank : 0 < canonicalGradedRank occ.length (LiveRows.bound occ I))
    (hC : (258 * occ.length + 2) ^ 2 ≤ C)
    (hcode : (canonicalGradedDepth (LiveRows.bound occ I) + 2 * occ.length + 2) ^ 2 ≤ C)
    (hw : 3 ≤ w)
    (hlit : (occ.length * (2 * canonicalGradedDepth (LiveRows.bound occ I) + 1) + 2) ^ rawDeg occ I ≤ 2 ^ w)
    (hsrc : (occ.length + 1) ^ rawDeg occ I ≤ 2 ^ w) (hatoms : occ.length + 1 ≤ 2 ^ w) :
    Theorem25Completion.WalkLiteralLoop.Bounds C w (rawDeg occ I) occ.length (LiveRows.bound occ I)
      (canonicalGradedDepth (LiveRows.bound occ I)) (ConeWindow.root (LiveRows.bound occ I))
      (Theorem25Completion.WalkLiteralProducedMajority.S C w) (Theorem25Completion.WalkLiteralProducedMajority.R C w)
      (executableGradedWindow (depth := canonicalGradedDepth (LiveRows.bound occ I)) (LiveRows.bound occ I)) := by
  have hB := bound_le_pop occ I
  have hpop := pop_pos _ _ hB hrank
  have hr := rank_le _ _ hB hpop
  have hpC : occ.length ≤ C := by
    have : 258 * occ.length + 2 ≤ (258 * occ.length + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have hdC : canonicalGradedDepth (LiveRows.bound occ I) ≤ C := by
    have : canonicalGradedDepth (LiveRows.bound occ I) + 2 * occ.length + 2 ≤
        (canonicalGradedDepth (LiveRows.bound occ I) + 2 * occ.length + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have hres := reserve_ge C w
  have hroot := root_le (LiveRows.bound occ I)
  have hrootR : ConeWindow.root (LiveRows.bound occ I) ≤ Theorem25Completion.CycleBounds.commonReserve C w := by
    omega
  exact {
    depthRank := le_max_left _ _
    rankPopulation := hr
    populationCapacity := hC
    codeCapacity := hcode
    populationPositive := hpop
    populationRank := population_le_two_pow_canonicalGradedRank _ _
    width := hw
    degree := le_refl _
    literals := hlit
    source := hsrc
    atoms := hatoms
    windows := fun level => (ConeWindow.window_eq _ level).symm
    windowBound := fun level => by
      have := window_le (LiveRows.bound occ I) level
      omega
    rootBound := by omega
    reserve := PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp.palette_reserve_common C w
    capacity := PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp.palette_reserve_width C w
    space := PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp.palette_reserve_execution C w _ _ _ hw hpC hdC hrootR
    rankPositive := hrank
    decode := by
      show 8 * canonicalGradedRank occ.length (LiveRows.bound occ I) + 14 ≤
        Theorem25Completion.CycleBounds.commonReserve C w
      omega
    labels := by
      show 2 * toeplitzWalkSideBits (canonicalGradedRank occ.length (LiveRows.bound occ I)) + 1 ≤
        Theorem25Completion.CycleBounds.commonReserve C w
      unfold toeplitzWalkSideBits toeplitzSeedBits
      omega }

/-! ## Per request: the route-A shape and the keyed condition -/

variable (a : DecompositionAlgorithm)

def RouteA (K : KitShape a) : Prop :=
  ∀ r : Request, (258 * (r.family a).occurrences.length + 2) ^ 2 ≤ K.C r

/-- The non-degenerate requests: positive graded rank. -/
def Keyed (r : Request) : Prop :=
  0 < canonicalGradedRank (r.family a).occurrences.length
    (LiveRows.bound (r.family a).occurrences (Packets.live (r.family a)))

/-- SYM: the walk-majority degree is at most the request degree (one circuit at least). -/
theorem walkDeg_le_sym (r0 : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (four : r0.circuits.length ≤ 4) (L target : ℕ) (k : RCFive.RowKeys.SymKey r0 L target)
    (hk : k ∈ RCFive.RowKeys.symKeys r0 L target) (hpop : 1 ≤ (symmetricFourfoldOccurrences r0).length) :
    canonicalWalkLength (symmetricListDenominator r0 target) *
        rawDeg (symmetricFourfoldOccurrences r0) (CyclicChoice.live (symmetricFourfoldOccurrences r0) L) ≤
      (Request.sym r0 four L target).degree a := by
  have hrow := RCFive.PacketBounds.degree_bound a (Request.sym r0 four L target)
    (rcDecode a (Request.sym r0 four L target) k) (decode_mem a (Request.sym r0 four L target) k hk)
  have hc : 1 ≤ r0.circuits.length := by
    rcases Nat.eq_zero_or_pos r0.circuits.length with h | h
    · have hnil : r0.circuits = [] := List.eq_nil_of_length_eq_zero h
      have : (symmetricFourfoldOccurrences r0).length = 0 := by
        unfold symmetricFourfoldOccurrences
        rw [hnil]
        rfl
      omega
    · exact h
  have hdeg : (rcDecode a (Request.sym r0 four L target) k).degree =
      r0.circuits.length * (canonicalWalkLength (symmetricListDenominator r0 target) *
        rawDeg (symmetricFourfoldOccurrences r0) (CyclicChoice.live (symmetricFourfoldOccurrences r0) L)) := rfl
  rw [hdeg] at hrow
  have h2 := Nat.le_mul_of_pos_left (canonicalWalkLength (symmetricListDenominator r0 target) *
    rawDeg (symmetricFourfoldOccurrences r0) (CyclicChoice.live (symmetricFourfoldOccurrences r0) L)) hc
  omega

/-- THR: the walk-majority degree is at most the request degree. -/
theorem walkDeg_le_thr (r0 : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r0.circuits.length ≤ 4) (L target : ℕ) (k : RCFive.RowKeys.ThrKey a r0 L target)
    (hk : k ∈ RCFive.RowKeys.thrKeys a r0 L target) :
    canonicalWalkLength (CloseoutFinalC10ThresholdRows.listDenominator a r0 target) *
        rawDeg (thresholdFourfoldOccurrences r0) (CyclicChoice.live (thresholdFourfoldOccurrences r0) L) ≤
      (Request.thr r0 four L target).degree a := by
  have hrow := RCFive.PacketBounds.degree_bound a (Request.thr r0 four L target)
    (rcDecode a (Request.thr r0 four L target) k) (decode_mem a (Request.thr r0 four L target) k hk)
  have hdeg : (rcDecode a (Request.thr r0 four L target) k).degree =
      modulusDigitCount k.prime.val * (canonicalWalkLength (CloseoutFinalC10ThresholdRows.listDenominator a r0 target) *
        rawDeg (thresholdFourfoldOccurrences r0) (CyclicChoice.live (thresholdFourfoldOccurrences r0) L)) := rfl
  rw [hdeg] at hrow
  have hc : 1 ≤ modulusDigitCount k.prime.val := by
    unfold modulusDigitCount
    omega
  have h2 := Nat.le_mul_of_pos_left (canonicalWalkLength (CloseoutFinalC10ThresholdRows.listDenominator a r0 target) *
    rawDeg (thresholdFourfoldOccurrences r0) (CyclicChoice.live (thresholdFourfoldOccurrences r0) L)) hc
  omega

/-- Any keyed, non-degenerate request: the walk-majority degree is at most the request degree. -/
theorem walkDeg_le (r : Request) (k : rcKey a r) (hk : k ∈ rcKeys a r) (hkey : Keyed a r) :
    canonicalWalkLength (r.denominator a) *
        rawDeg (r.family a).occurrences (Packets.live (r.family a)) ≤ r.degree a := by
  cases r with
  | terminal => exact PEmpty.elim k
  | sym r0 four L target =>
    have hpop := pop_pos _ _ (bound_le_pop _ _) hkey
    exact walkDeg_le_sym a r0 four L target k hk hpop
  | thr r0 four L target => exact walkDeg_le_thr a r0 four L target k hk

/-- **The route-A premises of `all_run` at a keyed non-degenerate request**, all but the machine data: `Bounds`,
`hfit`, `hVisits`, `hCodes` (and `hdepth` is `rfl`). -/
theorem fit (K : KitShape a) (hA : RouteA a K) (r : Request) (k : rcKey a r) (hk : k ∈ rcKeys a r)
    (hkey : Keyed a r) :
    Theorem25Completion.WalkLiteralLoop.Bounds (K.C r) (K.w r)
        (rawDeg (r.family a).occurrences (Packets.live (r.family a))) (r.family a).occurrences.length
        (LiveRows.bound (r.family a).occurrences (Packets.live (r.family a)))
        (canonicalGradedDepth (LiveRows.bound (r.family a).occurrences (Packets.live (r.family a))))
        (ConeWindow.root (LiveRows.bound (r.family a).occurrences (Packets.live (r.family a))))
        (Theorem25Completion.WalkLiteralProducedMajority.S (K.C r) (K.w r))
        (Theorem25Completion.WalkLiteralProducedMajority.R (K.C r) (K.w r))
        (executableGradedWindow (depth := canonicalGradedDepth
          (LiveRows.bound (r.family a).occurrences (Packets.live (r.family a))))
          (LiveRows.bound (r.family a).occurrences (Packets.live (r.family a)))) ∧
      ((r.family a).occurrences.length + 1) ^
          (rawDeg (r.family a).occurrences (Packets.live (r.family a)) * canonicalWalkLength (r.denominator a)) ≤
        2 ^ (K.w r) ∧
      canonicalWalkLength (r.denominator a) ≤ 2 ^ (K.w r) ∧
      2 ^ canonicalWalkLength (r.denominator a) ≤ 2 ^ (K.w r) := by
  have hwd := walkDeg_le a r k hk hkey
  have hT := walk_pos (r.denominator a)
  have hd : rawDeg (r.family a).occurrences (Packets.live (r.family a)) ≤ r.degree a := by
    have := Nat.le_mul_of_pos_left (rawDeg (r.family a).occurrences (Packets.live (r.family a))) hT
    omega
  have hocc := small_occ a r
  have hwalk := small_walk a r
  have hcen := K.census r
  have hs12 : r.smallSize a ≤ (r.smallSize a) ^ 12 := Nat.le_self_pow (by norm_num) _
  have hs2 : 2 ≤ r.smallSize a := by
    have : 2 ≤ ((r.family a).occurrences.length + 2) ^ (r.degree a + 1) :=
      (Nat.le_self_pow (by omega) _).trans' (by omega)
    omega
  have hsw : r.smallSize a ≤ 2 ^ (K.w r) := hs12.trans hcen
  have hpow : ∀ e, e ≤ r.degree a →
      ((r.family a).occurrences.length + 2) ^ e ≤ r.smallSize a := fun e he =>
    (Nat.pow_le_pow_right (by omega) (by omega)).trans hocc
  have hw : 3 ≤ K.w r := by
    by_contra hlt
    have h1 : 2 ^ (K.w r) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ 12 ≤ (r.smallSize a) ^ 12 := Nat.pow_le_pow_left hs2 12
    omega
  have hB := bound_le_pop (r.family a).occurrences (Packets.live (r.family a))
  have hlit : ((r.family a).occurrences.length *
        (2 * canonicalGradedDepth (LiveRows.bound (r.family a).occurrences (Packets.live (r.family a))) + 1) + 2) ^
        rawDeg (r.family a).occurrences (Packets.live (r.family a)) ≤ 2 ^ (K.w r) := by
    have hb := literal_base_le _ _ hB
    calc _ ≤ (((r.family a).occurrences.length + 2) ^ 3) ^
            rawDeg (r.family a).occurrences (Packets.live (r.family a)) := Nat.pow_le_pow_left hb _
      _ = (((r.family a).occurrences.length + 2) ^
            rawDeg (r.family a).occurrences (Packets.live (r.family a))) ^ 3 := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ (r.smallSize a) ^ 3 := Nat.pow_le_pow_left (hpow _ hd) 3
      _ ≤ (r.smallSize a) ^ 12 := Nat.pow_le_pow_right (by omega) (by norm_num)
      _ ≤ 2 ^ (K.w r) := hcen
  have hsrc : ((r.family a).occurrences.length + 1) ^ rawDeg (r.family a).occurrences (Packets.live (r.family a)) ≤
      2 ^ (K.w r) :=
    ((Nat.pow_le_pow_left (by omega) _).trans (hpow _ hd)).trans hsw
  have hatoms : (r.family a).occurrences.length + 1 ≤ 2 ^ (K.w r) := by
    have : (r.family a).occurrences.length + 2 ≤ ((r.family a).occurrences.length + 2) ^ (r.degree a + 1) :=
      Nat.le_self_pow (by omega) _
    omega
  have hcode : (canonicalGradedDepth (LiveRows.bound (r.family a).occurrences (Packets.live (r.family a))) +
      2 * (r.family a).occurrences.length + 2) ^ 2 ≤ K.C r := by
    have := K.codes r
    unfold codeNeed at this
    omega
  refine ⟨bounds _ _ _ _ hkey (hA r) hcode hw hlit hsrc hatoms, ?_, ?_, ?_⟩
  · have hfit : rawDeg (r.family a).occurrences (Packets.live (r.family a)) * canonicalWalkLength (r.denominator a) ≤
        r.degree a := by rw [Nat.mul_comm]; exact hwd
    exact ((Nat.pow_le_pow_left (by omega) _).trans (hpow _ hfit)).trans hsw
  · have : canonicalWalkLength (r.denominator a) < 2 ^ canonicalWalkLength (r.denominator a) := Nat.lt_two_pow_self
    omega
  · omega

end
end NearCubicWires.PacketsConstruction.ConeBounds
