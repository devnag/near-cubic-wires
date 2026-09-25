import Proof.Packets.PacketsKitSeam
import Proof.Packets.PacketsRowGood
import Proof.Packets.PacketsXSubstitutionNatInvariant

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.LowerFacts
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent
open PCJ9eff70d512234a4c_Fixed.Materializer.LiteralAlphabet (Good)
noncomputable section

variable {a : DecompositionAlgorithm} (K : KitShape a) (r : Request) (k : rcKey a r)

theorem pop_le : (r.family a).occurrences.length ≤ K.C r := by
  have h := K.codes r
  unfold codeNeed at h
  omega

theorem child_le : relabelN a r ≤ K.C r := by
  have h := K.codes r
  unfold codeNeed at h
  omega

theorem one_le : 1 ≤ K.C r := by
  have h := K.codes r
  unfold codeNeed at h
  omega

/-- The row is a kit operand: normal, every code below `C`. -/
theorem row_kit_good : SubstitutionInvariant.Good (K.C r) (rcDecode a r k).polynomial := by
  have h := RowGood.row_good a r k
  refine ⟨fun m hm c hc => ?_, h.1⟩
  have h1 := Finset.mem_range.mp (h.2 m hm c hc)
  have h2 := pop_le K r
  omega

theorem small_le : r.smallSize a ≤ 2 ^ K.w r :=
  (Nat.le_self_pow (by norm_num) _).trans (K.census r)

/-- The child alphabet to the request degree plus one is a summand of `smallSize`. -/
theorem alphabet_pow : (Packets.alphabet a (r.family a)) ^ (r.degree a + 1) ≤ r.smallSize a := by
  dsimp only [Request.smallSize]
  generalize (2:ℕ) ^ (Packets.live (r.family a)).card = livePower
  generalize (2:ℕ) ^ (canonicalWalkLength (r.denominator a)) = walkPower
  omega

theorem row_degree_le (hk : k ∈ rcKeys a r) : (rcDecode a r k).degree ≤ r.degree a :=
  RCFive.PacketBounds.degree_bound a r _ (decode_mem a r k hk)

theorem child_alphabet : relabelN a r + 1 ≤ Packets.alphabet a (r.family a) := by
  unfold Packets.alphabet relabelN childCount
  omega

/-- **The child fit** `(N+1)^deg ≤ 2^w`. -/
theorem fit_child (hk : k ∈ rcKeys a r) : (relabelN a r + 1) ^ (rcDecode a r k).degree ≤ 2 ^ K.w r := by
  have hA := child_alphabet (a := a) r
  have hd := row_degree_le r k hk
  calc (relabelN a r + 1) ^ (rcDecode a r k).degree
      ≤ (Packets.alphabet a (r.family a)) ^ (rcDecode a r k).degree := Nat.pow_le_pow_left hA _
    _ ≤ (Packets.alphabet a (r.family a)) ^ (r.degree a + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ r.smallSize a := alphabet_pow (a := a) r
    _ ≤ 2 ^ K.w r := small_le K r

theorem fit_atom : relabelN a r + 1 ≤ 2 ^ K.w r := by
  have hA := child_alphabet (a := a) r
  calc relabelN a r + 1 ≤ Packets.alphabet a (r.family a) := hA
    _ ≤ (Packets.alphabet a (r.family a)) ^ (r.degree a + 1) := Nat.le_self_pow (by omega) _
    _ ≤ r.smallSize a := alphabet_pow (a := a) r
    _ ≤ 2 ^ K.w r := small_le K r

/-- **The row census.** -/
theorem row_census (hk : k ∈ rcKeys a r) : (rcDecode a r k).polynomial.length ≤ 2 ^ K.w r := by
  have hS : (Finset.range (r.family a).occurrences.length).card + 1 ≤
      ((r.family a).occurrences.length + 2) ^ 12 := by
    rw [Finset.card_range]
    have := Nat.le_self_pow (n := 12) (by norm_num) ((r.family a).occurrences.length + 2)
    omega
  exact (census_le a r (RowGood.row_good a r k) (RowGood.row_degree a r k) hS
    (Or.inr (row_degree_le r k hk))).trans (K.census r)

theorem lowered_good : Good (Finset.range (relabelN a r)) (Packets.lowered a (r.family a) (rcDecode a r k)) :=
  ⟨lowered_normal a _ _, fun m hm c hc => Finset.mem_range.mpr (lowered_valid a _ _ m hm c hc)⟩

/-- **The lowered census.** -/
theorem lowered_census (hk : k ∈ rcKeys a r) :
    (Packets.lowered a (r.family a) (rcDecode a r k)).length ≤ 2 ^ K.w r := by
  have h := count_le (lowered_good r k) (loweredDegree_holds a r k hk)
  rw [Finset.card_range] at h
  exact h.trans (fit_child K r k hk)

/-- The lowered row is normal, so its normal form is its reversal. -/
theorem norm_lowered :
    Ring.norm (Packets.lowered a (r.family a) (rcDecode a r k)) =
      (Packets.lowered a (r.family a) (rcDecode a r k)).reverse :=
  NormalizerOrder.norm_normal _ (lowered_normal a _ _)

theorem norm_census (hk : k ∈ rcKeys a r) :
    (Ring.norm (Packets.lowered a (r.family a) (rcDecode a r k))).length ≤ 2 ^ K.w r := by
  rw [norm_lowered, List.length_reverse]
  exact lowered_census K r k hk

theorem masks_flatten (C : ℕ) : ∀ P : Ring.Poly ℕ,
    (P.map (NormalizedFiniteTransport.maskNat C)).flatten.length = P.length * C
  | [] => by simp
  | m :: P => by
    rw [List.map_cons, List.flatten_cons, List.length_append, masks_flatten C P, List.length_cons,
      NormalizedFiniteTransport.maskNat, List.length_ofFn, Nat.succ_mul]
    omega

/-- **The row register fits the kit reserve.** -/
theorem row_fits (hk : k ∈ rcKeys a r) :
    PacketVector.Fits (PolyKit.reserve (K.C r) (K.w r))
      ((rcDecode a r k).polynomial.map (NormalizedFiniteTransport.maskNat (K.C r))) := by
  have hc := row_census K r k hk
  have h8 : 2 ^ K.w r ≤ 2 ^ (8 * K.w r) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hC4 : K.C r + 1 ≤ (K.C r + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
  have hpos : 1 ≤ 2 ^ (8 * K.w r) := Nat.one_le_two_pow
  set n := (rcDecode a r k).polynomial.length
  set X := 2 ^ (8 * K.w r)
  set Y := (K.C r + 1) ^ 4
  have hR : PolyKit.reserve (K.C r) (K.w r) = 65536 * Y * X := rfl
  refine ⟨?_, ?_⟩
  · rw [masks_flatten, hR]
    have h1 : n * K.C r ≤ X * Y := Nat.mul_le_mul (hc.trans h8) (by omega)
    nlinarith only [h1, hpos]
  · rw [List.length_map, hR]
    simp only [RepairSource.VerifierDecoding.CompareMachine.word, List.length_cons, List.length_replicate]
    have hY : 1 ≤ Y := by omega
    nlinarith only [hc, h8, hY, hpos]

/-- **The tape-14 seam word is the row register.** -/
theorem row_word :
    rowPolyWordK K r k = PacketVector.entry (PolyKit.reserve (K.C r) (K.w r))
      ((rcDecode a r k).polynomial.map (NormalizedFiniteTransport.maskNat (K.C r))) := by
  unfold rowPolyWordK KitShape.word PolyKit.vector PacketVector.bank PolyKit.masks
  simp

end
end NearCubicWires.PacketsConstruction.LowerFacts
