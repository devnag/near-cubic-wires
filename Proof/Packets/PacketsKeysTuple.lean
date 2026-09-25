import Proof.Packets.PacketsKeysPowStage

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.PacketsKeys.Tuple
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production NearCubicWires.PacketsGlue.RequestMeta
noncomputable section

variable (a : DecompositionAlgorithm)

/-- The exponent: `0` (terminal), `1` (SYM), `digits(cutoff)` (THR). -/
def exOf (r : Request) : ℕ := max (liveFlag r) (thrFlag r * Nat.clog 2 (cutoffOf a r + 1))

theorem tupleWork_eq (r : Request) : tupleWork a r = (pop a r + 1) ^ exOf a r := by
  cases r with
  | terminal => simp [tupleWork, Request.tupleWork, exOf, liveFlag, thrFlag]
  | sym r four L tg =>
    simp [tupleWork, Request.tupleWork, exOf, liveFlag, thrFlag, pop, occ, Request.family, Packets.symFamily]
    rfl
  | thr r four L tg =>
    have h563 := canonicalPrimeCutoff_ge_563
      (familyMagnitudeExponent (RepairOrdinary.ThresholdRows.equation a r))
      (CloseoutFinalC10ThresholdRows.primeDenominator a r tg)
    have hc : cutoffOf a (.thr r four L tg) = CloseoutFinalC10ThresholdRows.primeCutoff a r tg := rfl
    have hd := log_succ_eq_clog (CloseoutFinalC10ThresholdRows.primeCutoff a r tg) (by
      unfold CloseoutFinalC10ThresholdRows.primeCutoff; omega)
    have hpos : 1 ≤ Nat.clog 2 (CloseoutFinalC10ThresholdRows.primeCutoff a r tg + 1) := by omega
    simp only [tupleWork, Request.tupleWork, exOf, liveFlag, thrFlag, hc, one_mul, pop, occ, Request.family,
      Packets.thrFamily, modulusDigitCount]
    rw [Nat.max_eq_right hpos, ← hd]
    rfl

theorem tupleWork_le_small (r : Request) : tupleWork a r ≤ r.smallSize a := by
  have key : ∀ q n x1 x2 x3 x4 x5 x6 : ℕ, x4 ≤ q + n + x1 + x2 + x3 + x4 + x5 + x6 + 1 := by intros; omega
  unfold tupleWork Request.smallSize
  exact key _ _ _ _ _ _ _ _

theorem max_cost (x y : ℕ) : maxMap2.cost x y ≤ 6 * (x + y + 3) ^ 1 := by
  change 2 * (max x y + 1) + 2 ≤ _
  rw [pow_one]
  rcases le_total x y with h | h
  · rw [max_eq_right h]; omega
  · rw [max_eq_left h]; omega

section Stages
variable (cutS : UnaryStage a (cutoffOf a))

def sx : UnaryStage a (fun r => pop a r + 1) := (popStage a).thenMapP (plusMap 1) (2 * 1 + 4) 1 (plus_cost 1)

def sd : UnaryStage a (fun r => Nat.clog 2 (cutoffOf a r + 1)) :=
  (cutS.thenMapP (plusMap 1) (2 * 1 + 4) 1 (plus_cost 1)).thenMapP clogMap 62 1 clog_cost

def se : UnaryStage a (exOf a) :=
  (liveFlagStage a).pairP ((thrFlagStage a).pairP (sd a cutS) mulMap2 8 2 mul_cost) maxMap2 6 1 max_cost

def sw : UnaryStage a (fun r => (pop a r + 1 + 1) * (exOf a r + 1)) :=
  ((sx a).thenMapP (plusMap 1) (2 * 1 + 4) 1 (plus_cost 1)).pairP
    ((se a cutS).thenMapP (plusMap 1) (2 * 1 + 4) 1 (plus_cost 1)) mulMap2 8 2 mul_cost

end Stages

/-! ## The side conditions of the power program -/

theorem lt_two_pow_mul (x e : ℕ) : x ^ e < 2 ^ ((x + 1) * (e + 1)) := by
  have h1 : x ^ e ≤ (2 ^ x) ^ e := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le e
  have h2 : (2 ^ x) ^ e = 2 ^ (x * e) := by rw [← pow_mul]
  have h3 : 2 ^ (x * e) < 2 ^ ((x + 1) * (e + 1)) := Nat.pow_lt_pow_right (by norm_num) (by nlinarith)
  omega

theorem good (x e : ℕ) :
    x < 2 ^ ((x + 1) * (e + 1)) ∧ e < 2 ^ ((x + 1) * (e + 1)) ∧ x ^ e < 2 ^ ((x + 1) * (e + 1)) ∧
      1 ≤ (x + 1) * (e + 1) := by
  have hw : x + e + 1 ≤ (x + 1) * (e + 1) := by nlinarith
  have hl : (x + 1) * (e + 1) < 2 ^ ((x + 1) * (e + 1)) := Nat.lt_two_pow_self
  refine ⟨by omega, by omega, lt_two_pow_mul x e, by omega⟩

/-- The program's steps with `x^e` abstracted to `P`. -/
def pc' (x e w P : ℕ) : ℕ :=
  1 + 1 + ((w + 1) * (1 + 1 + 2) + 1 + ((w + 3) + 1 + ((x + 1) * (1 + (2 * w + 3) + 2) + 1 +
    ((e + 1) * (1 + (2 * w + 3) + 2) + 1 + ((2 * w + 3) + 1 +
    ((e + 1) * ((2 * w + 3) + ((13 * w * w + 60 * w + 40) + 1 + ((2 * w + 3) + 1 + (2 * w + 3))) + 2) + 1 +
    (P + 1) * ((2 * w + 3) + (2 * w + 3 + 1 + 1) + 2)))))))

theorem pcost_eq (x e w : ℕ) : Pow.pcost x e w = pc' x e w (x ^ e) := rfl

theorem pc'_mono (x e w P S : ℕ) (hx : x ≤ S) (he : e ≤ S) (hw : w ≤ S) (hP : P ≤ S) : pc' x e w P ≤ pc' S S S S := by
  unfold pc'
  gcongr

theorem pc'_S (S : ℕ) : pc' S S S S ≤ 300 * (S + 1) ^ 3 := by
  unfold pc'
  nlinarith [Nat.zero_le S, sq_nonneg (S + 1)]

/-! ## The stage -/

section Final
variable (cutS : UnaryStage a (cutoffOf a))

/-- The dominating constants. -/
def K : ℕ := (sx a).coefficient + (se a cutS).coefficient + (sw a cutS).coefficient + 22
def D : ℕ := (sx a).degree + (se a cutS).degree + (sw a cutS).degree + 3

theorem S_bound (r : Request) :
    (pop a r + 1) + exOf a r + (pop a r + 1 + 1) * (exOf a r + 1) + (pop a r + 1) ^ exOf a r + 1 ≤
      K a cutS * (r.smallSize a) ^ D a cutS := by
  have b1 := (sx a).value_bound r
  have b2 := (se a cutS).value_bound r
  have b3 := (sw a cutS).value_bound r
  have b4 := tupleWork_le_small a r
  rw [tupleWork_eq] at b4
  have hs := one_le_small a r
  have p1 : (r.smallSize a) ^ ((sx a).degree + 1) ≤ (r.smallSize a) ^ D a cutS := Nat.pow_le_pow_right hs (by unfold D; omega)
  have p2 : (r.smallSize a) ^ ((se a cutS).degree + 1) ≤ (r.smallSize a) ^ D a cutS :=
    Nat.pow_le_pow_right hs (by unfold D; omega)
  have p3 : (r.smallSize a) ^ ((sw a cutS).degree + 1) ≤ (r.smallSize a) ^ D a cutS :=
    Nat.pow_le_pow_right hs (by unfold D; omega)
  have p4 : r.smallSize a ≤ (r.smallSize a) ^ D a cutS := by
    calc r.smallSize a = (r.smallSize a) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right hs (by unfold D; omega)
  have q1 := Nat.mul_le_mul_left ((sx a).coefficient + 7) p1
  have q2 := Nat.mul_le_mul_left ((se a cutS).coefficient + 7) p2
  have q3 := Nat.mul_le_mul_left ((sw a cutS).coefficient + 7) p3
  have e : K a cutS * (r.smallSize a) ^ D a cutS =
      ((sx a).coefficient + 7) * (r.smallSize a) ^ D a cutS + ((se a cutS).coefficient + 7) * (r.smallSize a) ^ D a cutS +
      ((sw a cutS).coefficient + 7) * (r.smallSize a) ^ D a cutS + (r.smallSize a) ^ D a cutS := by
    unfold K; ring
  rw [e]
  omega

/-- **`tupleWork`, one fixed machine.** -/
def tupleStage : UnaryStage a (tupleWork a) := by
  have h : tupleWork a = fun r => (pop a r + 1) ^ exOf a r := funext (tupleWork_eq a)
  rw [h]
  exact Pow.powStage (sx a) (se a cutS) (sw a cutS) (300 * K a cutS ^ 3) (3 * D a cutS)
    (fun r => good (pop a r + 1) (exOf a r))
    (by
      intro r
      rw [pcost_eq]
      set S := (pop a r + 1) + exOf a r + (pop a r + 1 + 1) * (exOf a r + 1) + (pop a r + 1) ^ exOf a r with hS
      have hm := pc'_mono (pop a r + 1) (exOf a r) ((pop a r + 1 + 1) * (exOf a r + 1)) ((pop a r + 1) ^ exOf a r) S
        (by omega) (by omega) (by omega) (by omega)
      have h3 := pc'_S S
      have hb := S_bound a cutS r
      have hp := Nat.pow_le_pow_left hb 3
      have e : (K a cutS * (r.smallSize a) ^ D a cutS) ^ 3 = K a cutS ^ 3 * (r.smallSize a) ^ (3 * D a cutS) := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm (D a cutS) 3]
      rw [e] at hp
      calc pc' (pop a r + 1) (exOf a r) ((pop a r + 1 + 1) * (exOf a r + 1)) ((pop a r + 1) ^ exOf a r)
          ≤ 300 * (S + 1) ^ 3 := hm.trans h3
        _ ≤ 300 * (K a cutS ^ 3 * (r.smallSize a) ^ (3 * D a cutS)) := Nat.mul_le_mul_left _ hp
        _ = 300 * K a cutS ^ 3 * (r.smallSize a) ^ (3 * D a cutS) := by ring)

end Final

end
end NearCubicWires.PacketsKeys.Tuple

