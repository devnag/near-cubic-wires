import Proof.Packets.PacketsCombineThrMetaVec
import Proof.Packets.PacketsCombineThrPow
import Proof.Packets.PacketsLowerAdapter

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.PacketsCombine.Asm
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrime NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction
open NearCubicWires.PacketsGlue.RequestMeta
noncomputable section

variable {a : DecompositionAlgorithm}

/-! ## Small adapters -/

/-- Transport a THR word along a pointwise equality of its values. -/
def ThrWord.congrV {v w : TVal a} (s : ThrWord a v)
    (h : ∀ r four L target (k : RCFive.RowKeys.ThrKey a r L target), v r four L target k = w r four L target k) :
    ThrWord a w where
  extra := s.extra
  states := s.states
  machine := s.machine
  cost := s.cost
  costC := s.costC
  costD := s.costD
  cost_le := s.cost_le
  run := by
    intro r four L target k hk
    obtain ⟨H, A, st, keep, h9, hh9⟩ := s.run r four L target k hk
    exact ⟨H, A, st, keep, h9.trans (h r four L target k), hh9⟩

def tplStage {v : Request → ℕ} (s : UnaryStage a v) : WordStage a (fun r => UnaryTemplate.tape (v r)) :=
  s.thenWord tplMap (2 * s.coefficient + 16) (s.degree + 1) (by
    intro r
    have hb := s.value_bound r
    have p0 : 1 ≤ (r.smallSize a) ^ (s.degree + 1) := Nat.one_le_pow _ _ (one_le_small a r)
    show 2 * v r + 8 ≤ (2 * s.coefficient + 16) * (r.smallSize a) ^ (s.degree + 1)
    have e : (2 * s.coefficient + 16) * (r.smallSize a) ^ (s.degree + 1) =
        2 * ((s.coefficient + 7) * (r.smallSize a) ^ (s.degree + 1)) + 2 * (r.smallSize a) ^ (s.degree + 1) := by
      ring
    rw [e]
    omega)

/-! ## The per-request master bound -/

section Bounds
variable (cutS : UnaryStage a (cutoffOf a))

/-- Coefficient of the master bound. -/
def bigC : ℕ := cutS.coefficient + 10 ^ 12 + 14
/-- Degree of the master bound. -/
def bigD : ℕ := cutS.degree + 25

theorem thr_d_eq {r : TReq} {L target : ℕ} (k : RCFive.RowKeys.ThrKey a r L target) :
    Nat.clog 2 (k.prime.val + 1) = thrD k := by
  have hp : 1 ≤ k.prime.val := by have := k.residue.isLt; omega
  unfold thrD modulusDigitCount
  exact (log_succ_eq_clog _ hp).symm

/-- **Every scalar of a THR key's table is at most `B = bigC·smallSize^bigD`.** -/
theorem thr_scalars (r : TReq) (four : r.circuits.length ≤ 4) (L target : ℕ)
    (k : RCFive.RowKeys.ThrKey a r L target) :
    1 ≤ bigC cutS * ((Request.thr r four L target).smallSize a) ^ bigD cutS ∧
    k.prime.val + 1 ≤ bigC cutS * ((Request.thr r four L target).smallSize a) ^ bigD cutS ∧
    k.residue.val ≤ bigC cutS * ((Request.thr r four L target).smallSize a) ^ bigD cutS ∧
    thrD k + ((thresholdFourfoldOccurrences r).length + 1) ≤
      bigC cutS * ((Request.thr r four L target).smallSize a) ^ bigD cutS ∧
    thrD k * ((thresholdFourfoldOccurrences r).length + 1) ≤
      bigC cutS * ((Request.thr r four L target).smallSize a) ^ bigD cutS ∧
    ((thresholdFourfoldOccurrences r).length + 1) ^ thrD k ≤
      bigC cutS * ((Request.thr r four L target).smallSize a) ^ bigD cutS ∧
    (thresholdFourfoldOccurrences r).length ≤ bigC cutS * ((Request.thr r four L target).smallSize a) ^ bigD cutS ∧
    ((thresholdFourfoldOccurrences r).length + 1) + thrD k + wOf a (.thr r four L target) +
        ((thresholdFourfoldOccurrences r).length + 1) ^ thrD k + 1 ≤
      bigC cutS * ((Request.thr r four L target).smallSize a) ^ bigD cutS ∧
    (thresholdFourfoldOccurrences r).length + thrD k + k.prime.val + k.residue.val +
        ((thresholdFourfoldOccurrences r).length + 1) ^ thrD k + 1 ≤
      2 * (bigC cutS * ((Request.thr r four L target).smallSize a) ^ bigD cutS) ∧
    powPre ((thresholdFourfoldOccurrences r).length + 1, thrD k, wOf a (.thr r four L target)) := by
  have hs1 : 1 ≤ (Request.thr r four L target).smallSize a := one_le_small a _
  have hcut := cutS.value_bound (.thr r four L target)
  have hp : k.prime.val ≤ CloseoutFinalC10ThresholdRows.primeCutoff a r target :=
    (mem_primesUpTo.mp k.prime.property).2
  have ecut : cutoffOf a (.thr r four L target) = CloseoutFinalC10ThresholdRows.primeCutoff a r target := rfl
  have hres := k.residue.isLt
  have hdig := thr_digits_lt a r L target k
  have hwalk := small_walk a (.thr r four L target)
  change 2 ^ canonicalWalkLength (CloseoutFinalC10ThresholdRows.listDenominator a r target) ≤
    (Request.thr r four L target).smallSize a at hwalk
  have hD : thrD k < (Request.thr r four L target).smallSize a := by unfold thrD; omega
  have hpop := (small_facts (kitShapePG a) (.thr r four L target)).2.1
  change (thresholdFourfoldOccurrences r).length + 2 ≤ (Request.thr r four L target).smallSize a at hpop
  have hdims := thr_dims_le r four L target k
  unfold thrKmax thrNmax at hdims
  have hcen := census a (.thr r four L target)
  have hwp := w_pos a (.thr r four L target)
  have hwl := w_le a (.thr r four L target)
  have hw2 : wOf a (.thr r four L target) < 2 ^ wOf a (.thr r four L target) := Nat.lt_two_pow_self
  generalize (Request.thr r four L target).smallSize a = S at *
  have hS12 : S < S ^ 12 := by
    have h := Nat.pow_lt_pow_right (show 1 < S by omega) (show 1 < 12 by norm_num)
    simpa using h
  -- the master bound
  have p1 : S ^ (cutS.degree + 1) ≤ S ^ bigD cutS := Nat.pow_le_pow_right hs1 (by unfold bigD; omega)
  have p2 : S ^ 2 ≤ S ^ bigD cutS := Nat.pow_le_pow_right hs1 (by unfold bigD; omega)
  have p3 : S ^ 24 ≤ S ^ bigD cutS := Nat.pow_le_pow_right hs1 (by unfold bigD; omega)
  have p4 : S ≤ S ^ bigD cutS := by
    calc S = S ^ 1 := (pow_one S).symm
      _ ≤ S ^ bigD cutS := Nat.pow_le_pow_right hs1 (by unfold bigD; omega)
  have p0 : 1 ≤ S ^ bigD cutS := Nat.one_le_pow _ _ hs1
  have q1 := Nat.mul_le_mul_left (cutS.coefficient + 7) p1
  have q3 := Nat.mul_le_mul_left (10 ^ 12) p3
  have hSS : S * S = S ^ 2 := (sq S).symm
  have hB : (cutS.coefficient + 7) * S ^ (cutS.degree + 1) + S * S + 10 ^ 12 * S ^ 24 + 3 * S + 3 ≤
      bigC cutS * S ^ bigD cutS := by
    have e : bigC cutS * S ^ bigD cutS = (cutS.coefficient + 7) * S ^ bigD cutS + S ^ bigD cutS +
        10 ^ 12 * S ^ bigD cutS + 3 * S ^ bigD cutS + 3 * S ^ bigD cutS := by
      unfold bigC; ring
    rw [e, hSS]
    omega
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
  unfold powPre
  dsimp only
  refine ⟨by omega, by omega, by omega, hwp⟩

end Bounds

/-! ## The words -/

section Words
variable (cutS : UnaryStage a (cutoffOf a)) (wS : UnaryStage a (wOf a))
  {vP vR : ∀ r : Request, rcKey a r → List Bool} (primeW : Residual.KeyWord a vP) (resW : Residual.KeyWord a vR)
  (hP : ∀ (r : TReq) (four : r.circuits.length ≤ 4) (L target : ℕ) (k : RCFive.RowKeys.ThrKey a r L target),
    vP (.thr r four L target) k = List.replicate k.prime.val true)
  (hR : ∀ (r : TReq) (four : r.circuits.length ≤ 4) (L target : ℕ) (k : RCFive.RowKeys.ThrKey a r L target),
    vR (.thr r four L target) k = List.replicate k.residue.val true)

def primeWord : ThrWord a (fun _ _ _ _ k => List.replicate k.prime.val true) :=
  ThrWord.ofKeyWord primeW _ hP

def resWord : ThrWord a (fun _ _ _ _ k => List.replicate k.residue.val true) :=
  ThrWord.ofKeyWord resW _ hR

def mWord : ThrWord a (fun r _ _ _ _ => List.replicate ((thresholdFourfoldOccurrences r).length + 1) true) :=
  ThrWord.congrV (ThrWord.ofUnary ((popStage a).thenMapP (plusMap 1) 6 1 (plus_cost 1))) (fun _ _ _ _ _ => rfl)

def widthWord : ThrWord a (fun r four L target _ => List.replicate (wOf a (.thr r four L target)) true) :=
  ThrWord.ofUnary wS

def thrDWord : ThrWord a (fun _ _ _ _ k => List.replicate (thrD k) true) :=
  ThrWord.congrV
    (((primeWord primeW hP).thenMap (plusMap 1) (18 * bigC cutS) (bigD cutS) (by
        intro r four L target k _
        have hs := thr_scalars cutS r four L target k
        have hc := plus_cost 1 k.prime.val
        rw [Nat.mul_assoc]
        simp only [pow_one] at hc
        omega)).thenMap clogMap (248 * bigC cutS) (bigD cutS) (by
        intro r four L target k _
        have hs := thr_scalars cutS r four L target k
        have hc := clog_cost (k.prime.val + 1)
        rw [Nat.mul_assoc]
        simp only [pow_one] at hc
        omega))
    (fun _ _ _ _ k => by rw [thr_d_eq k])

def kWord : ThrWord a (fun r _ _ _ k => List.replicate (thrD k * ((thresholdFourfoldOccurrences r).length + 1)) true) :=
  ThrWord.pair (thrDWord cutS primeW hP) (mWord (a := a)) mulMap2 (128 * bigC cutS ^ 2) (bigD cutS * 2) (by
    intro r four L target k _
    have hs := thr_scalars cutS r four L target k
    have hc := mul_cost (thrD k) ((thresholdFourfoldOccurrences r).length + 1)
    have h4 : thrD k + ((thresholdFourfoldOccurrences r).length + 1) + 3 ≤
        4 * (bigC cutS * ((Request.thr r four L target).smallSize a) ^ bigD cutS) := by omega
    have h5 := Nat.pow_le_pow_left h4 2
    have e : (4 * (bigC cutS * ((Request.thr r four L target).smallSize a) ^ bigD cutS)) ^ 2 =
        16 * (bigC cutS ^ 2 * ((Request.thr r four L target).smallSize a) ^ (bigD cutS * 2)) := by
      rw [mul_pow, mul_pow, ← pow_mul]; ring
    rw [e] at h5
    have e2 : 128 * bigC cutS ^ 2 * ((Request.thr r four L target).smallSize a) ^ (bigD cutS * 2) =
        128 * (bigC cutS ^ 2 * ((Request.thr r four L target).smallSize a) ^ (bigD cutS * 2)) := by ring
    rw [e2]
    omega)

def nWord : ThrWord a (fun r _ _ _ k => List.replicate (((thresholdFourfoldOccurrences r).length + 1) ^ thrD k) true) :=
  ThrWord.pow (mWord (a := a)) (thrDWord cutS primeW hP) (widthWord wS)
    (fun r four L target k _ => (thr_scalars cutS r four L target k).2.2.2.2.2.2.2.2.2)
    (1026 * bigC cutS ^ 3) (bigD cutS * 3) (by
      intro r four L target k _
      have hs := thr_scalars cutS r four L target k
      have hc := pcost_le ((thresholdFourfoldOccurrences r).length + 1) (thrD k) (wOf a (.thr r four L target))
      set B := bigC cutS * ((Request.thr r four L target).smallSize a) ^ bigD cutS with hBdef
      have hY : (thresholdFourfoldOccurrences r).length + 1 + thrD k + wOf a (.thr r four L target) +
          ((thresholdFourfoldOccurrences r).length + 1) ^ thrD k + 1 ≤ B := hs.2.2.2.2.2.2.2.1
      have h3 := Nat.pow_le_pow_left hY 3
      have hB1 : 1 ≤ B := hs.1
      have hB3 : 1 ≤ B ^ 3 := Nat.one_le_pow _ _ hB1
      have e : 1026 * bigC cutS ^ 3 * ((Request.thr r four L target).smallSize a) ^ (bigD cutS * 3) =
          1026 * B ^ 3 := by
        rw [hBdef, mul_pow, ← pow_mul]; ring
      rw [e]
      omega)

theorem tplCost (cutS : UnaryStage a (cutoffOf a)) {u : TNat a}
    (hu : ∀ r four L target k, k ∈ RCFive.RowKeys.thrKeys a r L target →
      u r four L target k ≤ bigC cutS * ((Request.thr r four L target).smallSize a) ^ bigD cutS) :
    ∀ r four L target k, k ∈ RCFive.RowKeys.thrKeys a r L target →
      tplMap.cost (u r four L target k) ≤ 10 * bigC cutS * ((Request.thr r four L target).smallSize a) ^ bigD cutS := by
  intro r four L target k hk
  have h := hu r four L target k hk
  have h1 := (thr_scalars cutS r four L target k).1
  show 2 * u r four L target k + 8 ≤ _
  rw [Nat.mul_assoc]
  omega

/-- **The eleven words** on tapes 9–19. -/
def vec11 :=
  ((((((((((((ThrVec.nil a (fun _ _ _ _ _ _ => [])).snoc (ThrWord.ofWord (tplStage (kitCStage a)))).snoc
    (ThrWord.ofWord (tplStage (kitCStage a)))).snoc (ThrWord.ofWord (tplStage wS))).snoc
    ((kWord cutS primeW hP).thenWord tplMap (10 * bigC cutS) (bigD cutS)
      (tplCost cutS (fun r four L target k _ => (thr_scalars cutS r four L target k).2.2.2.2.1)))).snoc
    ((kWord cutS primeW hP).thenWord tplMap (10 * bigC cutS) (bigD cutS)
      (tplCost cutS (fun r four L target k _ => (thr_scalars cutS r four L target k).2.2.2.2.1)))).snoc
    ((nWord cutS wS primeW hP).thenWord tplMap (10 * bigC cutS) (bigD cutS)
      (tplCost cutS (fun r four L target k _ => (thr_scalars cutS r four L target k).2.2.2.2.2.1)))).snoc
    (ThrWord.blank a)).snoc (ThrWord.ofWord (tplStage (popStage a)))).snoc
    ((thrDWord cutS primeW hP).thenWord tplMap (10 * bigC cutS) (bigD cutS)
      (tplCost cutS (fun r four L target k _ => by
        have := (thr_scalars cutS r four L target k).2.2.2.1
        omega)))).snoc
    ((primeWord primeW hP).thenWord tplMap (10 * bigC cutS) (bigD cutS)
      (tplCost cutS (fun r four L target k _ => by
        have := (thr_scalars cutS r four L target k).2.1
        omega)))).snoc
    ((resWord resW hR).thenWord tplMap (10 * bigC cutS) (bigD cutS)
      (tplCost cutS (fun r four L target k _ => (thr_scalars cutS r four L target k).2.2.1))))

/-- The writer's per-request fuel. -/
def writerBound (R : Request) : ℕ := 2 ^ 20 * (2 * (bigC cutS * (R.smallSize a) ^ bigD cutS)) ^ 4

theorem writerBound_le (R : Request) :
    writerBound cutS R ≤ 2 ^ 24 * bigC cutS ^ 4 * (R.smallSize a) ^ (bigD cutS * 4) := by
  unfold writerBound
  rw [mul_pow, mul_pow, ← pow_mul]
  exact le_of_eq (by ring)

def thrMetaPG (a : DecompositionAlgorithm) (cutS : UnaryStage a (cutoffOf a)) (wS : UnaryStage a (wOf a))
    {vP vR : ∀ r : Request, rcKey a r → List Bool} (primeW : Residual.KeyWord a vP) (resW : Residual.KeyWord a vR)
    (hP : ∀ (r : TReq) (four : r.circuits.length ≤ 4) (L target : ℕ) (k : RCFive.RowKeys.ThrKey a r L target),
      vP (.thr r four L target) k = List.replicate k.prime.val true)
    (hR : ∀ (r : TReq) (four : r.circuits.length ≤ 4) (L target : ℕ) (k : RCFive.RowKeys.ThrKey a r L target),
      vR (.thr r four L target) k = List.replicate k.residue.val true) :
    ThrMeta a (kitShapePG a) :=
  ThrMeta.ofVec (vec11 cutS wS primeW resW hP hR)
    (fun _ _ _ _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
    (writerBound cutS)
    (fun r four L target k _ => by
      have hs := (thr_scalars cutS r four L target k).2.2.2.2.2.2.2.2.1
      refine (writerCost_le _ _ _ _ _).trans ?_
      unfold writerBound
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 4))
    (2 ^ 24 * bigC cutS ^ 4) (bigD cutS * 4) (writerBound_le cutS)

end Words

end
end NearCubicWires.PacketsCombine.Asm

