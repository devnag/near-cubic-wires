import Proof.Packets.PacketsKitSeam

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent
noncomputable section

variable {a : DecompositionAlgorithm}

/-! ## The stage contracts at the kit seam (frame form) -/

structure RowPolyStageK (X : WriterShape a) (K : KitShape a) where
  states : ℕ
  machine : Machine (10 + X.w) states
  cost : Request → ℕ
  coefficient : ℕ
  degree : ℕ
  cost_le : ∀ r, cost r ≤ coefficient * (r.smallSize a)^degree
  run : ∀ r (k : rcKey a r), k ∈ rcKeys a r → ∀ (H : Fin (10 + X.w) → ℕ) (A : Fin (10 + X.w) → List Bool),
    (∀ i : Fin (10 + X.w), i.val < 10 → i.val ≠ 1 → A i = X.layout.bank r (some k) [] i ∧ H i = 0) →
    (∀ i : Fin (10 + X.w), X.inP1 i ∨ i.val = 14 → A i = List.replicate (X.R r) false ∧ H i = 0) →
    ∃ (H' : Fin (10 + X.w) → ℕ) (A' : Fin (10 + X.w) → List Bool), Step machine (cost r) H A H' A' ∧
      A' (X.port 14 (by omega)) =
        ZeroPadding.pad (X.R r) (rowPolyWordK K r k) ∧
      H' (X.port 14 (by omega)) = 0 ∧
      ∀ i : Fin (10 + X.w), ¬ X.inP1 i → i.val ≠ 14 → A' i = A i ∧ H' i = H i

/-- **F2, the normalized lowering, reversed and serialized** for the relabel source tape. -/
structure LowerStageK (X : WriterShape a) (K : KitShape a) where
  states : ℕ
  machine : Machine (10 + X.w) states
  cost : Request → ℕ
  coefficient : ℕ
  degree : ℕ
  cost_le : ∀ r, cost r ≤ coefficient * (r.smallSize a)^degree
  run : ∀ r (k : rcKey a r), k ∈ rcKeys a r → ∀ (H : Fin (10 + X.w) → ℕ) (A : Fin (10 + X.w) → List Bool),
    A (X.port 0 (by omega)) = RepairOrdinary.frame (Request.input a r) → H (X.port 0 (by omega)) = 0 →
    A (X.port 14 (by omega)) =
      ZeroPadding.pad (X.R r) (rowPolyWordK K r k) →
    H (X.port 14 (by omega)) = 0 →
    (∀ i : Fin (10 + X.w), X.inP2 i ∨ i.val = 10 → A i = List.replicate (X.R r) false ∧ H i = 0) →
    ∃ (H' : Fin (10 + X.w) → ℕ) (A' : Fin (10 + X.w) → List Bool), Step machine (cost r) H A H' A' ∧
      A' (X.port 10 (by omega)) = ZeroPadding.pad (X.R r)
        (ExtIncidence.stream (Packets.lowered a (r.family a) (rcDecode a r k)).reverse) ∧
      H' (X.port 10 (by omega)) = 0 ∧
      ∀ i : Fin (10 + X.w), ¬ X.inP2 i → i.val ≠ 10 → A' i = A i ∧ H' i = H i

/-! ## Assembly -/

/-- The writer's four stages and the relabel fit. -/
structure WriterStagesK (X : WriterShape a) (K : KitShape a) where
  rowPoly : RowPolyStageK X K
  lower : LowerStageK X K
  prep : RelabelPrepStage X
  fit : RelabelFit X

namespace WriterStagesK
variable {X : WriterShape a} {K : KitShape a} (s : WriterStagesK X K)

def machine :=
  Composition.machine (Composition.machine (Composition.machine s.rowPoly.machine s.lower.machine)
    s.prep.machine) (RecoveryFocus.machine X.relabelSlot P1Closure.RawRelabelFamily.machine)

def cost (r : Request) : ℕ :=
  s.rowPoly.cost r + 1 + s.lower.cost r + 1 + s.prep.cost r + 1 +
    P1Closure.RawRelabelFamily.budget (relabelN a r) (relabelY a r) (s.fit.streamCap r)

/-- **The writer from its stages.** F1 ; F2 ; F3 ; docked relabel, exact on every kept port. -/
theorem write (selector : CyclicChoice.Laws) (r : Request) (k : rcKey a r) (hk : k ∈ rcKeys a r)
    (out : List Bool) :
    ∃ (H' : Fin X.layout.tapes → ℕ) (A' : Fin X.layout.tapes → List Bool),
      Step s.machine (s.cost r) (X.layout.heads out) (X.layout.bank r (some k) out) H' A' ∧
      ∀ i, X.layout.scratch i = false →
        H' i = X.layout.heads (out ++ rowWord selector a (rcFiveKeys a) r k) i ∧
        A' i = X.layout.bank r (some k) (out ++ rowWord selector a (rcFiveKeys a) r k) i := by
  have hroom := s.fit.room r
  have hR1 : 1 ≤ X.R r := by omega
  -- F1
  obtain ⟨H1, A1, s1, h1A, h1H, f1⟩ := s.rowPoly.run r k hk (X.layout.heads out)
    (X.layout.bank r (some k) out)
    (fun i hi h1 => ⟨X.bank_lo r _ out i h1, by rw [X.heads_val]; simp [h1]⟩)
    (fun i hi => by
      have h10 : 10 ≤ i.val := by
        rcases hi with hi | hi
        · exact le_trans (by omega) hi.1
        · omega
      refine ⟨X.bank_hi r _ out i h10, ?_⟩
      rw [X.heads_val]
      simp only [show i.val ≠ 1 by omega, if_false])
  -- F2
  have hA0 : ∀ i : Fin (10 + X.w), 10 ≤ i.val → X.layout.bank r (some k) out i = List.replicate (X.R r) false :=
    fun i h => X.bank_hi r _ out i h
  have hH0 : ∀ i : Fin (10 + X.w), i.val ≠ 1 → X.layout.heads out i = 0 := by
    intro i h
    rw [X.heads_val]
    simp [h]
  obtain ⟨H2, A2, s2, h2A, h2H, f2⟩ := s.lower.run r k hk H1 A1
    (by
      rw [(f1 _ (by simp [WriterShape.inP1, WriterShape.port]) (by simp [WriterShape.port])).1]
      exact X.bank_zero r _ out)
    (by
      rw [(f1 _ (by simp [WriterShape.inP1, WriterShape.port]) (by simp [WriterShape.port])).2]
      exact hH0 _ (by simp [WriterShape.port]))
    h1A h1H
    (fun i hi => by
      have hnot1 : ¬ X.inP1 i := by
        unfold WriterShape.inP1
        rcases hi with hi | hi
        · unfold WriterShape.inP2 at hi; omega
        · omega
      have hn14 : i.val ≠ 14 := by
        rcases hi with hi | hi
        · unfold WriterShape.inP2 at hi; omega
        · omega
      have h10 : 10 ≤ i.val := by
        rcases hi with hi | hi
        · unfold WriterShape.inP2 at hi; omega
        · omega
      rw [(f1 i hnot1 hn14).1, (f1 i hnot1 hn14).2]
      exact ⟨hA0 i h10, hH0 i (by omega)⟩)
  -- F3
  obtain ⟨H3, A3, s3, h3A11, h3A16, h3A18, h3H11, h3H16, h3H18, f3⟩ := s.prep.run r H2 A2
    (by
      rw [(f2 _ (by simp [WriterShape.inP2, WriterShape.port]) (by simp [WriterShape.port])).1,
        (f1 _ (by simp [WriterShape.inP1, WriterShape.port]) (by simp [WriterShape.port])).1]
      exact X.bank_zero r _ out)
    (by
      rw [(f2 _ (by simp [WriterShape.inP2, WriterShape.port]) (by simp [WriterShape.port])).2,
        (f1 _ (by simp [WriterShape.inP1, WriterShape.port]) (by simp [WriterShape.port])).2]
      exact hH0 _ (by simp [WriterShape.port]))
    (fun i hi => by
      have hv : 10 ≤ i.val ∧ i.val ≠ 10 ∧ i.val ≠ 14 ∧ ¬ X.inP1 i ∧ ¬ X.inP2 i := by
        have hi' : (19 + X.w1 + X.w2 ≤ i.val ∧ i.val < 19 + X.w1 + X.w2 + X.w3) ∨ i.val = 11 ∨
            i.val = 16 ∨ i.val = 18 := hi
        simp only [WriterShape.inP1, WriterShape.inP2]
        omega
      obtain ⟨h10, hn10, hn14, hn1, hn2⟩ := hv
      rw [(f2 i hn2 hn10).1, (f2 i hn2 hn10).2, (f1 i hn1 hn14).1, (f1 i hn1 hn14).2]
      exact ⟨hA0 i h10, hH0 i (by omega)⟩)
  -- untouched tapes after F3: everything outside all three footprints is the row-entry bank
  have keep3 : ∀ i : Fin (10 + X.w), ¬ X.inP1 i → ¬ X.inP2 i → ¬ X.inP3 i → i.val ≠ 14 → i.val ≠ 10 →
      i.val ≠ 11 → i.val ≠ 16 → i.val ≠ 18 →
      A3 i = X.layout.bank r (some k) out i ∧ H3 i = X.layout.heads out i := by
    intro i n1 n2 n3 n14 n10 n11 n16 n18
    rw [(f3 i n3 n11 n16 n18).1, (f3 i n3 n11 n16 n18).2, (f2 i n2 n10).1, (f2 i n2 n10).2,
      (f1 i n1 n14).1, (f1 i n1 n14).2]
    exact ⟨rfl, rfl⟩
  have outside : ∀ i : Fin (10 + X.w), i.val < 19 → ¬ X.inP1 i ∧ ¬ X.inP2 i ∧ ¬ X.inP3 i := by
    intro i hi
    unfold WriterShape.inP1 WriterShape.inP2 WriterShape.inP3
    omega
  have blank3 : ∀ i : Fin (10 + X.w), 10 ≤ i.val → i.val < 19 → i.val ≠ 14 → i.val ≠ 10 →
      i.val ≠ 11 → i.val ≠ 16 → i.val ≠ 18 → A3 i = List.replicate (X.R r) false ∧ H3 i = 0 := by
    intro i h10 h19 n14 n10 n11 n16 n18
    obtain ⟨o1, o2, o3⟩ := outside i h19
    rw [(keep3 i o1 o2 o3 n14 n10 n11 n16 n18).1, (keep3 i o1 o2 o3 n14 n10 n11 n16 n18).2]
    exact ⟨hA0 i h10, hH0 i (by omega)⟩
  have src3 : A3 (X.port 10 (by omega)) = ZeroPadding.pad (X.R r)
      (ExtIncidence.stream (Packets.lowered a (r.family a) (rcDecode a r k)).reverse) ∧
      H3 (X.port 10 (by omega)) = 0 := by
    have n3 : ¬ X.inP3 (X.port 10 (by omega)) := by
      simp only [WriterShape.inP3, WriterShape.port]
      omega
    rw [(f3 _ n3 (by simp [WriterShape.port]) (by simp [WriterShape.port]) (by simp [WriterShape.port])).1,
      (f3 _ n3 (by simp [WriterShape.port]) (by simp [WriterShape.port]) (by simp [WriterShape.port])).2]
    exact ⟨h2A, h2H⟩
  have out3 : A3 X.outPort = out ∧ H3 X.outPort = out.length := by
    obtain ⟨o1, o2, o3⟩ := outside X.outPort (by simp)
    rw [(keep3 _ o1 o2 o3 (by simp) (by simp) (by simp) (by simp) (by simp)).1,
      (keep3 _ o1 o2 o3 (by simp) (by simp) (by simp) (by simp) (by simp)).2]
    refine ⟨X.bank_out r _ out, ?_⟩
    rw [X.heads_val]
    simp
  -- F4
  obtain ⟨H4, A4, s4, h4A, h4H, f4⟩ := X.relabel_docked s.fit r k hk selector out H3 A3
    (by
      intro j
      fin_cases j
      · simp only [WriterShape.relabelCap]
        have hs : X.relabelSlot ⟨0, by decide⟩ = X.port 10 (by omega) := Fin.ext (by rw [X.relabelSlot_val]; rfl)
        rw [hs, src3.1]
        simp only [true_or, if_true, ZeroPadding.pad_zero]
        rfl
      · have hs : X.relabelSlot ⟨1, by decide⟩ = X.port 11 (by omega) := Fin.ext (by rw [X.relabelSlot_val]; rfl)
        rw [hs, h3A11]
        rfl
      · have hs : X.relabelSlot ⟨2, by decide⟩ = X.port 12 (by omega) := Fin.ext (by rw [X.relabelSlot_val]; rfl)
        rw [hs, (blank3 _ (by simp [WriterShape.port]) (by simp [WriterShape.port]) (by simp [WriterShape.port])
          (by simp [WriterShape.port]) (by simp [WriterShape.port]) (by simp [WriterShape.port])
          (by simp [WriterShape.port])).1]
        simp only [WriterShape.relabelCap]
        simp [P1Closure.RawRelabelFamily.familyData, P1Closure.RawRelabelRun.input,
          P1Closure.RawRelabelRun.data]
        exact (WriterShape.pad_word_zero (X.R r) hR1).symm
      · have hs : X.relabelSlot ⟨3, by decide⟩ = X.port 13 (by omega) := Fin.ext (by rw [X.relabelSlot_val]; rfl)
        rw [hs, (blank3 _ (by simp [WriterShape.port]) (by simp [WriterShape.port]) (by simp [WriterShape.port])
          (by simp [WriterShape.port]) (by simp [WriterShape.port]) (by simp [WriterShape.port])
          (by simp [WriterShape.port])).1]
        simp [WriterShape.relabelCap, P1Closure.RawRelabelFamily.familyData, P1Closure.RawRelabelRun.input,
          P1Closure.RawRelabelRun.data, P1Closure.RawRelabelUniform.capacity]
        exact (pad_replicate_false _ _ (by omega)).symm
      · have hs : X.relabelSlot ⟨4, by decide⟩ = X.outPort := Fin.ext (by rw [X.relabelSlot_val]; rfl)
        rw [hs, out3.1]
        rw [show X.relabelCap r ⟨4, by decide⟩ = 0 from rfl, ZeroPadding.pad_zero]
        rfl
      · have hs : X.relabelSlot ⟨5, by decide⟩ = X.port 15 (by omega) := Fin.ext (by rw [X.relabelSlot_val]; rfl)
        rw [hs, (blank3 _ (by simp [WriterShape.port]) (by simp [WriterShape.port]) (by simp [WriterShape.port])
          (by simp [WriterShape.port]) (by simp [WriterShape.port]) (by simp [WriterShape.port])
          (by simp [WriterShape.port])).1]
        simp [WriterShape.relabelCap, P1Closure.RawRelabelFamily.familyData, P1Closure.RawRelabelRun.input,
          P1Closure.RawRelabelRun.data]
        exact (pad_replicate_false _ _ (by omega)).symm
      · have hs : X.relabelSlot ⟨6, by decide⟩ = X.port 16 (by omega) := Fin.ext (by rw [X.relabelSlot_val]; rfl)
        rw [hs, h3A16]
        rfl
      · have hs : X.relabelSlot ⟨7, by decide⟩ = X.port 17 (by omega) := Fin.ext (by rw [X.relabelSlot_val]; rfl)
        rw [hs, (blank3 _ (by simp [WriterShape.port]) (by simp [WriterShape.port]) (by simp [WriterShape.port])
          (by simp [WriterShape.port]) (by simp [WriterShape.port]) (by simp [WriterShape.port])
          (by simp [WriterShape.port])).1]
        simp [WriterShape.relabelCap, P1Closure.RawRelabelFamily.familyData, P1Closure.RawRelabelRun.input,
          P1Closure.RawRelabelRun.data, P1Closure.RawRelabelUniform.capacity]
        exact (pad_replicate_false _ _ (by omega)).symm
      · have hs : X.relabelSlot ⟨8, by decide⟩ = X.port 18 (by omega) := Fin.ext (by rw [X.relabelSlot_val]; rfl)
        rw [hs, h3A18]
        rfl)
    (by
      intro j
      fin_cases j
      · have hs : X.relabelSlot ⟨0, by decide⟩ = X.port 10 (by omega) := Fin.ext (by rw [X.relabelSlot_val]; rfl)
        rw [hs, src3.2]
        rfl
      · have hs : X.relabelSlot ⟨1, by decide⟩ = X.port 11 (by omega) := Fin.ext (by rw [X.relabelSlot_val]; rfl)
        rw [hs, h3H11]
        rfl
      · have hs : X.relabelSlot ⟨2, by decide⟩ = X.port 12 (by omega) := Fin.ext (by rw [X.relabelSlot_val]; rfl)
        rw [hs, (blank3 _ (by simp [WriterShape.port]) (by simp [WriterShape.port]) (by simp [WriterShape.port])
          (by simp [WriterShape.port]) (by simp [WriterShape.port]) (by simp [WriterShape.port])
          (by simp [WriterShape.port])).2]
        rfl
      · have hs : X.relabelSlot ⟨3, by decide⟩ = X.port 13 (by omega) := Fin.ext (by rw [X.relabelSlot_val]; rfl)
        rw [hs, (blank3 _ (by simp [WriterShape.port]) (by simp [WriterShape.port]) (by simp [WriterShape.port])
          (by simp [WriterShape.port]) (by simp [WriterShape.port]) (by simp [WriterShape.port])
          (by simp [WriterShape.port])).2]
        rfl
      · have hs : X.relabelSlot ⟨4, by decide⟩ = X.outPort := Fin.ext (by rw [X.relabelSlot_val]; rfl)
        rw [hs, out3.2]
        rfl
      · have hs : X.relabelSlot ⟨5, by decide⟩ = X.port 15 (by omega) := Fin.ext (by rw [X.relabelSlot_val]; rfl)
        rw [hs, (blank3 _ (by simp [WriterShape.port]) (by simp [WriterShape.port]) (by simp [WriterShape.port])
          (by simp [WriterShape.port]) (by simp [WriterShape.port]) (by simp [WriterShape.port])
          (by simp [WriterShape.port])).2]
        rfl
      · have hs : X.relabelSlot ⟨6, by decide⟩ = X.port 16 (by omega) := Fin.ext (by rw [X.relabelSlot_val]; rfl)
        rw [hs, h3H16]
        rfl
      · have hs : X.relabelSlot ⟨7, by decide⟩ = X.port 17 (by omega) := Fin.ext (by rw [X.relabelSlot_val]; rfl)
        rw [hs, (blank3 _ (by simp [WriterShape.port]) (by simp [WriterShape.port]) (by simp [WriterShape.port])
          (by simp [WriterShape.port]) (by simp [WriterShape.port]) (by simp [WriterShape.port])
          (by simp [WriterShape.port])).2]
        rfl
      · have hs : X.relabelSlot ⟨8, by decide⟩ = X.port 18 (by omega) := Fin.ext (by rw [X.relabelSlot_val]; rfl)
        rw [hs, h3H18]
        rfl)
  refine ⟨H4, A4, ((s1.seq s2).seq s3).seq s4, ?_⟩
  intro i hi
  have hi10 : i.val < 10 := by simpa [WriterShape.layout, digitLayout] using hi
  by_cases h1 : i.val = 1
  · have he : i = X.outPort := Fin.ext h1
    rw [he]
    refine ⟨?_, ?_⟩
    · rw [h4H, X.heads_val]
      simp
    · rw [h4A, X.bank_out]
  · have hslot : ∀ j, X.relabelSlot j ≠ i := by
      intro j hj
      have := congrArg Fin.val hj
      rw [X.relabelSlot_val] at this
      split_ifs at this <;> omega
    obtain ⟨o1, o2, o3⟩ := outside i (by omega)
    obtain ⟨k1, k2⟩ := keep3 i o1 o2 o3 (by omega) (by omega) (by omega) (by omega) (by omega)
    refine ⟨?_, ?_⟩
    · rw [(f4 i hslot).2, k2, X.heads_val, X.heads_val]
      simp [h1]
    · rw [(f4 i hslot).1, k1, X.bank_lo r _ out i h1]
      exact (X.bank_lo r _ _ i h1).symm

end WriterStagesK

namespace WriterStagesK
variable {X : WriterShape a} {K : KitShape a} (s : WriterStagesK X K)

def coefficient : ℕ :=
  s.rowPoly.coefficient + s.lower.coefficient + s.prep.coefficient + 3 +
    128 * ((s.fit.capCoefficient + 3) * (s.fit.capCoefficient + 3) * (s.fit.capCoefficient + 3) *
      (s.fit.capCoefficient + 3))

def degree : ℕ := s.rowPoly.degree + s.lower.degree + s.prep.degree + 4 * (s.fit.capDegree + 1)

theorem cost_le (r : Request) : s.cost r ≤ s.coefficient * (r.smallSize a)^s.degree := by
  have hs := RCFive.PacketBounds.positive a r
  set sz := r.smallSize a with hsz
  have hmono : ∀ d, d ≤ s.degree → sz^d ≤ sz^s.degree := fun d hd => Nat.pow_le_pow_right hs hd
  have hP1 : 1 ≤ sz^(s.fit.capDegree + 1) := Nat.one_le_pow _ _ hs
  have hszP : sz ≤ sz^(s.fit.capDegree + 1) := Nat.le_self_pow (by omega) _
  have hSP : s.fit.streamCap r ≤ s.fit.capCoefficient * sz^(s.fit.capDegree + 1) :=
    (s.fit.cap_le r).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hs (by omega)))
  have hPD : sz^(s.fit.capDegree + 1) * sz^(s.fit.capDegree + 1) * sz^(s.fit.capDegree + 1) *
      sz^(s.fit.capDegree + 1) ≤ sz^s.degree := by
    rw [← pow_add, ← pow_add, ← pow_add]
    exact hmono _ (by unfold degree; omega)
  have hx1 : s.rowPoly.cost r ≤ s.rowPoly.coefficient * sz^s.degree :=
    (s.rowPoly.cost_le r).trans (Nat.mul_le_mul_left _ (hmono _ (by unfold degree; omega)))
  have hx2 : s.lower.cost r ≤ s.lower.coefficient * sz^s.degree :=
    (s.lower.cost_le r).trans (Nat.mul_le_mul_left _ (hmono _ (by unfold degree; omega)))
  have hx3 : s.prep.cost r ≤ s.prep.coefficient * sz^s.degree :=
    (s.prep.cost_le r).trans (Nat.mul_le_mul_left _ (hmono _ (by unfold degree; omega)))
  have hD : 1 ≤ sz^s.degree := Nat.one_le_pow _ _ hs
  have hB := relabel_budget_le (relabelN a r) (relabelY a r) (s.fit.streamCap r)
  exact cost_arith s.rowPoly.coefficient s.lower.coefficient s.prep.coefficient s.fit.capCoefficient
    (s.rowPoly.cost r) (s.lower.cost r) (s.prep.cost r) _ (s.fit.streamCap r) (relabelN a r) (relabelY a r)
    sz _ _ hP1 ((relabelN_le r).trans hszP) ((relabelY_le r).trans hszP) hSP hB hx1 hx2 hx3 hPD hD rfl

/-- **The consumer's writer field**, from the four stages. -/
def rowWriter (selector : CyclicChoice.Laws) : RowWriter selector X.layout where
  states := _
  machine := s.machine
  cost := s.cost
  coefficient := s.coefficient
  degree := s.degree
  cost_le := s.cost_le
  write := fun r k hk out => s.write selector r k hk out

end WriterStagesK

end
end NearCubicWires.PacketsConstruction
