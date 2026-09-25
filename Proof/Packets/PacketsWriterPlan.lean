import Proof.CaseAnalysis.FivePacketBounds
import Proof.Packets.PacketsLayout
import Proof.Packets.PacketsRelabelRoute

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

/-- The writer's bank shape: three private regions and the scrub width `R`. -/
structure WriterShape (a : DecompositionAlgorithm) where
  w1 : ℕ
  w2 : ℕ
  w3 : ℕ
  R : Request → ℕ
  cR : ℕ
  dR : ℕ
  hR : ∀ r, R r ≤ cR * (r.smallSize a)^dR

namespace WriterShape
variable {a : DecompositionAlgorithm} (X : WriterShape a)

abbrev w : ℕ := 9 + X.w1 + X.w2 + X.w3

def layout : Layout a (rcFiveKeys a) := digitLayout a X.w X.R X.cR X.dR X.hR

def inP1 (i : Fin (10 + X.w)) : Prop := 19 ≤ i.val ∧ i.val < 19 + X.w1
def inP2 (i : Fin (10 + X.w)) : Prop := 19 + X.w1 ≤ i.val ∧ i.val < 19 + X.w1 + X.w2
def inP3 (i : Fin (10 + X.w)) : Prop := 19 + X.w1 + X.w2 ≤ i.val ∧ i.val < 19 + X.w1 + X.w2 + X.w3

/-- Fixed ports. -/
def port (n : ℕ) (h : n < 19) : Fin (10 + X.w) := ⟨n, by unfold WriterShape.w; omega⟩

/-- Relabel tape `j` sits at `10 + j`, except its output tape 4, which is the layout's output. -/
def relabelSlot : Fin 9 → Fin (10 + X.w) :=
  fun j => if j.val = 4 then ⟨1, by omega⟩ else ⟨10 + j.val, by unfold WriterShape.w; omega⟩

theorem relabelSlot_val (j : Fin 9) : (X.relabelSlot j).val = if j.val = 4 then 1 else 10 + j.val := by
  unfold relabelSlot
  split_ifs <;> rfl

theorem relabelSlot_injective : Function.Injective X.relabelSlot := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [relabelSlot_val, relabelSlot_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

/-- The layout's output port, as a closed term. -/
def outPort : Fin (10 + X.w) := ⟨1, Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right 10 _)⟩

@[simp] theorem outPort_val : X.outPort.val = 1 := rfl

theorem ne_output (i : Fin X.layout.tapes) (h : i.val ≠ 1) : ¬ (i = X.layout.output) :=
  fun he => h (by rw [he]; rfl)

theorem bank_hi (r : Request) (c : Option (rcKey a r)) (out : List Bool) (i : Fin X.layout.tapes)
    (h : 10 ≤ i.val) : X.layout.bank r c out i = List.replicate (X.R r) false := by
  have hne := X.ne_output i (by omega)
  have hs : X.layout.scratch i = true := by simp [WriterShape.layout, digitLayout, h]
  unfold Layout.bank
  simp only [hne, hs, if_false, if_true]
  rfl

theorem bank_lo (r : Request) (c : Option (rcKey a r)) (out : List Bool) (i : Fin X.layout.tapes)
    (h1 : i.val ≠ 1) : X.layout.bank r c out i = X.layout.bank r c [] i := by
  have hne := X.ne_output i h1
  unfold Layout.bank
  simp only [hne, if_false]

theorem bank_zero (r : Request) (c : Option (rcKey a r)) (out : List Bool) :
    X.layout.bank r c out (X.port 0 (by omega)) = RepairOrdinary.frame (Request.input a r) := by
  have hne := X.ne_output (X.port 0 (by omega)) (by simp [port])
  have hs : X.layout.scratch (X.port 0 (by omega)) = false := by simp [WriterShape.layout, digitLayout, port]
  have hc : X.layout.cursorPort (X.port 0 (by omega)) = false := by
    simp [WriterShape.layout, digitLayout, port]
  unfold Layout.bank
  simp only [hne, hs, hc, if_false, Bool.false_eq_true]
  simp [WriterShape.layout, digitLayout, port]

theorem bank_out (r : Request) (c : Option (rcKey a r)) (out : List Bool) :
    X.layout.bank r c out X.outPort = out := by
  have he : (X.outPort : Fin X.layout.tapes) = X.layout.output := rfl
  unfold Layout.bank
  simp only [he, if_true]

theorem heads_val (out : List Bool) (i : Fin X.layout.tapes) :
    X.layout.heads out i = if i.val = 1 then out.length else 0 := by
  unfold Layout.heads
  by_cases h : i.val = 1
  · have he : i = X.layout.output := Fin.ext h
    simp only [he, if_true]
    rfl
  · simp only [X.ne_output i h, h, if_false]

end WriterShape

/-- The relabel stage's sizes at a request: pooled children `N` and live assignments `2^K`. -/
abbrev relabelN (a : DecompositionAlgorithm) (r : Request) : ℕ := childCount a (r.family a)
abbrev relabelY (a : DecompositionAlgorithm) (r : Request) : ℕ := 2 ^ (Packets.live (r.family a)).card

/-! ## The stage contracts (frame form) -/

variable {a : DecompositionAlgorithm}

/-- **F3, the relabel drivers** (request constants `N`, `2^K`). -/
structure RelabelPrepStage (X : WriterShape a) where
  states : ℕ
  machine : Machine (10 + X.w) states
  cost : Request → ℕ
  coefficient : ℕ
  degree : ℕ
  cost_le : ∀ r, cost r ≤ coefficient * (r.smallSize a)^degree
  run : ∀ r (H : Fin (10 + X.w) → ℕ) (A : Fin (10 + X.w) → List Bool),
    A (X.port 0 (by omega)) = RepairOrdinary.frame (Request.input a r) → H (X.port 0 (by omega)) = 0 →
    (∀ i : Fin (10 + X.w), X.inP3 i ∨ i.val = 11 ∨ i.val = 16 ∨ i.val = 18 →
      A i = List.replicate (X.R r) false ∧ H i = 0) →
    ∃ (H' : Fin (10 + X.w) → ℕ) (A' : Fin (10 + X.w) → List Bool), Step machine (cost r) H A H' A' ∧
      A' (X.port 11 (by omega)) = ZeroPadding.pad (X.R r) (List.replicate (relabelN a r) true) ∧
      A' (X.port 16 (by omega)) = ZeroPadding.pad (X.R r) (List.replicate (relabelN a r * relabelY a r + 2) true) ∧
      A' (X.port 18 (by omega)) = ZeroPadding.pad (X.R r) (CompareMachine.word (relabelY a r)) ∧
      H' (X.port 11 (by omega)) = 0 ∧ H' (X.port 16 (by omega)) = 0 ∧ H' (X.port 18 (by omega)) = 1 ∧
      ∀ i : Fin (10 + X.w), ¬ X.inP3 i → i.val ≠ 11 → i.val ≠ 16 → i.val ≠ 18 → A' i = A i ∧ H' i = H i

/-- The relabel source bound and the width's room for every relabel tape. -/
structure RelabelFit (X : WriterShape a) where
  streamCap : Request → ℕ
  capCoefficient : ℕ
  capDegree : ℕ
  cap_le : ∀ r, streamCap r ≤ capCoefficient * (r.smallSize a)^capDegree
  stream_le : ∀ r (k : rcKey a r), k ∈ rcKeys a r →
    (ExtIncidence.stream (Packets.lowered a (r.family a) (rcDecode a r k)).reverse).length ≤ streamCap r
  room : ∀ r, P1Closure.RawRelabelUniform.logCapacity (relabelN a r) (relabelY a r) (streamCap r) +
    (relabelN a r * relabelY a r + 3) + (relabelY a r + 1) + 1 ≤ X.R r

namespace WriterShape
variable (X : WriterShape a)

/-- Padding per relabel tape: the source and output are exact; every other tape is backed to `R`. -/
def relabelCap (r : Request) (j : Fin 9) : ℕ := if j.val = 0 ∨ j.val = 4 then 0 else X.R r

theorem pad_word_zero (R : ℕ) (hR : 1 ≤ R) : ZeroPadding.pad R (CompareMachine.word 0) = List.replicate R false := by
  have h : CompareMachine.word 0 = List.replicate 1 false := rfl
  rw [h]
  exact pad_replicate_false R 1 hR

theorem relabel_docked (fit : RelabelFit X) (r : Request) (k : rcKey a r) (hk : k ∈ rcKeys a r)
    (selector : CyclicChoice.Laws) (out : List Bool)
    (H : Fin (10 + X.w) → ℕ) (A : Fin (10 + X.w) → List Bool)
    (hA : ∀ j : Fin 9, A (X.relabelSlot j) = ZeroPadding.pad (X.relabelCap r j)
      (P1Closure.RawRelabelFamily.familyData (relabelN a r) (relabelY a r) (fit.streamCap r) 0
        (Packets.lowered a (r.family a) (rcDecode a r k)).reverse
        (List.replicate (X.R r - (ExtIncidence.stream
          (Packets.lowered a (r.family a) (rcDecode a r k)).reverse).length) false) out j))
    (hH : ∀ j : Fin 9, H (X.relabelSlot j) = P1Closure.RawRelabelFamily.familyHeads out j) :
    ∃ (H' : Fin (10 + X.w) → ℕ) (A' : Fin (10 + X.w) → List Bool),
      Step (RecoveryFocus.machine X.relabelSlot P1Closure.RawRelabelFamily.machine)
        (P1Closure.RawRelabelFamily.budget (relabelN a r) (relabelY a r) (fit.streamCap r)) H A H' A' ∧
      A' X.outPort = out ++ rowWord selector a (rcFiveKeys a) r k ∧
      H' X.outPort = (out ++ rowWord selector a (rcFiveKeys a) r k).length ∧
      ∀ i : Fin (10 + X.w), (∀ j, X.relabelSlot j ≠ i) → A' i = A i ∧ H' i = H i := by
  have hrun := relabel_writes_rowWord a (r.family a) (Packets.geometry selector (r.family a))
    (rcDecode a r k) (fit.streamCap r)
    (List.replicate (X.R r - (ExtIncidence.stream
      (Packets.lowered a (r.family a) (rcDecode a r k)).reverse).length) false) out
    (fit.stream_le r k hk)
  have hpad := hrun.pad (X.relabelCap r)
  have hdock := hpad.dock X.relabelSlot X.relabelSlot_injective H A hH hA
  refine ⟨_, _, hdock, ?_, ?_, ?_⟩
  · have h4 : X.outPort = X.relabelSlot 4 := by
      apply Fin.ext
      rw [relabelSlot_val]
      rfl
    rw [h4, install_slot _ X.relabelSlot_injective]
    have hc : X.relabelCap r 4 = 0 := by simp [relabelCap]
    simp only [hc, ZeroPadding.pad_zero]
    rfl
  · have h4 : X.outPort = X.relabelSlot 4 := by
      apply Fin.ext
      rw [relabelSlot_val]
      rfl
    rw [h4, dockH_slot _ X.relabelSlot_injective]
    rfl
  · intro i hi
    exact ⟨install_other _ _ _ i hi, dockH_other _ _ _ i hi⟩

end WriterShape

/-! ## Assembly -/

namespace WriterStages

end WriterStages

/-! ### Cost: every stage and the relabel loop are fixed powers of `smallSize` -/

theorem relabelY_le (r : Request) : relabelY a r ≤ r.smallSize a := by
  dsimp only [relabelY, Request.smallSize]
  generalize (2:Nat)^(Packets.live (r.family a)).card = livePower
  generalize (2:Nat)^(SupplierWalkBridge.canonicalWalkLength (r.denominator a)) = walkPower
  omega

theorem relabelN_le (r : Request) : relabelN a r ≤ r.smallSize a := by
  have h1 : Packets.alphabet a (r.family a) ≤ (Packets.alphabet a (r.family a))^(r.degree a + 1) :=
    Nat.le_self_pow (by omega) _
  have h2 : relabelN a r + 2 = Packets.alphabet a (r.family a) := rfl
  have h3 : (Packets.alphabet a (r.family a))^(r.degree a + 1) ≤ r.smallSize a := by
    dsimp only [Request.smallSize]
    generalize (2:Nat)^(Packets.live (r.family a)).card = livePower
    generalize (2:Nat)^(SupplierWalkBridge.canonicalWalkLength (r.denominator a)) = walkPower
    omega
  omega

theorem cost_arith (c1 c2 c3 cS x1 x2 x3 B S N Y s P D : ℕ) (hP1 : 1 ≤ P)
    (hN : N ≤ P) (hY : Y ≤ P) (hS : S ≤ cS * P) (hB : B ≤ 128 * ((N + Y + S + 1) * (N + Y + S + 1) *
      (N + Y + S + 1) * (N + Y + S + 1)))
    (hx1 : x1 ≤ c1 * D) (hx2 : x2 ≤ c2 * D) (hx3 : x3 ≤ c3 * D) (hPD : P * P * P * P ≤ D) (hD : 1 ≤ D)
    (_hs : s = s) :
    x1 + 1 + x2 + 1 + x3 + 1 + B ≤ (c1 + c2 + c3 + 3 + 128 * ((cS + 3) * (cS + 3) * (cS + 3) * (cS + 3))) * D := by
  have hM : N + Y + S + 1 ≤ (cS + 3) * P := by nlinarith
  have hM4 : (N + Y + S + 1) * (N + Y + S + 1) * (N + Y + S + 1) * (N + Y + S + 1) ≤
      ((cS + 3) * P) * ((cS + 3) * P) * ((cS + 3) * P) * ((cS + 3) * P) :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hM hM) hM) hM
  have he : ((cS + 3) * P) * ((cS + 3) * P) * ((cS + 3) * P) * ((cS + 3) * P) =
      ((cS + 3) * (cS + 3) * (cS + 3) * (cS + 3)) * (P * P * P * P) := by ring
  have hC : ((cS + 3) * (cS + 3) * (cS + 3) * (cS + 3)) * (P * P * P * P) ≤
      ((cS + 3) * (cS + 3) * (cS + 3) * (cS + 3)) * D := Nat.mul_le_mul_left _ hPD
  nlinarith

namespace WriterStages

end WriterStages

end
end NearCubicWires.PacketsConstruction
