import Proof.Packets.PacketsCoordDock
import Proof.Packets.PacketsConeRunReq
import Proof.Packets.PacketsMetaVec

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.Residual
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction
noncomputable section

variable {a : DecompositionAlgorithm}

/-! ## The per-key words -/

section Words
variable (a : DecompositionAlgorithm)

/-- The number of masks of a key (SYM: circuits; THR: residue digits of the key's prime). -/
def maskCount (r : Request) (k : rcKey a r) : ℕ := (MaskCoord.maskCoordsList a r k).length

/-- The masks' bits, in the coordinate order. -/
def maskBitsList : ∀ r : Request, rcKey a r → List (List Bool)
  | .terminal, k => PEmpty.elim k
  | .sym r _ _ _, _ => (symMasks r).map (MaskCoord.maskBits (symmetricFourfoldOccurrences r))
  | .thr r _ L target, k =>
      (thrMasks a r L target k).map (MaskCoord.maskBits (thresholdFourfoldOccurrences r))

/-- The walk's labels word of the key's seed (`labelsWord`, `160·(t-1)` bits). -/
def labelsOf : ∀ r : Request, rcKey a r → List Bool
  | .terminal, k => PEmpty.elim k
  | .sym r _ L target, k => MaskCoord.labelsWord (symmetricFourfoldOccurrences r)
      (CyclicChoice.live (symmetricFourfoldOccurrences r) L) (symmetricListDenominator r target) k.seed
  | .thr r _ L target, k => MaskCoord.labelsWord (thresholdFourfoldOccurrences r)
      (CyclicChoice.live (thresholdFourfoldOccurrences r) L)
      (CloseoutFinalC10ThresholdRows.listDenominator a r target) k.seed

/-- The walk's start coordinates of the key's seed (framed binary). -/
def startXOf : ∀ r : Request, rcKey a r → List Bool
  | .terminal, k => PEmpty.elim k
  | .sym r _ L target, k => MaskCoord.startX (symmetricFourfoldOccurrences r)
      (CyclicChoice.live (symmetricFourfoldOccurrences r) L) (symmetricListDenominator r target) k.seed
  | .thr r _ L target, k => MaskCoord.startX (thresholdFourfoldOccurrences r)
      (CyclicChoice.live (thresholdFourfoldOccurrences r) L)
      (CloseoutFinalC10ThresholdRows.listDenominator a r target) k.seed

def startYOf : ∀ r : Request, rcKey a r → List Bool
  | .terminal, k => PEmpty.elim k
  | .sym r _ L target, k => MaskCoord.startY (symmetricFourfoldOccurrences r)
      (CyclicChoice.live (symmetricFourfoldOccurrences r) L) (symmetricListDenominator r target) k.seed
  | .thr r _ L target, k => MaskCoord.startY (thresholdFourfoldOccurrences r)
      (CyclicChoice.live (thresholdFourfoldOccurrences r) L)
      (CloseoutFinalC10ThresholdRows.listDenominator a r target) k.seed

theorem maskBitsList_length (r : Request) (k : rcKey a r) : (maskBitsList a r k).length = maskCount a r k := by
  cases r with
  | terminal => exact PEmpty.elim k
  | sym r0 four L target => simp [maskBitsList, maskCount, MaskCoord.maskCoordsList]
  | thr r0 four L target => simp [maskBitsList, maskCount, MaskCoord.maskCoordsList]

end Words

/-! ## The hole types -/

/-- The key-stage entry: `metaEntry` (framed input, key fields 1–8) with unary `j` on tape 9. -/
def keyEntry (a : DecompositionAlgorithm) (r : Request) (k : rcKey a r) (j t : ℕ) (i : Fin t) : List Bool :=
  if i.val = 9 then List.replicate j true else PacketsCombine.metaEntry a r (some k) t i

/-- **A key-level word** (one fixed machine): from `metaEntry a r (some k)` (tapes 0–8; tapes `≥ 9` empty, heads 0)
it writes `v r k` on tape 9 at head 0, keeps tapes 0–8 and their heads; private tapes existential. -/
structure KeyWord (a : DecompositionAlgorithm) (v : ∀ r : Request, rcKey a r → List Bool) where
  extra : ℕ
  states : ℕ
  machine : Machine (10 + extra) states
  cost : Request → ℕ
  costC : ℕ
  costD : ℕ
  cost_le : ∀ r, cost r ≤ costC * (r.smallSize a) ^ costD
  run : ∀ r (k : rcKey a r), k ∈ rcKeys a r →
    ∃ (H : Fin (10 + extra) → ℕ) (A : Fin (10 + extra) → List Bool),
      Step machine (cost r) (fun _ => 0) (PacketsCombine.metaEntry a r (some k) (10 + extra)) H A ∧
      (∀ i : Fin (10 + extra), i.val < 9 → A i = PacketsCombine.metaEntry a r (some k) (10 + extra) i ∧ H i = 0) ∧
      A ⟨9, by omega⟩ = v r k ∧ H ⟨9, by omega⟩ = 0

/-- **A key-and-mask-level word** (one fixed machine): from `keyEntry a r k j` (unary `j` on tape 9, tapes `≥ 10`
empty, heads 0), for every mask index `j < maskCount a r k`, it writes `v r k j` on tape 10 at head 0, keeps tapes
0–9 and their heads; private tapes existential. -/
structure KeyStage (a : DecompositionAlgorithm) (v : ∀ r : Request, rcKey a r → ℕ → List Bool) where
  extra : ℕ
  states : ℕ
  machine : Machine (11 + extra) states
  cost : Request → ℕ
  costC : ℕ
  costD : ℕ
  cost_le : ∀ r, cost r ≤ costC * (r.smallSize a) ^ costD
  run : ∀ r (k : rcKey a r), k ∈ rcKeys a r → ∀ j, j < maskCount a r k →
    ∃ (H : Fin (11 + extra) → ℕ) (A : Fin (11 + extra) → List Bool),
      Step machine (cost r) (fun _ => 0) (keyEntry a r k j (11 + extra)) H A ∧
      (∀ i : Fin (11 + extra), i.val < 10 → A i = keyEntry a r k j (11 + extra) i ∧ H i = 0) ∧
      A ⟨10, by omega⟩ = v r k j ∧ H ⟨10, by omega⟩ = 0

/-- The append stage's entry: source `pad Q v` (tape 0), output `out` (tape 1), driver `1^|v|` (tape 2). -/
def appendEntry (Q : ℕ) (v out : List Bool) (t : ℕ) (i : Fin t) : List Bool :=
  if i.val = 0 then ZeroPadding.pad Q v else if i.val = 1 then out
  else if i.val = 2 then List.replicate v.length true else []

structure AppendStage where
  extra : ℕ
  states : ℕ
  machine : Machine (3 + extra) states
  cost : ℕ → ℕ
  costC : ℕ
  costD : ℕ
  cost_le : ∀ n, cost n ≤ costC * (n + 1) ^ costD
  run : ∀ (Q : ℕ) (v out : List Bool), v.length ≤ Q →
    ∃ (H : Fin (3 + extra) → ℕ) (A : Fin (3 + extra) → List Bool),
      Step machine (cost v.length) (fun i => if i.val = 1 then out.length else 0) (appendEntry Q v out (3 + extra))
        H A ∧
      A ⟨1, by omega⟩ = out ++ v ∧ H ⟨1, by omega⟩ = (out ++ v).length ∧
      A ⟨2, by omega⟩ = List.replicate v.length true ∧ H ⟨2, by omega⟩ = 0

section Adapter
variable {w : Request → List Bool} (s : PacketsGlue.RequestMeta.WordStage a w)

/-- Local `0 ↦ 0`, `1 ↦ 9`, private `2 + i ↦ 10 + i`. -/
def wordSlot (j : Fin (2 + s.extra)) : Fin (10 + s.extra) :=
  ⟨if j.val = 0 then 0 else if j.val = 1 then 9 else j.val + 8, by have := j.isLt; split_ifs <;> omega⟩

theorem wordSlot_val (j : Fin (2 + s.extra)) :
    (wordSlot s j).val = if j.val = 0 then 0 else if j.val = 1 then 9 else j.val + 8 := rfl

theorem wordSlot_injective : Function.Injective (wordSlot s) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [wordSlot_val, wordSlot_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

def KeyWord.ofWord : KeyWord a (fun r _ => w r) where
  extra := s.extra
  states := _
  machine := RecoveryFocus.machine (wordSlot s) s.machine
  cost := s.cost
  costC := s.coefficient
  costD := s.degree
  cost_le := s.cost_le
  run := fun r k _ => by
    obtain ⟨H1, A1, hs, h0A, h0H, h1A, h1H⟩ := s.run r
    obtain ⟨H', A', st, hslot, hother⟩ := Dock.lift hs (wordSlot s) (wordSlot_injective s) (fun _ => 0)
      (fun _ => 0) (PacketsCombine.metaEntry a r (some k) (10 + s.extra)) (by
        intro j
        refine ⟨rfl, ?_⟩
        rw [ZeroPadding.pad_zero]
        simp only [inBank, PacketsCombine.metaEntry, wordSlot_val]
        by_cases h0 : j.val = 0
        · simp [h0]
        · by_cases h1 : j.val = 1
          · simp [h1]
          · have h2 : ¬ (j.val + 8 = 0) := by omega
            have h3 : ¬ (1 ≤ j.val + 8 ∧ j.val + 8 ≤ 8) := by omega
            simp only [h0, h1, h2, h3, if_false, dite_false])
    refine ⟨H', A', st, ?_, ?_, ?_⟩
    · intro i hi
      by_cases h0 : i.val = 0
      · have he : i = wordSlot s ⟨0, by omega⟩ := Fin.ext (by rw [wordSlot_val]; simpa using h0)
        rw [he, (hslot _).1, (hslot _).2, ZeroPadding.pad_zero]
        refine ⟨?_, h0H⟩
        rw [h0A]
        simp [PacketsCombine.metaEntry, wordSlot_val]
      · have hn : ∀ j, wordSlot s j ≠ i := by
          intro j hj
          have hv := congrArg Fin.val hj
          rw [wordSlot_val] at hv
          split_ifs at hv <;> omega
        exact ⟨(hother i hn).2, (hother i hn).1⟩
    · have he : (⟨9, by omega⟩ : Fin (10 + s.extra)) = wordSlot s ⟨1, by omega⟩ := Fin.ext (by rw [wordSlot_val]; rfl)
      rw [he, (hslot _).2, ZeroPadding.pad_zero]
      exact h1A
    · have he : (⟨9, by omega⟩ : Fin (10 + s.extra)) = wordSlot s ⟨1, by omega⟩ := Fin.ext (by rw [wordSlot_val]; rfl)
      rw [he, (hslot _).1]
      exact h1H

end Adapter

end
end NearCubicWires.PacketsConstruction.Residual
