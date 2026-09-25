import Proof.Packets.PacketsCombineMeaning
import Proof.Packets.PacketsKitBoot
import Proof.Packets.PacketsRowPolySplitKit

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsCombine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrime NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction
open NormalizedFiniteTransport Theorem25Completion.CycleBounds
noncomputable section

/-! ## Per-key words -/

/-- The key field word of field `f` (the writer's cursor tape `2 + f`, `digitLayout.cursor`). -/
def keyWord (a : DecompositionAlgorithm) (r : Request) (c : Option (rcKey a r)) (f : Fin 8) : List Bool :=
  RepairOrdinary.frame (SignedSortKey.binary (fieldWidth a r) (keyDigits a r c f))

/-- The entry bank of a metadata machine on `t` tapes: framed input on `0`, key fields on `1..8`. -/
def metaEntry (a : DecompositionAlgorithm) (r : Request) (c : Option (rcKey a r)) (t : ℕ) (i : Fin t) : List Bool :=
  if i.val = 0 then RepairOrdinary.frame (Request.input a r)
  else if h : 1 ≤ i.val ∧ i.val ≤ 8 then keyWord a r c ⟨i.val - 1, by omega⟩ else []

/-- The SYM lookup bits: circuit-major, candidate-minor `shiftedFiniteLookup (offset i) (topLookup i)`. -/
def symBitsWord (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (L target : ℕ)
    (k : RCFive.RowKeys.SymKey r L target) : List Bool :=
  (List.ofFn (fun i : Fin r.circuits.length =>
    List.ofFn (shiftedFiniteLookup (population := (symmetricFourfoldOccurrences r).length) (k.offset i)
      (symmetricCircuitTopLookup r i)))).flatten

/-- **The SYM metadata contract** (hypothesis of the assembly; one fixed machine). From the framed
input and the key fields (all else empty, heads 0) it keeps tapes `0..8` and writes, heads 0 except the
bits: templates of `C`, `C`, `w`, `m = pop+1`, `n = #circuits`, `n*m` on `9..14`, and the lookup bits
on `15` with head at `n*m` (the SYM engine's starting cursor). Private tapes `16..` existential. -/
structure SymMeta (a : DecompositionAlgorithm) (K : KitShape a) where
  extra : ℕ
  states : ℕ
  machine : Machine (16 + extra) states
  cost : Request → ℕ
  coefficient : ℕ
  degree : ℕ
  cost_le : ∀ r, cost r ≤ coefficient * (r.smallSize a) ^ degree
  run : ∀ (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : ℕ) (k : RCFive.RowKeys.SymKey r L target), k ∈ RCFive.RowKeys.symKeys r L target →
    ∃ (H : Fin (16 + extra) → ℕ) (A : Fin (16 + extra) → List Bool),
      Step machine (cost (.sym r four L target)) (fun _ => 0)
        (metaEntry a (.sym r four L target) (some k) (16 + extra)) H A ∧
      (∀ i : Fin (16 + extra), i.val ≤ 8 →
        A i = metaEntry a (.sym r four L target) (some k) (16 + extra) i ∧ H i = 0) ∧
      A ⟨9, by omega⟩ = UnaryTemplate.tape (K.C (.sym r four L target)) ∧ H ⟨9, by omega⟩ = 0 ∧
      A ⟨10, by omega⟩ = UnaryTemplate.tape (K.C (.sym r four L target)) ∧ H ⟨10, by omega⟩ = 0 ∧
      A ⟨11, by omega⟩ = UnaryTemplate.tape (K.w (.sym r four L target)) ∧ H ⟨11, by omega⟩ = 0 ∧
      A ⟨12, by omega⟩ = UnaryTemplate.tape ((symmetricFourfoldOccurrences r).length + 1) ∧ H ⟨12, by omega⟩ = 0 ∧
      A ⟨13, by omega⟩ = UnaryTemplate.tape r.circuits.length ∧ H ⟨13, by omega⟩ = 0 ∧
      A ⟨14, by omega⟩ = UnaryTemplate.tape (r.circuits.length * ((symmetricFourfoldOccurrences r).length + 1)) ∧
        H ⟨14, by omega⟩ = 0 ∧
      A ⟨15, by omega⟩ = symBitsWord r L target k ∧
        H ⟨15, by omega⟩ = r.circuits.length * ((symmetricFourfoldOccurrences r).length + 1)

/-! ## Slot maps -/

section Slots
variable (e : ℕ)

def metaSlotVal (i : ℕ) : ℕ := if i ≤ 8 then i else if i ≤ 15 then i + 2 else i + 101
def metaSlot (i : Fin (16 + e)) : Fin (117 + e) := ⟨metaSlotVal i.val, by unfold metaSlotVal; split_ifs <;> omega⟩

def kbSlotVal (k : ℕ) : ℕ := if k < 3 then 11 + k else 15 + k
def kbSlot (k : Fin 97) : Fin (117 + e) := ⟨kbSlotVal k.val, by unfold kbSlotVal; split_ifs <;> omega⟩

def engSlotVal (j : ℕ) : ℕ :=
  if j < 34 then (if j = 32 then 62 else 66 + j)
  else if j = 34 then 9 else if j = 35 then 16 else if j = 36 then 112 else if j = 37 then 17
  else if j = 38 then 14 else if j = 39 then 113 else if j = 40 then 114 else 15
def engSlot (j : Fin 42) : Fin (117 + e) := ⟨engSlotVal j.val, by unfold engSlotVal; split_ifs <;> omega⟩

def stoSlotVal (j : ℕ) : ℕ :=
  if j = 0 then 97 else if j = 1 then 10 else if j = 2 then 113 else if j = 3 then 114
  else if j = 4 then 14 else if j = 5 then 115 else 116
def stoSlot (j : Fin 7) : Fin (117 + e) := ⟨stoSlotVal j.val, by unfold stoSlotVal; split_ifs <;> omega⟩

theorem metaSlot_injective : Function.Injective (metaSlot e) := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [metaSlot, metaSlotVal] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem kbSlot_injective : Function.Injective (kbSlot e) := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [kbSlot, kbSlotVal] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem engSlotVal_inj : ∀ i, i < 42 → ∀ j, j < 42 → engSlotVal i = engSlotVal j → i = j := by
  decide

theorem engSlot_injective : Function.Injective (engSlot e) := by
  intro i j h
  exact Fin.ext (engSlotVal_inj i.val i.isLt j.val j.isLt (congrArg Fin.val h))

theorem stoSlotVal_inj : ∀ i, i < 7 → ∀ j, j < 7 → stoSlotVal i = stoSlotVal j → i = j := by
  decide

theorem stoSlot_injective : Function.Injective (stoSlot e) := by
  intro i j h
  exact Fin.ext (stoSlotVal_inj i.val i.isLt j.val j.isLt (congrArg Fin.val h))

/-- The local tape of arena tape `j`. -/
theorem arena_local (j : Fin 34) :
    kbSlot e (KitBoot.outSlot j) = ⟨if j.val = 32 then 62 else 66 + j.val, by split_ifs <;> omega⟩ := by
  apply Fin.ext
  simp only [kbSlot, kbSlotVal, KitBoot.outSlot]
  rw [KitBoot.arenaSlots_val]
  simp only [Fin.val_castAdd]
  split_ifs <;> omega

end Slots

end
end NearCubicWires.PacketsCombine
