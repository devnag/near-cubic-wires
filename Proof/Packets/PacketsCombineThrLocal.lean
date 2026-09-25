import Proof.Packets.PacketsCombineSymStage

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

/-! ## The THR table of a key -/

/-- The digit count of a THR key. -/
def thrD {a : DecompositionAlgorithm} {r : FourfoldRequest NormalizedThresholdThresholdCircuit} {L target : ℕ}
    (k : RCFive.RowKeys.ThrKey a r L target) : ℕ := modulusDigitCount k.prime.val

/-- The selection table of a THR key: per code (ascending), the one-hot selection bits of its digit
tuple, then `modularTupleAccepts prime residue 2`. -/
def thrTableOf {a : DecompositionAlgorithm} (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (L target : ℕ)
    (k : RCFive.RowKeys.ThrKey a r L target) : List Bool :=
  thrTable (thrD k) ((thresholdFourfoldOccurrences r).length + 1)
    (((thresholdFourfoldOccurrences r).length + 1) ^ thrD k) tupleOf
    (fun c => SupplierRadix.modularTupleAccepts k.prime.val k.residue.val 2 (tupleOf c))

/-- **The THR metadata contract** (hypothesis of the assembly; one fixed machine). From the framed
input and the key fields it keeps tapes `0..8` and writes, heads `0` except the table: templates of `C`,
`C`, `w`, `K = digits*(pop+1)` (twice), `N = (pop+1)^digits`, and the table `thrTableOf` with head at
`N*(K+1)` (the engine's starting cursor). Private tapes `16..` existential. -/
structure ThrMeta (a : DecompositionAlgorithm) (K : KitShape a) where
  extra : ℕ
  states : ℕ
  machine : Machine (16 + extra) states
  cost : Request → ℕ
  coefficient : ℕ
  degree : ℕ
  cost_le : ∀ r, cost r ≤ coefficient * (r.smallSize a) ^ degree
  run : ∀ (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : ℕ) (k : RCFive.RowKeys.ThrKey a r L target), k ∈ RCFive.RowKeys.thrKeys a r L target →
    ∃ (H : Fin (16 + extra) → ℕ) (A : Fin (16 + extra) → List Bool),
      Step machine (cost (.thr r four L target)) (fun _ => 0)
        (metaEntry a (.thr r four L target) (some k) (16 + extra)) H A ∧
      (∀ i : Fin (16 + extra), i.val ≤ 8 →
        A i = metaEntry a (.thr r four L target) (some k) (16 + extra) i ∧ H i = 0) ∧
      A ⟨9, by omega⟩ = UnaryTemplate.tape (K.C (.thr r four L target)) ∧ H ⟨9, by omega⟩ = 0 ∧
      A ⟨10, by omega⟩ = UnaryTemplate.tape (K.C (.thr r four L target)) ∧ H ⟨10, by omega⟩ = 0 ∧
      A ⟨11, by omega⟩ = UnaryTemplate.tape (K.w (.thr r four L target)) ∧ H ⟨11, by omega⟩ = 0 ∧
      A ⟨12, by omega⟩ = UnaryTemplate.tape (thrD k * ((thresholdFourfoldOccurrences r).length + 1)) ∧
        H ⟨12, by omega⟩ = 0 ∧
      A ⟨13, by omega⟩ = UnaryTemplate.tape (thrD k * ((thresholdFourfoldOccurrences r).length + 1)) ∧
        H ⟨13, by omega⟩ = 0 ∧
      A ⟨14, by omega⟩ = UnaryTemplate.tape (((thresholdFourfoldOccurrences r).length + 1) ^ thrD k) ∧
        H ⟨14, by omega⟩ = 0 ∧
      A ⟨15, by omega⟩ = thrTableOf r L target k ∧
        H ⟨15, by omega⟩ = ((thresholdFourfoldOccurrences r).length + 1) ^ thrD k *
          (thrD k * ((thresholdFourfoldOccurrences r).length + 1) + 1)

/-! ## Slot maps -/

section Slots
variable (e : ℕ)

def tmetaSlotVal (i : ℕ) : ℕ := if i ≤ 8 then i else if i ≤ 15 then i + 2 else i + 102
def tmetaSlot (i : Fin (16 + e)) : Fin (118 + e) := ⟨tmetaSlotVal i.val, by unfold tmetaSlotVal; split_ifs <;> omega⟩

def tkbSlot (k : Fin 97) : Fin (118 + e) := ⟨kbSlotVal k.val, by unfold kbSlotVal; split_ifs <;> omega⟩

def tengSlotVal (j : ℕ) : ℕ :=
  if j < 34 then (if j = 32 then 62 else 66 + j)
  else if j = 34 then 9 else if j = 35 then 113 else if j = 36 then 112 else if j = 37 then 17
  else if j = 38 then 15 else if j = 39 then 114 else if j = 40 then 115 else if j = 41 then 14 else 16
def tengSlot (j : Fin 43) : Fin (118 + e) := ⟨tengSlotVal j.val, by unfold tengSlotVal; split_ifs <;> omega⟩

def tstoSlotVal (j : ℕ) : ℕ :=
  if j = 0 then 97 else if j = 1 then 10 else if j = 2 then 114 else if j = 3 then 115
  else if j = 4 then 15 else if j = 5 then 116 else 117
def tstoSlot (j : Fin 7) : Fin (118 + e) := ⟨tstoSlotVal j.val, by unfold tstoSlotVal; split_ifs <;> omega⟩

theorem tmetaSlot_injective : Function.Injective (tmetaSlot e) := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [tmetaSlot, tmetaSlotVal] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem tkbSlot_injective : Function.Injective (tkbSlot e) := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [tkbSlot, kbSlotVal] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem tengSlotVal_inj : ∀ i, i < 43 → ∀ j, j < 43 → tengSlotVal i = tengSlotVal j → i = j := by
  decide

theorem tengSlot_injective : Function.Injective (tengSlot e) := by
  intro i j h
  exact Fin.ext (tengSlotVal_inj i.val i.isLt j.val j.isLt (congrArg Fin.val h))

theorem tstoSlotVal_inj : ∀ i, i < 7 → ∀ j, j < 7 → tstoSlotVal i = tstoSlotVal j → i = j := by
  decide

theorem tstoSlot_injective : Function.Injective (tstoSlot e) := by
  intro i j h
  exact Fin.ext (tstoSlotVal_inj i.val i.isLt j.val j.isLt (congrArg Fin.val h))

theorem tengSlot_arena (j : Fin 34) :
    tengSlot e ⟨j.val, by omega⟩ = tkbSlot e (KitBoot.outSlot j) := by
  apply Fin.ext
  simp only [tengSlot, tengSlotVal, tkbSlot, kbSlotVal, KitBoot.outSlot, show j.val < 34 from j.isLt, if_true]
  rw [KitBoot.arenaSlots_val]
  simp only [Fin.val_castAdd]
  split_ifs <;> omega

end Slots

/-! ## The THR engine bank and its read-offs -/

def tengA (C R idx K : ℕ) (left acc : Poly) (ps : List Poly) (table : List Bool) (P : Poly) (stored : List Bool)
    (N : ℕ) : Fin 43 → List Bool :=
  Fin.addCases (m := 42) (n := 1) (motive := fun _ => List Bool) (thrA C R idx K left acc ps table P stored)
    (fun _ => CompareMachine.word N)

def tengH (pos : ℕ) : Fin 43 → ℕ :=
  Fin.addCases (m := 42) (n := 1) (motive := fun _ => ℕ) (thrH pos) (fun _ => 1)

theorem tengA_arena (C R idx K : ℕ) (left acc : Poly) (ps : List Poly) (table : List Bool) (P : Poly)
    (stored : List Bool) (N : ℕ) (j : Fin 43) (hj : j.val < 34) :
    tengA C R idx K left acc ps table P stored N j =
      ReusableArithmetic.state C R (left.map (maskNat C)) (acc.map (maskNat C)) ⟨j.val, hj⟩ := by
  unfold tengA thrA bodyA TranscriptColumnLookupFold.A SelectedPairFetch.A OrderedPacketStep.A ArithmeticLookup.A
  rw [addCases_lt (m := 42) (n := 1) _ _ j (by omega)]
  rw [addCases_lt (m := 41) (n := 1) _ _ _ (by show j.val < 41; omega)]
  rw [addCases_lt (m := 39) (n := 2) _ _ _ (by show j.val < 39; omega)]
  rw [addCases_lt (m := 38) (n := 1) _ _ _ (by show j.val < 38; omega)]
  rw [addCases_lt (m := 37) (n := 1) _ _ _ (by show j.val < 37; omega)]
  rw [addCases_lt (m := 34) (n := 3) _ _ _ (by show j.val < 34; omega)]

theorem tengH_arena (pos : ℕ) (j : Fin 43) (hj : j.val < 34) :
    tengH pos j = ReusableArithmetic.heads ⟨j.val, hj⟩ := by
  unfold tengH thrH bodyH TranscriptColumnLookupFold.H SelectedPairFetch.H
  rw [addCases_lt (m := 42) (n := 1) _ _ j (by omega)]
  rw [addCases_lt (m := 41) (n := 1) _ _ _ (by show j.val < 41; omega)]
  rw [addCases_lt (m := 39) (n := 2) _ _ _ (by show j.val < 39; omega)]
  rw [addCases_lt (m := 38) (n := 1) _ _ _ (by show j.val < 38; omega)]
  rw [addCases_lt (m := 37) (n := 1) _ _ _ (by show j.val < 37; omega)]
  simp only [ArithmeticLookup.H, ReusableArithmetic.heads, Fin.ext_iff]
  split_ifs <;> simp_all

end
end NearCubicWires.PacketsCombine
