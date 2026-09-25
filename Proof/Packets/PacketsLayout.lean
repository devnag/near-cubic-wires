import Proof.Packets.PacketFamilyParent

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
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
noncomputable section

/-! ## Key digits -/

/-- The eight digit fields of a key; `none` (after the last row) is the done flag. -/
def keyDigits (a : DecompositionAlgorithm) : ∀ r : Request, Option (rcKey a r) → Fin 8 → ℕ
  | _, none => fun i => if i.val = 7 then 1 else 0
  | .terminal, some k => PEmpty.elim k
  | .sym r _ _ _, some k => fun i =>
      if h : i.val < r.circuits.length then k.offset ⟨i.val, h⟩
      else if i.val = 5 then (canonicalWalkSampleFinEquiv _ _ k.seed).val else 0
  | .thr r _ _ _, some k => fun i =>
      if h : i.val < r.circuits.length then (k.selection ⟨i.val, h⟩).val
      else if i.val = 4 then (primeIndexFinEquiv _ k.prime).val
      else if i.val = 5 then (canonicalWalkSampleFinEquiv _ _ k.seed).val
      else if i.val = 6 then k.residue.val else 0

/-- A strict bound on every digit of an actual key, from the request's dimensions alone. -/
def digitBound (a : DecompositionAlgorithm) : Request → ℕ
  | .terminal => 2
  | .sym r _ L target =>
      (Packets.seedList (symmetricFourfoldOccurrences r)
        (CyclicChoice.live (symmetricFourfoldOccurrences r) L) (symmetricListDenominator r target)).length +
      (∑ i : Fin r.circuits.length, ((r.circuits.get i).bottomCount + 1)) + 2
  | .thr r _ L target =>
      (Packets.seedList (thresholdFourfoldOccurrences r)
        (CyclicChoice.live (thresholdFourfoldOccurrences r) L)
        (CloseoutFinalC10ThresholdRows.listDenominator a r target)).length +
      (∑ i : Fin r.circuits.length, (ThresholdRows.children a (r.circuits.get i)).length) +
      Fintype.card (PrimeIndex (CloseoutFinalC10ThresholdRows.primeCutoff a r target)) +
      CloseoutFinalC10ThresholdRows.primeCutoff a r target + 2

/-- One field width per request: every digit of an actual key fits. -/
def fieldWidth (a : DecompositionAlgorithm) (r : Request) : ℕ := Nat.log 2 (digitBound a r) + 1

/-- The codes the cursor may hold: actual keys and `done`. -/
def CodeValid (a : DecompositionAlgorithm) (r : Request) (c : Option (rcKey a r)) : Prop :=
  c = none ∨ ∃ k ∈ rcKeys a r, c = some k

theorem two_le_bound (a : DecompositionAlgorithm) (r : Request) : 2 ≤ digitBound a r := by
  cases r <;> simp [digitBound]

theorem keyDigits_none (a : DecompositionAlgorithm) (r : Request) (i : Fin 8) :
    keyDigits a r none i = if i.val = 7 then 1 else 0 := by
  cases r <;> rfl

theorem keyDigits_sym (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) (k : RCFive.RowKeys.SymKey r L target) (i : Fin 8) :
    keyDigits a (.sym r four L target) (some k) i =
      if h : i.val < r.circuits.length then k.offset ⟨i.val, h⟩
      else if i.val = 5 then (canonicalWalkSampleFinEquiv _ _ k.seed).val else 0 := rfl

theorem keyDigits_thr (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) (k : RCFive.RowKeys.ThrKey a r L target) (i : Fin 8) :
    keyDigits a (.thr r four L target) (some k) i =
      if h : i.val < r.circuits.length then (k.selection ⟨i.val, h⟩).val
      else if i.val = 4 then (primeIndexFinEquiv _ k.prime).val
      else if i.val = 5 then (canonicalWalkSampleFinEquiv _ _ k.seed).val
      else if i.val = 6 then k.residue.val else 0 := rfl

theorem sym_digit_lt (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) (k : RCFive.RowKeys.SymKey r L target)
    (hk : k ∈ RCFive.RowKeys.symKeys r L target) (i : Fin 8) :
    keyDigits a (.sym r four L target) (some k) i < digitBound a (.sym r four L target) := by
  rw [keyDigits_sym]
  simp only [digitBound, Packets.seedList, List.length_ofFn]
  split_ifs with h h5
  · obtain ⟨seed, _, hk⟩ := List.mem_flatMap.mp hk
    obtain ⟨offset, ho, rfl⟩ := List.mem_map.mp hk
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp ho
    have hlt : (t ⟨i.val, h⟩).val < (r.circuits.get ⟨i.val, h⟩).bottomCount + 1 := (t ⟨i.val, h⟩).isLt
    have hsum := Finset.single_le_sum (f := fun j : Fin r.circuits.length =>
      (r.circuits.get j).bottomCount + 1) (fun j _ => Nat.zero_le _) (Finset.mem_univ ⟨i.val, h⟩)
    simp only at hsum ⊢
    omega
  · have := (canonicalWalkSampleFinEquiv _ _ k.seed).isLt
    omega
  · omega

theorem thr_digit_lt (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) (k : RCFive.RowKeys.ThrKey a r L target) (i : Fin 8) :
    keyDigits a (.thr r four L target) (some k) i < digitBound a (.thr r four L target) := by
  rw [keyDigits_thr]
  simp only [digitBound, Packets.seedList, List.length_ofFn]
  split_ifs with h h4 h5 h6
  · have hlt := (k.selection ⟨i.val, h⟩).isLt
    have hsum := Finset.single_le_sum (f := fun j : Fin r.circuits.length =>
      (ThresholdRows.children a (r.circuits.get j)).length) (fun j _ => Nat.zero_le _)
      (Finset.mem_univ ⟨i.val, h⟩)
    omega
  · have := (primeIndexFinEquiv _ k.prime).isLt
    omega
  · have := (canonicalWalkSampleFinEquiv _ _ k.seed).isLt
    omega
  · have hres := k.residue.isLt
    have hp := (mem_primesUpTo.mp k.prime.property).2
    omega
  · omega

theorem digit_lt_bound (a : DecompositionAlgorithm) (r : Request) (c : Option (rcKey a r))
    (hc : CodeValid a r c) (i : Fin 8) : keyDigits a r c i < digitBound a r := by
  have h2 := two_le_bound a r
  rcases hc with rfl | ⟨k, hk, rfl⟩
  · rw [keyDigits_none]
    split_ifs <;> omega
  cases r with
  | terminal => exact PEmpty.elim k
  | sym r four L target => exact sym_digit_lt a r four L target k hk i
  | thr r four L target => exact thr_digit_lt a r four L target k i

theorem digit_lt_pow (a : DecompositionAlgorithm) (r : Request) (c : Option (rcKey a r))
    (hc : CodeValid a r c) (i : Fin 8) : keyDigits a r c i < 2 ^ fieldWidth a r :=
  (digit_lt_bound a r c hc i).trans (Nat.lt_pow_succ_log_self (by norm_num) _)

/-! ## The layout -/

/-- The fixed row bank, given the writer's private scratch count `w` and scrub width `R`. -/
def digitLayout (a : DecompositionAlgorithm) (w : ℕ) (R : Request → ℕ) (cR dR : ℕ)
    (hR : ∀ r, R r ≤ cR * (r.smallSize a)^dR) : Layout a (rcFiveKeys a) where
  tapes := 10 + w
  output := ⟨1, by omega⟩
  outputFresh := by simp
  scratch := fun i => decide (10 ≤ i.val)
  scratchOutput := by simp
  cursorPort := fun i => decide (2 ≤ i.val ∧ i.val < 10)
  resident := fun r i => if i.val = 0 then RepairOrdinary.frame (Request.input a r) else []
  cursor := fun r c i =>
    if h : 2 ≤ i.val ∧ i.val < 10 then
      RepairOrdinary.frame (binary (fieldWidth a r) (keyDigits a r c ⟨i.val - 2, by omega⟩))
    else []
  inputResident := by
    intro r i hi
    refine ⟨by simp [hi], by simp [hi], by simp [hi]⟩
  width := R
  widthCoefficient := cR
  widthDegree := dR
  width_le := hR

end
end NearCubicWires.PacketsConstruction
