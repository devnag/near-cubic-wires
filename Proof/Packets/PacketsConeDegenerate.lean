import Proof.Packets.PacketsConeBounds

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.ConeDegenerate
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces NearCubicWires.SupplierWalk
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.SupplierListSchedule
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore PCJ9eff70d512234a4c_Fixed.Materializer
noncomputable section

/-! ## The two constant polynomials and their algebra -/

/-- `cst true = 1 = [[]]`, `cst false = 0 = []`. -/
def cst (b : Bool) : StructuralGF2Polynomial := if b then [[]] else []

theorem add_cst (a b : Bool) : Normalized.structuralGF2Add (cst a) (cst b) = cst (a != b) := by
  cases a <;> cases b <;> rfl

theorem mul_cst (a b : Bool) : Normalized.structuralGF2Mul (cst a) (cst b) = cst (a && b) := by
  cases a <;> cases b <;> rfl

theorem not_cst (b : Bool) : Normalized.structuralGF2Not (cst b) = cst (!b) := by
  cases b <;> rfl

theorem substitute_cst (atom : ℕ → StructuralGF2Polynomial) (b : Bool) :
    Normalized.structuralGF2Substitute atom (cst b) = cst b := by
  cases b <;> rfl

theorem ite_cst (c b : Bool) : (if c then cst b else structuralGF2Zero) = cst (c && b) := by
  cases c <;> cases b <;> rfl

theorem product_cst : ∀ {t : ℕ} (g : Fin t → Bool),
    Normalized.structuralGF2Product (List.ofFn (fun i => cst (g i))) = cst (decide (∀ i, g i = true))
  | 0, g => by
    simp only [List.ofFn_zero]
    have : decide (∀ i : Fin 0, g i = true) = true := by simp
    rw [this]
    rfl
  | t + 1, g => by
    rw [List.ofFn_succ]
    change Normalized.structuralGF2Mul (cst (g 0)) (Normalized.structuralGF2Product
      (List.ofFn (fun i : Fin t => cst (g i.succ)))) = _
    rw [product_cst (fun i : Fin t => g i.succ), mul_cst]
    congr 1
    by_cases h0 : g 0 = true
    · simp [h0, Fin.forall_fin_succ]
    · simp [h0, Fin.forall_fin_succ]

theorem boolParity_fin_succ {t : ℕ} (value : Fin (t + 1) → Bool) :
    SupplierRadix.boolParity value =
      (value 0 != SupplierRadix.boolParity (fun i : Fin t => value i.succ)) := by
  unfold SupplierRadix.boolParity
  rw [Fin.sum_univ_succ]
  cases value 0 <;> simp [Nat.odd_add, ← Nat.not_odd_iff_even]

theorem finParity_cst : ∀ {t : ℕ} (g : Fin t → Bool),
    Normalized.structuralGF2FinParity (fun i => cst (g i)) = cst (SupplierRadix.boolParity g)
  | 0, g => by
    have : SupplierRadix.boolParity g = false := by
      unfold SupplierRadix.boolParity
      simp
    rw [this]
    rfl
  | t + 1, g => by
    change Normalized.structuralGF2Add (cst (g 0))
      (Normalized.structuralGF2FinParity (fun i : Fin t => cst (g i.succ))) = _
    rw [finParity_cst (fun i : Fin t => g i.succ), add_cst, boolParity_fin_succ]

theorem selector_cst {t : ℕ} (b : Bool) (target : BitInput t) :
    Normalized.structuralGF2BooleanSelector (fun _ : Fin t => cst b) target =
      cst (decide (∀ i, target i = b)) := by
  unfold Normalized.structuralGF2BooleanSelector
  have h : (fun i : Fin t => if target i then cst b else Normalized.structuralGF2Not (cst b)) =
      fun i => cst (target i == b) := by
    funext i
    rw [not_cst]
    cases target i <;> cases b <;> rfl
  rw [h, product_cst]
  congr 1
  apply decide_eq_decide.mpr
  constructor
  · intro hi i
    have := hi i
    revert this
    cases target i <;> cases b <;> simp
  · intro hi i
    rw [hi i]
    cases b <;> rfl

theorem assignment_injective (t : ℕ) : Function.Injective (structuralTruthAssignment t) := by
  intro left right hequal
  apply Fin.ext
  have hencoded := congrArg encodeBitInput hequal
  unfold structuralTruthAssignment at hencoded
  rw [encodeBitInput_testBit left.isLt, encodeBitInput_testBit right.isLt] at hencoded
  exact hencoded

theorem truthTable_cst {t : ℕ} (b : Bool) (f : BitInput t → Bool) :
    Normalized.structuralGF2TruthTable (fun _ : Fin t => cst b) f = cst (f (fun _ => b)) := by
  unfold Normalized.structuralGF2TruthTable
  let c0 : Fin (2 ^ t) := ⟨encodeBitInput (fun _ : Fin t => b), by
    rw [encodeBitInput_eq_ofBits]
    exact Nat.ofBits_lt_two_pow _⟩
  have hc0 : structuralTruthAssignment t c0 = fun _ => b := structuralTruthAssignment_encode _
  have h : (fun code : Fin (2 ^ t) => if f (structuralTruthAssignment t code) then
        Normalized.structuralGF2BooleanSelector (fun _ : Fin t => cst b) (structuralTruthAssignment t code)
      else structuralGF2Zero) =
      fun code => cst (decide (code = c0) && f (structuralTruthAssignment t code)) := by
    funext code
    rw [selector_cst, ite_cst]
    congr 1
    have hd : decide (∀ i, structuralTruthAssignment t code i = b) = decide (code = c0) := by
      apply decide_eq_decide.mpr
      constructor
      · intro hi
        apply assignment_injective t
        rw [hc0]
        funext i
        exact hi i
      · intro hi i
        rw [hi, hc0]
    rw [hd, Bool.and_comm]
  rw [h, finParity_cst, SupplierRadix.boolParity_exactSelector, hc0]

theorem majority_const {t : ℕ} (ht : 1 ≤ t) (b : Bool) : compiledBitMajority (fun _ : Fin t => b) = b := by
  unfold compiledBitMajority majorityThreshold
  cases b
  · simp
    omega
  · simp
    omega

theorem bitMajority_cst {t : ℕ} (ht : 1 ≤ t) (b : Bool) :
    Normalized.structuralGF2BitMajority (fun _ : Fin t => cst b) = cst b := by
  unfold Normalized.structuralGF2BitMajority
  rw [truthTable_cst, majority_const ht]

/-! ## The terminal vector at depth zero -/

theorem shifted_zero (codes : List ℕ) :
    Normalized.structuralGF2ShiftedElementarySymmetric codes 0 0 = [[]] := by
  unfold Normalized.structuralGF2ShiftedElementarySymmetric
  simp only [List.Nat.antidiagonal_zero, List.map_cons, List.map_nil, Ring.choose_zero_right, Int.cast_one]
  unfold Normalized.structuralGF2ElementarySymmetric
  simp only [List.sublistsLen_zero]
  rfl

theorem triangular_zero (target : ℕ) :
    SupplierWindow.triangularCoefficient (SupplierWindow.windowDelta target) 0 =
      if 0 = target then 1 else 0 := by
  rw [SupplierWindow.triangularCoefficient]
  simp [SupplierWindow.windowDelta]

theorem terminal_zero (depth population target : ℕ) :
    Normalized.structuralTerminalWindowPolynomial depth population 0 target = cst (decide (target = 0)) := by
  unfold Normalized.structuralTerminalWindowPolynomial Normalized.structuralGF2ConsecutiveWindowIndicator
  simp only [Nat.zero_add, List.range_one, List.map_cons, List.map_nil]
  rw [shifted_zero, triangular_zero]
  by_cases h : target = 0
  · subst h
    rfl
  · have h' : ¬ (0 = target) := fun e => h e.symm
    simp only [h', if_false, h, decide_false]
    rfl

/-- **The coordinate vector with no touching occurrence.** Depth `0`: every coordinate is the terminal constant. -/
theorem coordinate_of_depth_zero {rank depth population t : ℕ} (hd : depth = 0) (ht : 1 ≤ t)
    (mask : Finset (Fin population)) (label : Fin population → BinaryVector rank) (window : Fin depth → ℕ)
    (sample : MargulisWalkSample (2 ^ toeplitzWalkSideBits rank) t) (cand : Fin (population + 1)) :
    Normalized.structuralMaskedWalkListCoordinate mask label window 0 sample cand =
      cst (decide (cand.val = 0)) := by
  unfold Normalized.structuralMaskedWalkListCoordinate
  have hstep : ∀ seed : ToeplitzSeed rank,
      Normalized.structuralMaskedListCoordinate mask label seed window 0 cand = cst (decide (cand.val = 0)) := by
    intro seed
    unfold Normalized.structuralMaskedListCoordinate Normalized.structuralListPolynomialVector
    rw [Normalized.structuralListPolynomialVectorFrom, dif_neg (by omega)]
    unfold Normalized.structuralTerminalPolynomialVector
    rw [terminal_zero, substitute_cst]
  have hfun : (fun time : Fin t => Normalized.structuralMaskedListCoordinate mask label
      (toeplitzWalkEncoding rank (sample.vertex time)).1 window 0 cand) = fun _ => cst (decide (cand.val = 0)) := by
    funext time
    exact hstep _
  rw [hfun, bitMajority_cst ht]

/-- The terminal vector over `pop + 1` candidates. -/
def terminalVec (pop : ℕ) : List StructuralGF2Polynomial :=
  List.ofFn (fun cand : Fin (pop + 1) => cst (decide (cand.val = 0)))

/-- **Every mask's coordinate vector of a touching-free family is the terminal vector.** -/
theorem coords_of_bound_zero {q : ℕ} (occ : List (SupportedNormalizedGate q)) (I : Finset (Fin q)) (den : ℕ)
    (hB : LiveRows.bound occ I = 0) (M : Finset (Fin occ.length)) (sample : LiveRows.Seed occ I den) :
    MaskCoord.maskCoords occ I den M sample = terminalVec occ.length := by
  rw [MaskCoord.coords_eq]
  unfold terminalVec
  congr 1
  funext cand
  have hd : canonicalGradedDepth (LiveRows.bound occ I) = 0 := by
    rw [hB]
    rfl
  exact coordinate_of_depth_zero hd (walk_pos den) _ _ _ _ _

/-! ## The branch condition -/

variable (a : DecompositionAlgorithm)

/-- A positive touching bound gives a positive rank (route A applies). -/
theorem keyed_of_bound_pos (r : Request)
    (hB : 1 ≤ LiveRows.bound (r.family a).occurrences (Packets.live (r.family a))) : ConeBounds.Keyed a r := by
  unfold ConeBounds.Keyed
  have hle := bound_le_pop (r.family a).occurrences (Packets.live (r.family a))
  rcases Nat.eq_zero_or_pos (canonicalGradedRank (r.family a).occurrences.length
      (LiveRows.bound (r.family a).occurrences (Packets.live (r.family a)))) with h | h
  · have := (ConeBounds.rank_eq_zero_iff _ _ hle).1 h
    omega
  · exact h

/-- Every mask of a key of a touching-free request: the terminal vector. -/
theorem maskCoords_of_bound_zero (r : Request) (k : rcKey a r)
    (hB : LiveRows.bound (r.family a).occurrences (Packets.live (r.family a)) = 0)
    (j : ℕ) (hj : j < (MaskCoord.maskCoordsList a r k).length) :
    (MaskCoord.maskCoordsList a r k)[j] = terminalVec (r.family a).occurrences.length := by
  cases r with
  | terminal => exact PEmpty.elim k
  | sym r0 four L target =>
    simp only [MaskCoord.maskCoordsList, List.getElem_map]
    exact coords_of_bound_zero _ _ _ hB _ _
  | thr r0 four L target =>
    simp only [MaskCoord.maskCoordsList, List.getElem_map]
    exact coords_of_bound_zero _ _ _ hB _ _

/-! ## The terminal vector in the kit codec -/

theorem pad_replicate_false (R C : ℕ) (hC : C ≤ R) :
    ZeroPadding.pad R (List.replicate C false) = List.replicate R false := by
  unfold ZeroPadding.pad
  rw [List.length_replicate, ← List.replicate_add]
  congr 1
  omega

theorem entry_one (C R : ℕ) (hC : C ≤ R) :
    PacketVector.entry R (PolyKit.masks C (cst true)) =
      List.replicate (R + 1) false ++ true :: List.replicate (R - 2) false := by
  have hm : NormalizedFiniteTransport.maskNat C [] = List.replicate C false := by
    unfold NormalizedFiniteTransport.maskNat
    simp [List.ofFn_const]
  have hP : PolyKit.masks C (cst true) = [List.replicate C false] := by
    unfold PolyKit.masks cst
    simp only [if_true, List.map_cons, List.map_nil]
    rw [hm]
  have h2 : ZeroPadding.pad R (RepairSource.VerifierDecoding.CompareMachine.word 1) =
      false :: true :: List.replicate (R - 2) false := by
    unfold ZeroPadding.pad RepairSource.VerifierDecoding.CompareMachine.word
    simp
  rw [hP]
  unfold PacketVector.entry PacketVector.payload PacketVector.count
  rw [List.flatten_singleton, List.length_singleton, pad_replicate_false R C hC, h2, List.replicate_succ',
    List.append_assoc]
  rfl

theorem entry_zero (C R : ℕ) (hR : 1 ≤ R) :
    PacketVector.entry R (PolyKit.masks C (cst false)) = List.replicate (2 * R) false := by
  have hP : PolyKit.masks C (cst false) = [] := rfl
  have h2 : ZeroPadding.pad R (RepairSource.VerifierDecoding.CompareMachine.word 0) =
      false :: List.replicate (R - 1) false := by
    unfold ZeroPadding.pad RepairSource.VerifierDecoding.CompareMachine.word
    simp
  rw [hP]
  unfold PacketVector.entry PacketVector.payload PacketVector.count
  have hp0 : ZeroPadding.pad R [] = List.replicate R false := by simp [ZeroPadding.pad]
  rw [List.flatten_nil, List.length_nil, h2, ← List.replicate_succ, hp0, ← List.replicate_add]
  congr 1
  omega

theorem zeros_entries (C R : ℕ) (hR : 1 ≤ R) : ∀ n : ℕ,
    ((List.replicate n (cst false)).map (PolyKit.masks C)).flatMap (PacketVector.entry R) =
      List.replicate (n * (2 * R)) false
  | 0 => by simp
  | n + 1 => by
    rw [List.replicate_succ, List.map_cons, List.flatMap_cons, entry_zero C R hR, zeros_entries C R hR n,
      ← List.replicate_add]
    congr 1
    ring

/-- **The terminal vector's word**: one `true`, at cell `R + 1`. -/
theorem vector_terminal (C w pop : ℕ) (hC : C ≤ PolyKit.reserve C w) (hR : 1 ≤ PolyKit.reserve C w) :
    PolyKit.vector C w (terminalVec pop) =
      List.replicate (PolyKit.reserve C w + 1) false ++
        true :: List.replicate (PolyKit.reserve C w - 2 + pop * (2 * PolyKit.reserve C w)) false := by
  unfold PolyKit.vector terminalVec PacketVector.bank
  rw [List.ofFn_succ, List.map_cons, List.flatMap_cons]
  have h0 : cst (decide ((0 : Fin (pop + 1)).val = 0)) = cst true := rfl
  rw [h0, entry_one C _ hC]
  have hc : (fun i : Fin pop => cst (decide ((Fin.succ i).val = 0))) = fun _ => cst false := by
    funext i
    simp
  rw [hc, List.ofFn_const, zeros_entries C _ hR, List.append_assoc, List.cons_append,
    ← List.replicate_add]

/-! ## A keyed degenerate request exists (so the branch is needed) -/


end
end NearCubicWires.PacketsConstruction.ConeDegenerate
