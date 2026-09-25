import Proof.Packets.PacketsCoordHoles

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
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction
noncomputable section

/-- `Fin.addCases` by value. -/
theorem addCases_val {α : Type} {m n : ℕ} (f : Fin m → α) (g : Fin n → α) (i : Fin (m + n)) :
    Fin.addCases (motive := fun _ => α) f g i =
      if h : i.val < m then f ⟨i.val, h⟩ else g ⟨i.val - m, by omega⟩ := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.addCases_left]
    have hj : (Fin.castAdd n j : Fin (m + n)).val = j.val := rfl
    rw [dif_pos (by rw [hj]; exact j.isLt)]
    rfl
  · rw [Fin.addCases_right]
    have hj : (Fin.natAdd m j : Fin (m + n)).val = m + j.val := rfl
    rw [dif_neg (by rw [hj]; omega)]
    congr 1
    apply Fin.ext
    simp only [hj]
    omega

/-- The external entry bank by tape value: ten words, every other tape empty. -/
def allTable (C w root pop B n : ℕ) (mask x y code : List Bool) (v : ℕ) : List Bool :=
  if v = 0 then List.replicate B true else if v = 11 then List.replicate pop true
  else if v = 40 then List.replicate C true else if v = 42 then List.replicate root true
  else if v = 46 then mask else if v = 102 then code else if v = 427 then CompareMachine.word n
  else if v = 428 then x else if v = 429 then y else if v = 433 then List.replicate w true else []

theorem input_other (C w root pop B n : ℕ) (mask x y code : List Bool) (v : ℕ) (hv : v < 742)
    (hs : ¬ (v = 0 ∨ v = 11 ∨ v = 40 ∨ v = 42 ∨ v = 46 ∨ v = 102 ∨ v = 427 ∨ v = 428 ∨ v = 429 ∨ v = 433)) :
    Theorem25Completion.WalkLiteralProducedMajority.input C w root pop B n mask x y code ⟨v, hv⟩ = [] := by
  simp only [not_or] at hs
  obtain ⟨g0, g11, g40, g42, g46, g102, g427, g428, g429, g433⟩ := hs
  unfold Theorem25Completion.WalkLiteralProducedMajority.input
  rw [addCases_val]
  split_ifs with h566
  · unfold Theorem25Completion.WalkLiteralProducedReserve.input
    rw [addCases_val]
    split_ifs with h433
    · unfold Theorem25Completion.WalkLiteralProduced.input Theorem25Completion.WalkLiteralProduced.bank0
      rw [addCases_val]
      split_ifs with h95
      · unfold Theorem25Completion.WalkLiteralMasters.gradedInput
        rw [addCases_val]
        split_ifs with h40
        · unfold Completion.SourceGradedRank.input
          dsimp only at *
          split_ifs <;> first | rfl | (exfalso; simp only [Fin.ext_iff] at *; simp at *; omega)
        · unfold Theorem25Completion.WalkLiteralMasters.gradedExtra
          dsimp only at *
          split_ifs <;> first | rfl | (exfalso; simp only [Fin.ext_iff] at *; simp at *; omega)
      · unfold Theorem25Completion.WalkLiteralProduced.extras
        dsimp only at *
        split_ifs <;> first | rfl | (exfalso; simp only [Fin.ext_iff] at *; simp at *; omega)
    · unfold Theorem25Completion.WalkLiteralProducedReserve.tailInput
      dsimp only at *
      split_ifs <;> first | rfl | (exfalso; simp only [Fin.ext_iff] at *; simp at *; omega)
  · rfl

theorem input_table (C w root pop B n : ℕ) (mask x y code : List Bool) (i : Fin 742) :
    Theorem25Completion.WalkLiteralProducedMajority.input C w root pop B n mask x y code i =
      allTable C w root pop B n mask x y code i.val := by
  rcases i with ⟨v, hv⟩
  by_cases hs : v = 0 ∨ v = 11 ∨ v = 40 ∨ v = 42 ∨ v = 46 ∨ v = 102 ∨ v = 427 ∨ v = 428 ∨ v = 429 ∨ v = 433
  · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · rw [input_other C w root pop B n mask x y code v hv hs]
    have hs' := hs
    simp only [not_or] at hs'
    obtain ⟨h0, h11, h40, h42, h46, h102, h427, h428, h429, h433⟩ := hs'
    simp only [allTable, h0, h11, h40, h42, h46, h102, h427, h428, h429, h433, if_false]

/-! ## The per-request words -/

section Words
variable (a : DecompositionAlgorithm)

/-- The touching bound `B` (all_run tape 0). -/
def Bof (r : Request) : ℕ := LiveRows.bound (r.family a).occurrences (Packets.live (r.family a))
/-- The population (tape 11). -/
def popOf (r : Request) : ℕ := (r.family a).occurrences.length

def rootOf (r : Request) : ℕ := ConeWindow.root (Bof a r)
/-- The walk counter `t - 1` (tape 427, as `CompareMachine.word`). -/
def nOf (r : Request) : ℕ := 2 * Nat.clog 2 (r.denominator a + 1)

/-- The prepared entry of mask `j` of key `k`. -/
def cellIn (K : KitShape a) (r : Request) (k : rcKey a r) (j : ℕ) (i : Fin 742) : List Bool :=
  allTable (K.C r) (K.w r) (rootOf a r) (popOf a r) (Bof a r) (nOf a r) ((maskBitsList a r k).getD j [])
    (startXOf a r k) (startYOf a r k) (labelsOf a r k) i.val

end Words

theorem getD_map_lt {α β : Type} (l : List α) (f : α → β) (j : ℕ) (d : β) (hj : j < l.length) :
    (l.map f).getD j d = f (l[j]'hj) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
  rfl

section PerKind
variable (a : DecompositionAlgorithm) (K : KitShape a)

theorem cellIn_sym (r0 : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r0.circuits.length ≤ 4)
    (L target : ℕ) (k : RCFive.RowKeys.SymKey r0 L target) (j : ℕ)
    (hj' : j < (PacketsConstruction.symMasks r0).length) :
    cellIn a K (.sym r0 four L target) k j = ConeRun.input (symmetricFourfoldOccurrences r0)
      (CyclicChoice.live (symmetricFourfoldOccurrences r0) L) (symmetricListDenominator r0 target)
      (K.C (.sym r0 four L target)) (K.w (.sym r0 four L target)) ((PacketsConstruction.symMasks r0)[j]'hj')
      k.seed := by
  have hmask : (maskBitsList a (.sym r0 four L target) k).getD j [] =
      MaskCoord.maskBits (symmetricFourfoldOccurrences r0) ((PacketsConstruction.symMasks r0)[j]'hj') :=
    getD_map_lt _ _ _ _ hj'
  funext i
  unfold cellIn ConeRun.input
  rw [input_table, hmask]
  rfl

theorem cellIn_thr (r0 : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r0.circuits.length ≤ 4)
    (L target : ℕ) (k : RCFive.RowKeys.ThrKey a r0 L target) (j : ℕ)
    (hj' : j < (PacketsConstruction.thrMasks a r0 L target k).length) :
    cellIn a K (.thr r0 four L target) k j = ConeRun.input (thresholdFourfoldOccurrences r0)
      (CyclicChoice.live (thresholdFourfoldOccurrences r0) L)
      (CloseoutFinalC10ThresholdRows.listDenominator a r0 target)
      (K.C (.thr r0 four L target)) (K.w (.thr r0 four L target))
      ((PacketsConstruction.thrMasks a r0 L target k)[j]'hj') k.seed := by
  have hmask : (maskBitsList a (.thr r0 four L target) k).getD j [] =
      MaskCoord.maskBits (thresholdFourfoldOccurrences r0) ((PacketsConstruction.thrMasks a r0 L target k)[j]'hj') :=
    getD_map_lt _ _ _ _ hj'
  funext i
  unfold cellIn ConeRun.input
  rw [input_table, hmask]
  rfl

theorem budgetOf_sym (r0 : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r0.circuits.length ≤ 4)
    (L target : ℕ) (k : RCFive.RowKeys.SymKey r0 L target) (j : ℕ)
    (hj' : j < (PacketsConstruction.symMasks r0).length) :
    ConeRun.budgetOf a K (.sym r0 four L target) k j = ConeRun.budget (symmetricFourfoldOccurrences r0)
      (CyclicChoice.live (symmetricFourfoldOccurrences r0) L) (symmetricListDenominator r0 target)
      (K.C (.sym r0 four L target)) (K.w (.sym r0 four L target)) ((PacketsConstruction.symMasks r0)[j]'hj') := by
  show ConeRun.budget _ _ _ _ _ ((PacketsConstruction.symMasks r0).getD j ∅) = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some]

theorem budgetOf_thr (r0 : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r0.circuits.length ≤ 4)
    (L target : ℕ) (k : RCFive.RowKeys.ThrKey a r0 L target) (j : ℕ)
    (hj' : j < (PacketsConstruction.thrMasks a r0 L target k).length) :
    ConeRun.budgetOf a K (.thr r0 four L target) k j = ConeRun.budget (thresholdFourfoldOccurrences r0)
      (CyclicChoice.live (thresholdFourfoldOccurrences r0) L)
      (CloseoutFinalC10ThresholdRows.listDenominator a r0 target)
      (K.C (.thr r0 four L target)) (K.w (.thr r0 four L target))
      ((PacketsConstruction.thrMasks a r0 L target k)[j]'hj') := by
  show ConeRun.budget _ _ _ _ _ ((PacketsConstruction.thrMasks a r0 L target k).getD j ∅) = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some]

theorem all_run_sym (hA : ConeBounds.RouteA a K) (r0 : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (four : r0.circuits.length ≤ 4) (L target : ℕ) (k : RCFive.RowKeys.SymKey r0 L target)
    (hk : k ∈ rcKeys a (.sym r0 four L target)) (hkey : ConeBounds.Keyed a (.sym r0 four L target)) (j : ℕ)
    (hj' : j < (PacketsConstruction.symMasks r0).length) :
    ∃ (H : Fin 742 → ℕ) (A : Fin 742 → List Bool),
      Step Theorem25Completion.WalkLiteralProducedMajority.machine (ConeRun.budgetOf a K (.sym r0 four L target) k j)
        (fun _ => 0) (cellIn a K (.sym r0 four L target) k j) H A ∧
      A 704 = PolyKit.vector (K.C (.sym r0 four L target)) (K.w (.sym r0 four L target))
        ((MaskCoord.maskCoordsList a (.sym r0 four L target) k).getD j []) := by
  obtain ⟨H, A, hs, ho⟩ := ConeRun.request_run_sym a K hA r0 four L target k hk hkey j hj'
  refine ⟨H, A, (hs.congr_in rfl (cellIn_sym a K r0 four L target k j hj').symm).enlarge
    (Nat.le_of_eq (budgetOf_sym a K r0 four L target k j hj').symm), ho.trans ?_⟩
  exact congrArg (PolyKit.vector (K.C (.sym r0 four L target)) (K.w (.sym r0 four L target)))
    (getD_map_lt (PacketsConstruction.symMasks r0) (fun M => MaskCoord.maskCoords (symmetricFourfoldOccurrences r0)
      (CyclicChoice.live (symmetricFourfoldOccurrences r0) L) (symmetricListDenominator r0 target) M k.seed) j [] hj').symm

theorem all_run_thr (hA : ConeBounds.RouteA a K) (r0 : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r0.circuits.length ≤ 4) (L target : ℕ) (k : RCFive.RowKeys.ThrKey a r0 L target)
    (hk : k ∈ rcKeys a (.thr r0 four L target)) (hkey : ConeBounds.Keyed a (.thr r0 four L target)) (j : ℕ)
    (hj' : j < (PacketsConstruction.thrMasks a r0 L target k).length) :
    ∃ (H : Fin 742 → ℕ) (A : Fin 742 → List Bool),
      Step Theorem25Completion.WalkLiteralProducedMajority.machine (ConeRun.budgetOf a K (.thr r0 four L target) k j)
        (fun _ => 0) (cellIn a K (.thr r0 four L target) k j) H A ∧
      A 704 = PolyKit.vector (K.C (.thr r0 four L target)) (K.w (.thr r0 four L target))
        ((MaskCoord.maskCoordsList a (.thr r0 four L target) k).getD j []) := by
  obtain ⟨H, A, hs, ho⟩ := ConeRun.request_run_thr a K hA r0 four L target k hk hkey j hj'
  refine ⟨H, A, (hs.congr_in rfl (cellIn_thr a K r0 four L target k j hj').symm).enlarge
    (Nat.le_of_eq (budgetOf_thr a K r0 four L target k j hj').symm), ho.trans ?_⟩
  exact congrArg (PolyKit.vector (K.C (.thr r0 four L target)) (K.w (.thr r0 four L target)))
    (getD_map_lt (PacketsConstruction.thrMasks a r0 L target k) (fun M => MaskCoord.maskCoords (thresholdFourfoldOccurrences r0)
      (CyclicChoice.live (thresholdFourfoldOccurrences r0) L) (CloseoutFinalC10ThresholdRows.listDenominator a r0 target) M k.seed) j [] hj').symm

end PerKind

/-- **Route A at every key and mask** (keyed: `B ≥ 1`). -/
theorem all_run_req (a : DecompositionAlgorithm) (K : KitShape a) (hA : ConeBounds.RouteA a K) (r : Request)
    (k : rcKey a r) (hk : k ∈ rcKeys a r) (hB : 1 ≤ Bof a r) (j : ℕ) (hj : j < maskCount a r k) :
    ∃ (H : Fin 742 → ℕ) (A : Fin 742 → List Bool),
      Step Theorem25Completion.WalkLiteralProducedMajority.machine (ConeRun.budgetOf a K r k j) (fun _ => 0)
        (cellIn a K r k j) H A ∧
      A 704 = PolyKit.vector (K.C r) (K.w r) ((MaskCoord.maskCoordsList a r k).getD j []) := by
  have hkey := ConeDegenerate.keyed_of_bound_pos a r hB
  cases r with
  | terminal => exact PEmpty.elim k
  | sym r0 four L target =>
    have e : maskCount a (.sym r0 four L target) k = (PacketsConstruction.symMasks r0).length := List.length_map _
    exact all_run_sym a K hA r0 four L target k hk hkey j (e ▸ hj)
  | thr r0 four L target =>
    have e : maskCount a (.thr r0 four L target) k = (PacketsConstruction.thrMasks a r0 L target k).length :=
      List.length_map _
    exact all_run_thr a K hA r0 four L target k hk hkey j (e ▸ hj)

end
end NearCubicWires.PacketsConstruction.Residual
