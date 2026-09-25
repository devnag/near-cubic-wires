import Proof.SourceAssembly.SourceRequestSymParity

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
open RepairSource.ProjectionNormalization SupplierPipeline CompilerSemantics
open NearCubicWires.SourceRequest ExecutableInterfaces NearCubicWires.RepairSource.CloseoutFinal
namespace NearCubicWires.SourceFactorSel.SysCost
noncomputable section

/-! ### Generic pieces -/

theorem pairsCost_le (gs : List CloseoutRowsTupleSeek.GatePair) :
    CloseoutRowsTupleSeek.pairsCost gs ≤ (CloseoutRowsTupleSeek.nativeWord gs).length +
      (CloseoutRowsTupleSeek.supportWord gs).length + 4 * gs.length + 3 := by
  have h : ∀ gs : List CloseoutRowsTupleSeek.GatePair, (gs.map CloseoutRowsTupleSeek.pairCost).sum ≤
      (CloseoutRowsTupleSeek.nativeWord gs).length + (CloseoutRowsTupleSeek.supportWord gs).length + gs.length := by
    intro gs
    induction gs with
    | nil => simp
    | cons g gs ih =>
      simp only [CloseoutRowsTupleSeek.nativeWord, CloseoutRowsTupleSeek.supportWord] at ih ⊢
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append, frame_length',
        List.length_cons, CloseoutRowsTupleSeek.pairCost]
      omega
  have := h gs
  unfold CloseoutRowsTupleSeek.pairsCost
  omega

theorem count_le (q Q : Nat) (bm : List Bool) : Gen.SymmetricHeaderQuery.count q Q bm ≤ q := by
  unfold Gen.SymmetricHeaderQuery.count PCJ6e421fabe2aa4155_SourceSymmetricScan.selected
  exact (List.length_filter_le _ _).trans (by simp)

theorem bitLen_le (n : Nat) : natBitLength n ≤ n + 1 := Nat.add_le_add_right (Nat.log_le_self 2 n) 1

/-- The symmetric header query (shared prefix of both chains). -/
theorem shq_le (q Q : Nat) (bm : List Bool) :
    Gen.SymmetricHeaderQuery.budget q Q bm ≤ 45 * Capacity.value q + 22 * q + 82 := by
  have hc := count_le q Q bm
  have hDP := CloseoutRowsEstimator.DriverPower.budget_linear 2 256 q (by decide) (by decide)
  have hNq := CloseoutRowsEstimatorParity.Natural.budget_fit q q le_rfl
  have hNc := CloseoutRowsEstimatorParity.Natural.budget_fit q _ hc
  have hSC := PCJ6e421fabe2aa4155_SourceSymmetricBound.budget_le q
  have hcap : Capacity.value q = 256 * (q + 1) ^ 2 := rfl
  unfold Gen.SymmetricHeaderQuery.budget Gen.SymmetricQuery.budget Gen.ParityQuery.budget
    PCJ6e421fabe2aa4155_SourceParityPrep.budget PCJ6e421fabe2aa4155_SourceSymmetricHeader.budget
    PCJ6e421fabe2aa4155_SourceSymmetricTopReady.budget PCJ6e421fabe2aa4155_SourceSymmetricTop.budget
  generalize (q + 1) ^ 2 = X at hDP hcap
  omega

/-! ### SYM -/

def symC : Nat := 65536
def symE : Nat := 2

/-- The SYM systematic cost as a function of the bitmap (`SymSystematic.cost S` is this at `bitmap S`). -/
def symBody (q : Nat) (bm : List Bool) : Nat :=
  (2 * Gen.SymPhysical.budget q 0 bm + 4 * (Gen.SymPhysical.native q 0 bm).length + 7) + 1 +
    ((12 * (Gen.SymPhysical.native q 0 bm).length + 13) + 1 +
      (2 * Gen.SymPhysical.budget q 0 bm +
        4 * (CloseoutRowsTupleSeek.supportWord (Gen.SymPhysical.selectedGates q 0 bm)).length + 7))

theorem symCost_eq {q : Nat} (S : Finset (Fin q)) :
    SymSystematic.cost S = symBody q (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap S) := rfl

theorem symGates_len (q : Nat) (bm : List Bool) : (Gen.SymPhysical.selectedGates q 0 bm).length ≤ q := by
  show (PCJ6e421fabe2aa4155_SourceSymmetricPhysical.gates q (Gen.SymmetricQuery.bitmap q 0 bm)).length ≤ q
  rw [PCJ6e421fabe2aa4155_SourceSymmetricPhysical.gates_length]
  exact count_le q 0 bm

theorem symNative_len (q : Nat) (bm : List Bool) :
    (CloseoutRowsTupleSeek.nativeWord (Gen.SymPhysical.selectedGates q 0 bm)).length ≤ Capacity.value q := by
  show (CloseoutRowsTupleSeek.nativeWord
    (PCJ6e421fabe2aa4155_SourceSymmetricPhysical.gates q (Gen.SymmetricQuery.bitmap q 0 bm))).length ≤ _
  rw [PCJ6e421fabe2aa4155_SourceSymmetricPhysical.gates_native]
  exact PCJ6e421fabe2aa4155_SourceSymmetricBound.output_bound q _ 0

theorem symSupport_len (q : Nat) (bm : List Bool) :
    (CloseoutRowsTupleSeek.supportWord (Gen.SymPhysical.selectedGates q 0 bm)).length ≤ Capacity.value q := by
  show (CloseoutRowsTupleSeek.supportWord
    (PCJ6e421fabe2aa4155_SourceSymmetricPhysical.gates q (Gen.SymmetricQuery.bitmap q 0 bm))).length ≤ _
  rw [PCJ6e421fabe2aa4155_SourceSymmetricPhysical.gates_support]
  exact PCJ6e421fabe2aa4155_SourceSymmetricBound.output_bound q _ 1

theorem symTop_len (q : Nat) (bm : List Bool) : (Gen.SymPhysical.top q 0 bm).length ≤ q + 1 := by
  unfold Gen.SymPhysical.top PCJ6e421fabe2aa4155_SourceSymmetricTop.table
  rw [List.length_ofFn]
  have := count_le q 0 bm
  omega

theorem symNativeWord_len (q : Nat) (bm : List Bool) :
    (Gen.SymPhysical.native q 0 bm).length ≤ Capacity.value q + 4 * q + 6 := by
  have e1 : (Gen.SymPhysical.native q 0 bm).length =
      (natWord (Gen.SymPhysical.selectedGates q 0 bm).length).length + (frame (Gen.SymPhysical.top q 0 bm)).length +
        (CloseoutRowsTupleSeek.nativeWord (Gen.SymPhysical.selectedGates q 0 bm)).length := by
    simp only [Gen.SymPhysical.native, PCJ6e421fabe2aa4155_SourceSymmetricAssemble.circuitWord,
      PCJ6e421fabe2aa4155_SourceSymmetricAssemble.prefixWord, List.length_append]
  have e2 := symGates_len q bm
  have e3 := symNative_len q bm
  have e4 := symTop_len q bm
  have e5 := bitLen_le (Gen.SymPhysical.selectedGates q 0 bm).length
  rw [e1, DecompositionSource.natWord_length, frame_length']
  omega

theorem symPhys_le (q : Nat) (bm : List Bool) :
    Gen.SymPhysical.budget q 0 bm ≤ 49 * Capacity.value q + 30 * q + 101 := by
  have hH := shq_le q 0 bm
  have hP := pairsCost_le (Gen.SymPhysical.selectedGates q 0 bm)
  have e2 := symGates_len q bm
  have e3 := symNative_len q bm
  have e4 := symTop_len q bm
  have e5 := bitLen_le (Gen.SymPhysical.selectedGates q 0 bm).length
  have e6 := symSupport_len q bm
  unfold Gen.SymPhysical.budget Gen.SymReset.budget PCJ6e421fabe2aa4155_SourceSymmetricAssemble.budget
  omega

/-- **The SYM systematic factor's cost** is at most `65536·(q+1)^2`, for every support `S`. -/
theorem symSys_cost_le {q : Nat} (S : Finset (Fin q)) :
    SymSystematic.cost S ≤ symC * (q + 1) ^ symE := by
  rw [symCost_eq]
  have h1 := symPhys_le q (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap S)
  have h2 := symNativeWord_len q (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap S)
  have h3 := symSupport_len q (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap S)
  have hcap : Capacity.value q = 256 * (q + 1) ^ 2 := rfl
  have hq : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by decide) _
  unfold symBody symC symE
  generalize (q + 1) ^ 2 = X at hcap hq ⊢
  omega

/-! ### THR -/

/-- `(D, Cc)` bound the decomposition source's degree and coefficient (at the site: its own fields, `le_rfl`). -/
def thrC (D Cc : Nat) : Nat := 4096 * (Cc * 2 ^ D + 3) ^ 2 + 2 ^ 22
def thrE (D : Nat) : Nat := 2 * D + 3

theorem thrLoop_le (q n : Nat) (hn : n ≤ q) :
    PCJ6e421fabe2aa4155_SourceThresholdLoop.budget q n ≤ 4096 * (q + 1) ^ 3 + 3 * q + 3 := by
  unfold PCJ6e421fabe2aa4155_SourceThresholdLoop.budget PCJ6e421fabe2aa4155_SourceThresholdLoop.cost
  have h1 : n * (4096 * (q + 1) ^ 2 + 3) ≤ q * (4096 * (q + 1) ^ 2 + 3) := Nat.mul_le_mul_right _ hn
  have h2 : q * (4096 * (q + 1) ^ 2 + 3) = 4096 * (q * (q + 1) ^ 2) + 3 * q := by ring
  have h3 : q * (q + 1) ^ 2 ≤ (q + 1) ^ 3 := by
    have e : (q + 1) ^ 3 = (q + 1) * (q + 1) ^ 2 := by ring
    rw [e]
    exact Nat.mul_le_mul_right _ (Nat.le_succ q)
  omega

theorem thrSA_le (q n : Nat) (bits : List Bool) (hn : n ≤ q) (hlen : bits.length = q) :
    PCJ6e421fabe2aa4155_SourceSymmetricAssemble.budget (PCJ6e421fabe2aa4155_SourceThresholdTop.payload n)
      (PCJ6e421fabe2aa4155_SourceThresholdPhysical.gates q n bits) ≤ 4 * Capacity.value q + 6 * q + 11 := by
  have hP := pairsCost_le (PCJ6e421fabe2aa4155_SourceThresholdPhysical.gates q n bits)
  rw [PCJ6e421fabe2aa4155_SourceThresholdPhysical.gates_native, PCJ6e421fabe2aa4155_SourceThresholdPhysical.gates_support,
    PCJ6e421fabe2aa4155_SourceThresholdPhysical.gates_length] at hP
  have h0 := PCJ6e421fabe2aa4155_SourceThresholdBounds.outputs_bound q n bits hn hlen 0
  have h1 := PCJ6e421fabe2aa4155_SourceThresholdBounds.outputs_bound q n bits hn hlen 1
  have ht := PCJ6e421fabe2aa4155_SourceThresholdBounds.top_bound q n hn
  rw [frame_length'] at ht
  have hb := bitLen_le n
  unfold PCJ6e421fabe2aa4155_SourceSymmetricAssemble.budget
  rw [PCJ6e421fabe2aa4155_SourceThresholdPhysical.gates_length]
  omega

theorem thrPhys_le (q : Nat) (bm : List Bool) (hbm : bm.length = q) :
    Gen.ThresholdPhysical.budget q 0 bm hbm ≤ 55 * Capacity.value q + 102 * q + 168 + 4096 * (q + 1) ^ 3 := by
  have hH := shq_le q 0 bm
  have hc := count_le q 0 bm
  have hL := thrLoop_le q (Gen.SymmetricHeaderQuery.count q 0 bm) hc
  have hN : (natWord (Gen.SymmetricHeaderQuery.count q 0 bm)).length ≤ 2 * q + 3 := by
    rw [DecompositionSource.natWord_length]
    have := bitLen_le (Gen.SymmetricHeaderQuery.count q 0 bm)
    omega
  have hSA := thrSA_le q (Gen.SymmetricHeaderQuery.count q 0 bm) (Gen.ThresholdCache.bits q 0 bm hbm) hc hbm
  unfold Gen.ThresholdPhysical.budget Gen.ThresholdReady.budget Gen.ThresholdTopQuery.budget Gen.ThresholdQuery.budget
    Gen.ThresholdCache.budget PCJ6e421fabe2aa4155_SourceThresholdTop.budget PCJ6e421fabe2aa4155_SourceThresholdCold.budget
    PCJ6e421fabe2aa4155_SourceThresholdBitmap.budget
  omega

/-- The native THR circuit word (`SourceNativeBounds.circuit_bound`'s argument, restated here). -/
theorem thrNative_le (q n : Nat) (bits : List Bool) (hn : n ≤ q) (hlen : bits.length = q) :
    (PCJ6e421fabe2aa4155_SourceThresholdPhysical.native q n bits).length ≤ 2 * Capacity.value q + 2 * q + 3 := by
  have ho := PCJ6e421fabe2aa4155_SourceThresholdBounds.outputs_bound q n bits hn hlen 0
  have ht := PCJ6e421fabe2aa4155_SourceThresholdBounds.top_bound q n hn
  have hb := bitLen_le n
  unfold PCJ6e421fabe2aa4155_SourceThresholdPhysical.native PCJ6e421fabe2aa4155_SourceSymmetricAssemble.circuitWord
    PCJ6e421fabe2aa4155_SourceSymmetricAssemble.prefixWord
  rw [PCJ6e421fabe2aa4155_SourceThresholdPhysical.gates_length, PCJ6e421fabe2aa4155_SourceThresholdPhysical.gates_native]
  simp only [List.length_append, DecompositionSource.natWord_length]
  omega

theorem card_le {q : Nat} (S : Finset (Fin q)) : S.card ≤ q :=
  (Finset.card_le_univ S).trans_eq (Fintype.card_fin q)

/-- The top gate's decomposition request. -/
def topReq {q : Nat} (S : Finset (Fin q)) : ExactDecompositionRequest :=
  ⟨(normalizedThresholdParityCircuit S).top.support.card,
    nonStrictAsStrict (SupplierPipeline.retainedTopGate (normalizedThresholdParityCircuit S))⟩

theorem topArity_le {q : Nat} (S : Finset (Fin q)) : (topReq S).arity ≤ q := by
  have h1 := Finset.card_le_univ (normalizedThresholdParityCircuit S).top.support
  rw [Fintype.card_fin] at h1
  exact h1.trans (card_le S)

theorem topBits_le {q : Nat} (S : Finset (Fin q)) : (topReq S).gate.encodingBits ≤ (topReq S).arity + 1 := by
  have hp : (topReq S).gate.parametersBoundedBy 1 := by
    refine ⟨fun i => ?_, ?_⟩
    · simp only [topReq, CompilerSemantics.nonStrictAsStrict, SupplierPipeline.retainedTopGate,
        normalizedThresholdParityCircuit, thresholdParityTopGate]
      split <;> decide
    · simp only [topReq, CompilerSemantics.nonStrictAsStrict, SupplierPipeline.retainedTopGate,
        normalizedThresholdParityCircuit, thresholdParityTopGate]
      decide
  have h := ComponentwiseCircuitRestriction.encodingBits_le_of_parametersBoundedBy (topReq S).gate hp
  have h1 : natBitLength 1 = 1 := by simp only [natBitLength, Nat.log_one_right]
  rw [h1, Nat.mul_one] at h
  exact h

theorem topParam_le {q : Nat} (S : Finset (Fin q)) : DecompositionSource.parameter (topReq S) ≤ 2 * (q + 1) := by
  have h1 := topArity_le S
  have h2 := topBits_le S
  unfold DecompositionSource.parameter
  omega

theorem topSB_le (a : DecompositionAlgorithm) (D Cc : Nat) (hdeg : a.degree ≤ D) (hcoef : a.coefficient ≤ Cc)
    {q : Nat} (S : Finset (Fin q)) :
    DecompositionSource.sourceBudget a (topReq S) ≤ Cc * 2 ^ D * (q + 1) ^ (D + 1) := by
  have hp := topParam_le S
  have hp1 : 1 ≤ 2 * (q + 1) := by omega
  have e1 : (topReq S).arity + (topReq S).gate.encodingBits + 1 ≤ 2 * (q + 1) := hp
  have e2 : ((topReq S).arity + (topReq S).gate.encodingBits + 1) ^ a.degree ≤ (2 * (q + 1)) ^ D :=
    (Nat.pow_le_pow_left e1 _).trans (Nat.pow_le_pow_right hp1 hdeg)
  have e3 : (2 * (q + 1)) ^ D = 2 ^ D * (q + 1) ^ D := Nat.mul_pow _ _ _
  have e4 : (q + 1) ^ D ≤ (q + 1) ^ (D + 1) := Nat.pow_le_pow_right (by omega) (Nat.le_succ D)
  unfold DecompositionSource.sourceBudget
  calc a.coefficient * ((topReq S).arity + (topReq S).gate.encodingBits + 1) ^ a.degree
      ≤ Cc * (2 ^ D * (q + 1) ^ D) := Nat.mul_le_mul hcoef (e3 ▸ e2)
    _ ≤ Cc * (2 ^ D * (q + 1) ^ (D + 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ e4)
    _ = Cc * 2 ^ D * (q + 1) ^ (D + 1) := by ring

/-- The THR systematic cost as a function of the support (`ThrSystematic.cost a S` is this, `rfl`). -/
theorem thrCost_eq (a : DecompositionAlgorithm) {q : Nat} (S : Finset (Fin q)) :
    ThrSystematic.cost a S =
      (2 * Gen.ThresholdPhysical.budget q 0 (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap S)
          (Gen.ThresholdCanonical.bitmap_length S) +
        4 * (PCJd4d1d9d7d1fa4313_Production.thrWord (normalizedThresholdParityCircuit S)).length + 7) + 1 +
      ((12 * (PCJd4d1d9d7d1fa4313_Production.thrWord (normalizedThresholdParityCircuit S)).length + 13) + 1 +
        (PCJ6e421fabe2aa4155_SourceTopNative.budget a (normalizedThresholdParityCircuit S).top.wireCount (topReq S) + 1 +
          ((12 * (natWord (topReq S).arity ++ exactListWord (a.output (topReq S)).children).length + 13) + 1 +
            (2 * Gen.ThresholdPhysical.budget q 0 (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap S)
                (Gen.ThresholdCanonical.bitmap_length S) +
              4 * (CloseoutRowsTupleSeek.supportWord (PCJ6e421fabe2aa4155_SourceThresholdPhysical.gates q S.card
                (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap S))).length + 7)))) := rfl

/-- **The THR systematic factor's cost** is at most `thrC D Cc·(q+1)^(2D+3)`, for every support `S`. -/
theorem thrSys_cost_le (a : DecompositionAlgorithm) (D Cc : Nat) (hdeg : a.degree ≤ D) (hcoef : a.coefficient ≤ Cc)
    {q : Nat} (S : Finset (Fin q)) :
    ThrSystematic.cost a S ≤ thrC D Cc * (q + 1) ^ thrE D := by
  rw [thrCost_eq]
  have hbm := Gen.ThresholdCanonical.bitmap_length S
  have hTP := thrPhys_le q (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap S) hbm
  have hT : (PCJd4d1d9d7d1fa4313_Production.thrWord (normalizedThresholdParityCircuit S)).length ≤
      2 * Capacity.value q + 2 * q + 3 := by
    rw [← Gen.ThresholdCanonical.native_eq S 0]
    exact thrNative_le q _ _ (count_le q 0 _) hbm
  have hY : (CloseoutRowsTupleSeek.supportWord (PCJ6e421fabe2aa4155_SourceThresholdPhysical.gates q S.card
      (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap S))).length ≤ Capacity.value q := by
    rw [PCJ6e421fabe2aa4155_SourceThresholdPhysical.gates_support]
    exact PCJ6e421fabe2aa4155_SourceThresholdBounds.outputs_bound q S.card _ (card_le S) hbm 1
  have hA := topArity_le S
  have hPm := topParam_le S
  have hSB := topSB_le a D Cc hdeg hcoef S
  have hEB := DecompositionSource.entry_budget_coarse a (topReq S)
  have hOL := DecompositionSource.output_length a (topReq S)
  have hTW := DecompositionSource.thresholdWord_bound (topReq S).gate
  have hwc : (normalizedThresholdParityCircuit S).top.wireCount = (topReq S).arity := rfl
  have hbA := bitLen_le (topReq S).arity
  have hEO : (DecompositionSource.Entry.output a (topReq S)).length ≤ 2 * q + 3 + DecompositionSource.sourceBudget a (topReq S) := by
    unfold DecompositionSource.Entry.output
    rw [List.length_append, DecompositionSource.natWord_length]
    omega
  have hX : (natWord (topReq S).arity ++ exactListWord (a.output (topReq S)).children).length ≤
      2 * q + 3 + DecompositionSource.sourceBudget a (topReq S) := by
    rw [List.length_append, DecompositionSource.natWord_length]
    omega
  have hTN : PCJ6e421fabe2aa4155_SourceTopNative.budget a (normalizedThresholdParityCircuit S).top.wireCount (topReq S) ≤
      68 * (q + 1) + 20 + 2 * DecompositionSource.Entry.budget a (topReq S) +
        4 * (DecompositionSource.Entry.output a (topReq S)).length := by
    unfold PCJ6e421fabe2aa4155_SourceTopNative.budget PCJ6e421fabe2aa4155_SourceTopExtract.budget
      PCJ6e421fabe2aa4155_SourceTopExtract.rawBudget PCJ6e421fabe2aa4155_SourceTopEntry.budget
    rw [hwc]
    unfold DecompositionSource.parameter at hPm
    omega
  -- the closed-form bound
  have hZ1 : 1 ≤ (q + 1) ^ (D + 1) := Nat.one_le_pow _ _ (by omega)
  have hq1 : q + 1 ≤ (q + 1) ^ (D + 1) := Nat.le_self_pow (by omega) _
  have hB : DecompositionSource.sourceBudget a (topReq S) + DecompositionSource.parameter (topReq S) + 1 ≤
      (Cc * 2 ^ D + 3) * (q + 1) ^ (D + 1) := by
    have e : (Cc * 2 ^ D + 3) * (q + 1) ^ (D + 1) = Cc * 2 ^ D * (q + 1) ^ (D + 1) + 3 * (q + 1) ^ (D + 1) := by ring
    omega
  have hW : 1024 * (DecompositionSource.sourceBudget a (topReq S) + DecompositionSource.parameter (topReq S) + 1) ^ 2 ≤
      1024 * ((Cc * 2 ^ D + 3) ^ 2 * (q + 1) ^ (2 * D + 3)) := by
    have e1 := Nat.pow_le_pow_left hB 2
    have e2 : ((Cc * 2 ^ D + 3) * (q + 1) ^ (D + 1)) ^ 2 = (Cc * 2 ^ D + 3) ^ 2 * (q + 1) ^ (2 * D + 2) := by ring
    have e3 : (q + 1) ^ (2 * D + 2) ≤ (q + 1) ^ (2 * D + 3) := Nat.pow_le_pow_right (by omega) (by omega)
    have e4 := Nat.mul_le_mul_left ((Cc * 2 ^ D + 3) ^ 2) e3
    omega
  have hBZ : (Cc * 2 ^ D + 3) * (q + 1) ^ (D + 1) ≤ (Cc * 2 ^ D + 3) ^ 2 * (q + 1) ^ (2 * D + 3) := by
    have e1 : 1 ≤ Cc * 2 ^ D + 3 := by omega
    have e2 : (Cc * 2 ^ D + 3) ^ 2 * (q + 1) ^ (2 * D + 3) =
        ((Cc * 2 ^ D + 3) * (q + 1) ^ (D + 1)) * ((Cc * 2 ^ D + 3) * (q + 1) ^ (D + 2)) := by ring
    have e3 : 1 ≤ (Cc * 2 ^ D + 3) * (q + 1) ^ (D + 2) :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by omega))))
    rw [e2]
    exact Nat.le_mul_of_pos_right _ e3
  have hSBZ : DecompositionSource.sourceBudget a (topReq S) + 2 * q + 3 ≤ (Cc * 2 ^ D + 3) * (q + 1) ^ (D + 1) := by
    have e : (Cc * 2 ^ D + 3) * (q + 1) ^ (D + 1) = Cc * 2 ^ D * (q + 1) ^ (D + 1) + 3 * (q + 1) ^ (D + 1) := by ring
    omega
  have hX3 : (q + 1) ^ 3 ≤ (q + 1) ^ (2 * D + 3) := Nat.pow_le_pow_right (by omega) (by omega)
  have hX2 : (q + 1) ^ 2 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hq3 : q + 1 ≤ (q + 1) ^ 3 := Nat.le_self_pow (by omega) _
  have hcap : Capacity.value q = 256 * (q + 1) ^ 2 := rfl
  have hgoal : thrC D Cc * (q + 1) ^ thrE D =
      4096 * ((Cc * 2 ^ D + 3) ^ 2 * (q + 1) ^ (2 * D + 3)) + 4194304 * (q + 1) ^ (2 * D + 3) := by
    unfold thrC thrE; ring
  rw [hgoal]
  generalize (Cc * 2 ^ D + 3) ^ 2 * (q + 1) ^ (2 * D + 3) = W at hW hBZ ⊢
  generalize (Cc * 2 ^ D + 3) * (q + 1) ^ (D + 1) = BZ at hBZ hSBZ hB
  generalize (q + 1) ^ (2 * D + 3) = E at hX3 ⊢
  generalize (q + 1) ^ 3 = X3 at hX3 hX2 hq3 hTP
  generalize (q + 1) ^ 2 = X2 at hX2 hcap
  omega

end
end NearCubicWires.SourceFactorSel.SysCost
end

