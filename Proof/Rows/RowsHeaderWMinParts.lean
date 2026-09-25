import Proof.Rows.RowsHeaderWBase
import Proof.Rows.RowsInitBinWords

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsHeaderW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation NearCubicWires.P1Closure
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.PacketsGlue.RequestMeta
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
noncomputable section

/-! ## 1. `N` and its bit length as request stages -/

theorem poolN_eq (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (r : Request) :
    poolN selector a r = twoK a r * childTotal a r + 1 := by
  have hA := alphabet_eq a r
  unfold alphabet Packets.alphabet at hA
  have hc : (NearCubicWires.RepairSource.CloseoutFinal.C10SupplierRowInput.childList a (Packets.live (r.family a))
      (r.family a).occurrences).length = childTotal a r := by omega
  unfold poolN Packets.pool BinaryPool.pool
  rw [List.length_cons, List.length_ofFn, NearCubicWires.RepairSource.CloseoutFinal.C10SupplierRowInput.liveList_length, hc]
  rfl

/-- `N` as a request stage. -/
def nStage (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) : UnaryStage a (poolN selector a) :=
  (((twoKStage a).pairP (childStage a) mulMap2 8 2 mul_cost).thenMapP (plusMap 1) (2 * 1 + 4) 1
    (plus_cost 1)).ofEq (fun r => (poolN_eq selector a r).symm)

/-- `natBitLength N` as a request stage. -/
def bStage (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) :
    UnaryStage a (fun r => natBitLength (poolN selector a r)) :=
  RowsInit.BinWords.bitLenS (nStage selector a)

/-! ## 2. Bit-length facts -/

/-- A degree whose bit length is at most `N`'s is at most `2N+1` (so reading it in unary is affordable). -/
theorem bits_true (d N : ℕ) (h : natBitLength d ≤ natBitLength N) : d ≤ 2 * N + 1 := by
  unfold natBitLength at h
  have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) d
  have h3 : 2 ^ (Nat.log 2 d).succ ≤ 2 ^ (Nat.log 2 N).succ := Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp at h3
    omega
  · have h2 := Nat.pow_log_le_self 2 (show N ≠ 0 by omega)
    rw [Nat.pow_succ] at h3
    omega

/-- A degree whose bit length exceeds `N`'s exceeds `N`. -/
theorem bits_false (d N : ℕ) (h : natBitLength N < natBitLength d) : N < d := by
  unfold natBitLength at h
  have hd : d ≠ 0 := by
    intro h0
    subst h0
    simp at h
  have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
  have h2 := Nat.pow_log_le_self 2 hd
  have h3 : 2 ^ (Nat.log 2 N).succ ≤ 2 ^ (Nat.log 2 d) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-! ## 3. The compare, heads back to `0` -/

theorem cmp_masked (U p : ℕ) : ∃ A : Fin (3 + 1) → List Bool,
    Step (MaskedReset.machine MatrixBucketDimensions.Compare.raw (fun _ => true)) (2 * (min U p + 2) + 2) (fun _ => 0)
      (Fin.addCases (m := 3) (n := 1) ![UnaryTemplate.tape U, List.replicate p true, []] (fun _ => [])) (fun _ => 0) A ∧
    A 0 = UnaryTemplate.tape U ∧ A 1 = List.replicate p true ∧ A 2 = [decide (U ≤ p)] := by
  obtain ⟨r, hr, hf, hs⟩ := MatrixBucketDimensions.Compare.raw_run U p
  have h : Step MatrixBucketDimensions.Compare.raw (min U p + 2) (fun _ => 0)
      ![UnaryTemplate.tape U, List.replicate p true, []] ![min U p + 1, min U p, 0]
      ![UnaryTemplate.tape U, List.replicate p true, [decide (U ≤ p)]] :=
    ⟨r, hr, by rw [hf]; rfl, by rw [hf]; rfl, hs.le⟩
  obtain ⟨k, -, mk⟩ := RowsInit.mask_empty h (fun _ => true) (fun _ _ => rfl)
  have hk := (mk.congr_in (RowsInit.zeros_addCases _ _) rfl).congr (RowsInit.zeros_masked _) rfl
  refine ⟨_, hk, ?_, ?_, ?_⟩
  · show Fin.addCases (m := 3) (n := 1) (motive := fun _ => List Bool) _ _ (Fin.castAdd 1 0) = _
    rw [Fin.addCases_left]
    rfl
  · show Fin.addCases (m := 3) (n := 1) (motive := fun _ => List Bool) _ _ (Fin.castAdd 1 1) = _
    rw [Fin.addCases_left]
    rfl
  · show Fin.addCases (m := 3) (n := 1) (motive := fun _ => List Bool) _ _ (Fin.castAdd 1 2) = _
    rw [Fin.addCases_left]
    rfl

/-! ## 4. The skip pass: `natWord 3`, `natWord w`, `natWord degree` (the last with a blank backing) -/

def kS1 : Fin 3 → Fin 7 := ![0, 1, 2]
def kS2 : Fin 3 → Fin 7 := ![0, 3, 4]
def kS3 : Fin 3 → Fin 7 := ![0, 5, 6]
theorem kS1_inj : Function.Injective kS1 := by decide
theorem kS2_inj : Function.Injective kS2 := by decide
theorem kS3_inj : Function.Injective kS3 := by decide

def skipChain := Composition.machine (Composition.machine
  (RecoveryFocus.machine kS1 (PCPPQueryField.machine false)) (RecoveryFocus.machine kS2 (PCPPQueryField.machine false)))
  (RecoveryFocus.machine kS3 (PCPPQueryField.machine false))
def skipCost (w deg : ℕ) : ℕ :=
  (2 * natBitLength 3 + 3) + 1 + (2 * natBitLength w + 3) + 1 + (2 * natBitLength deg + 3)
def kIn (src : List Bool) : Fin 7 → List Bool := fun i => if i.val = 0 then src else []

theorem overlay_nil (t : List Bool) : StablePartition.Workspace.overlay t [] = t := by
  simp [StablePartition.Workspace.overlay]

theorem skip_chain (w deg : ℕ) (rest : List Bool) :
    ∃ H A, Step skipChain (skipCost w deg) (fun _ => 0) (kIn (natWord 3 ++ natWord w ++ natWord deg ++ rest)) H A ∧
      A 0 = natWord 3 ++ natWord w ++ natWord deg ++ rest ∧ A 5 = UnaryTemplate.tape (natBitLength deg) := by
  classical
  set src := natWord 3 ++ natWord w ++ natWord deg ++ rest with hsrc
  set A0 := kIn src with hA0
  have b0 : ∀ x : Fin 7, x.val ≠ 0 → A0 x = [] := fun x hx => by simp [hA0, kIn, hx]
  -- skip `natWord 3`
  have s1 := RowsInit.skip_step [] (natWord w ++ natWord deg ++ rest) [] 3
  have e1 : [] ++ natWord 3 ++ (natWord w ++ natWord deg ++ rest) = src := by
    rw [hsrc]; simp only [List.nil_append, List.append_assoc]
  rw [e1] at s1
  have d1 := s1.dock kS1 kS1_inj (fun _ => 0) A0 (fun j => by fin_cases j <;> rfl) (fun j => by
    fin_cases j
    · show A0 0 = src
      simp [hA0, kIn]
    · exact b0 1 (by decide)
    · exact b0 2 (by decide))
  set H1 := dockH kS1 (fun _ => 0) ![([] : List Bool).length + 2 * natBitLength 3 + 1, 0, 0] with hH1
  set A1 := install kS1 A0 ![src, StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength 3)) [], []]
    with hA1
  have o1 : ∀ x : Fin 7, x ≠ 0 → x ≠ 1 → x ≠ 2 → H1 x = 0 ∧ A1 x = A0 x := by
    intro x h0 h1 h2
    have hn : ∀ j, kS1 j ≠ x := by
      intro j he; fin_cases j
      · exact h0 he.symm
      · exact h1 he.symm
      · exact h2 he.symm
    exact ⟨dockH_other _ _ _ _ hn, install_other _ _ _ _ hn⟩
  have h1_0 : H1 0 = (natWord 3).length := by
    show H1 (kS1 0) = _
    rw [hH1, dockH_slot _ kS1_inj, RowsInit.natWord_length]
    rfl
  have a1_0 : A1 0 = src := by
    show A1 (kS1 0) = _
    rw [hA1, install_slot _ kS1_inj]
    rfl
  -- skip `natWord w`
  have s2 := RowsInit.skip_step (natWord 3) (natWord deg ++ rest) [] w
  have e2 : natWord 3 ++ natWord w ++ (natWord deg ++ rest) = src := by
    rw [hsrc]; simp only [List.append_assoc]
  rw [e2] at s2
  have d2 := s2.dock kS2 kS2_inj H1 A1 (fun j => by
      fin_cases j
      · exact h1_0
      · exact (o1 3 (by decide) (by decide) (by decide)).1
      · exact (o1 4 (by decide) (by decide) (by decide)).1)
    (fun j => by
      fin_cases j
      · exact a1_0
      · exact ((o1 3 (by decide) (by decide) (by decide)).2).trans (b0 3 (by decide))
      · exact ((o1 4 (by decide) (by decide) (by decide)).2).trans (b0 4 (by decide)))
  set H2 := dockH kS2 H1 ![(natWord 3).length + 2 * natBitLength w + 1, 0, 0] with hH2
  set A2 := install kS2 A1 ![src, StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength w)) [], []]
    with hA2
  have o2 : ∀ x : Fin 7, x ≠ 0 → x ≠ 3 → x ≠ 4 → H2 x = H1 x ∧ A2 x = A1 x := by
    intro x h0 h3 h4
    have hn : ∀ j, kS2 j ≠ x := by
      intro j he; fin_cases j
      · exact h0 he.symm
      · exact h3 he.symm
      · exact h4 he.symm
    exact ⟨dockH_other _ _ _ _ hn, install_other _ _ _ _ hn⟩
  have h2_0 : H2 0 = (natWord 3 ++ natWord w).length := by
    show H2 (kS2 0) = _
    rw [hH2, dockH_slot _ kS2_inj, List.length_append, RowsInit.natWord_length w]
    rfl
  have a2_0 : A2 0 = src := by
    show A2 (kS2 0) = _
    rw [hA2, install_slot _ kS2_inj]
    rfl
  -- skip `natWord deg` with a blank backing
  have s3 := RowsInit.skip_step (natWord 3 ++ natWord w) rest [] deg
  have e3 : natWord 3 ++ natWord w ++ natWord deg ++ rest = src := rfl
  rw [e3] at s3
  have d3 := s3.dock kS3 kS3_inj H2 A2 (fun j => by
      fin_cases j
      · exact h2_0
      · exact ((o2 5 (by decide) (by decide) (by decide)).1).trans (o1 5 (by decide) (by decide) (by decide)).1
      · exact ((o2 6 (by decide) (by decide) (by decide)).1).trans (o1 6 (by decide) (by decide) (by decide)).1)
    (fun j => by
      fin_cases j
      · exact a2_0
      · exact ((o2 5 (by decide) (by decide) (by decide)).2).trans
          (((o1 5 (by decide) (by decide) (by decide)).2).trans (b0 5 (by decide)))
      · exact ((o2 6 (by decide) (by decide) (by decide)).2).trans
          (((o1 6 (by decide) (by decide) (by decide)).2).trans (b0 6 (by decide))))
  refine ⟨_, _, (d1.seq d2).seq d3, ?_, ?_⟩
  · show install kS3 A2 _ (kS3 0) = _
    rw [install_slot _ kS3_inj]
    rfl
  · show install kS3 A2 _ (kS3 1) = _
    rw [install_slot _ kS3_inj]
    exact overlay_nil _

/-- The skip pass under the all-heads masked reset. -/
theorem skip_masked (w deg : ℕ) (rest : List Bool) : ∃ A : Fin (7 + 1) → List Bool,
    Step (MaskedReset.machine skipChain (fun _ => true)) (2 * skipCost w deg + 2) (fun _ => 0)
      (Fin.addCases (m := 7) (n := 1) (kIn (natWord 3 ++ natWord w ++ natWord deg ++ rest)) (fun _ => [])) (fun _ => 0) A ∧
    A 0 = natWord 3 ++ natWord w ++ natWord deg ++ rest ∧ A 5 = UnaryTemplate.tape (natBitLength deg) := by
  obtain ⟨H, A, h, a0, a5⟩ := skip_chain w deg rest
  obtain ⟨k, -, mk⟩ := RowsInit.mask_empty h (fun _ => true) (fun _ _ => rfl)
  have hk := (mk.congr_in (RowsInit.zeros_addCases _ _) rfl).congr (RowsInit.zeros_masked _) rfl
  refine ⟨_, hk, ?_, ?_⟩
  · show Fin.addCases (m := 7) (n := 1) (motive := fun _ => List Bool) A _ (Fin.castAdd 1 0) = _
    rw [Fin.addCases_left]
    exact a0
  · show Fin.addCases (m := 7) (n := 1) (motive := fun _ => List Bool) A _ (Fin.castAdd 1 5) = _
    rw [Fin.addCases_left]
    exact a5

/-! ## 5. The read pass: skip `natWord 3`, `natWord w`, read `degree` -/

def rS1 : Fin 3 → Fin 15 := ![0, 1, 2]
def rS2 : Fin 3 → Fin 15 := ![0, 3, 4]
def rS3 : Fin 11 → Fin 15 := ![0, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
theorem rS1_inj : Function.Injective rS1 := by decide
theorem rS2_inj : Function.Injective rS2 := by decide
theorem rS3_inj : Function.Injective rS3 := by decide

def readChain := Composition.machine (Composition.machine
  (RecoveryFocus.machine rS1 (PCPPQueryField.machine false)) (RecoveryFocus.machine rS2 (PCPPQueryField.machine false)))
  (RecoveryFocus.machine rS3 PCJ45bee56da9f34d5a_CapReader.machine)
def readCost (w deg : ℕ) : ℕ :=
  (2 * natBitLength 3 + 3) + 1 + (2 * natBitLength w + 3) + 1 + (8 * deg + 20 * natBitLength deg + 17)
def rIn (src : List Bool) : Fin 15 → List Bool := fun i => if i.val = 0 then src else []

theorem read_chain (w deg : ℕ) (rest : List Bool) :
    ∃ H A, Step readChain (readCost w deg) (fun _ => 0) (rIn (natWord 3 ++ natWord w ++ natWord deg ++ rest)) H A ∧
      A 0 = natWord 3 ++ natWord w ++ natWord deg ++ rest ∧ A 12 = List.replicate deg true ∧
      A 14 = UnaryTemplate.tape deg := by
  classical
  set src := natWord 3 ++ natWord w ++ natWord deg ++ rest with hsrc
  set A0 := rIn src with hA0
  have b0 : ∀ x : Fin 15, x.val ≠ 0 → A0 x = [] := fun x hx => by simp [hA0, rIn, hx]
  have s1 := RowsInit.skip_step [] (natWord w ++ natWord deg ++ rest) [] 3
  have e1 : [] ++ natWord 3 ++ (natWord w ++ natWord deg ++ rest) = src := by
    rw [hsrc]; simp only [List.nil_append, List.append_assoc]
  rw [e1] at s1
  have d1 := s1.dock rS1 rS1_inj (fun _ => 0) A0 (fun j => by fin_cases j <;> rfl) (fun j => by
    fin_cases j
    · show A0 0 = src
      simp [hA0, rIn]
    · exact b0 1 (by decide)
    · exact b0 2 (by decide))
  set H1 := dockH rS1 (fun _ => 0) ![([] : List Bool).length + 2 * natBitLength 3 + 1, 0, 0] with hH1
  set A1 := install rS1 A0 ![src, StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength 3)) [], []]
    with hA1
  have o1 : ∀ x : Fin 15, x ≠ 0 → x ≠ 1 → x ≠ 2 → H1 x = 0 ∧ A1 x = A0 x := by
    intro x h0 h1 h2
    have hn : ∀ j, rS1 j ≠ x := by
      intro j he; fin_cases j
      · exact h0 he.symm
      · exact h1 he.symm
      · exact h2 he.symm
    exact ⟨dockH_other _ _ _ _ hn, install_other _ _ _ _ hn⟩
  have h1_0 : H1 0 = (natWord 3).length := by
    show H1 (rS1 0) = _
    rw [hH1, dockH_slot _ rS1_inj, RowsInit.natWord_length]
    rfl
  have a1_0 : A1 0 = src := by
    show A1 (rS1 0) = _
    rw [hA1, install_slot _ rS1_inj]
    rfl
  have s2 := RowsInit.skip_step (natWord 3) (natWord deg ++ rest) [] w
  have e2 : natWord 3 ++ natWord w ++ (natWord deg ++ rest) = src := by
    rw [hsrc]; simp only [List.append_assoc]
  rw [e2] at s2
  have d2 := s2.dock rS2 rS2_inj H1 A1 (fun j => by
      fin_cases j
      · exact h1_0
      · exact (o1 3 (by decide) (by decide) (by decide)).1
      · exact (o1 4 (by decide) (by decide) (by decide)).1)
    (fun j => by
      fin_cases j
      · exact a1_0
      · exact ((o1 3 (by decide) (by decide) (by decide)).2).trans (b0 3 (by decide))
      · exact ((o1 4 (by decide) (by decide) (by decide)).2).trans (b0 4 (by decide)))
  set H2 := dockH rS2 H1 ![(natWord 3).length + 2 * natBitLength w + 1, 0, 0] with hH2
  set A2 := install rS2 A1 ![src, StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength w)) [], []]
    with hA2
  have o2 : ∀ x : Fin 15, x ≠ 0 → x ≠ 3 → x ≠ 4 → H2 x = H1 x ∧ A2 x = A1 x := by
    intro x h0 h3 h4
    have hn : ∀ j, rS2 j ≠ x := by
      intro j he; fin_cases j
      · exact h0 he.symm
      · exact h3 he.symm
      · exact h4 he.symm
    exact ⟨dockH_other _ _ _ _ hn, install_other _ _ _ _ hn⟩
  have h2_0 : H2 0 = (natWord 3 ++ natWord w).length := by
    show H2 (rS2 0) = _
    rw [hH2, dockH_slot _ rS2_inj, List.length_append, RowsInit.natWord_length w]
    rfl
  have a2_0 : A2 0 = src := by
    show A2 (rS2 0) = _
    rw [hA2, install_slot _ rS2_inj]
    rfl
  have blank2 : ∀ x : Fin 15, 5 ≤ x.val → H2 x = 0 ∧ A2 x = [] := by
    intro x hx
    have n0 : x ≠ 0 := fun h => by rw [h] at hx; exact absurd hx (by decide)
    have n1 : x ≠ 1 := fun h => by rw [h] at hx; exact absurd hx (by decide)
    have n2 : x ≠ 2 := fun h => by rw [h] at hx; exact absurd hx (by decide)
    have n3 : x ≠ 3 := fun h => by rw [h] at hx; exact absurd hx (by decide)
    have n4 : x ≠ 4 := fun h => by rw [h] at hx; exact absurd hx (by decide)
    rw [(o2 x n0 n3 n4).1, (o2 x n0 n3 n4).2, (o1 x n0 n1 n2).1, (o1 x n0 n1 n2).2]
    exact ⟨rfl, b0 x (fun h => n0 (Fin.ext h))⟩
  -- read `deg`
  obtain ⟨HR, AR, sR, r0, -, r8, -, -, -, r10, -⟩ := RowsInit.read_step (natWord 3 ++ natWord w) rest deg
  have d3 := sR.dock rS3 rS3_inj H2 A2 (fun j => by
      by_cases hj : j = 0
      · subst hj
        exact h2_0
      · have hv : 5 ≤ (rS3 j).val := by
          revert j
          decide
        rw [(blank2 _ hv).1]
        fin_cases j <;> first | exact absurd rfl hj | rfl)
    (fun j => by
      by_cases hj : j = 0
      · subst hj
        exact a2_0
      · have hv : 5 ≤ (rS3 j).val := by
          revert j
          decide
        rw [(blank2 _ hv).2]
        fin_cases j <;> first | exact absurd rfl hj | rfl)
  refine ⟨_, _, (d1.seq d2).seq d3, ?_, ?_, ?_⟩
  · show install rS3 A2 AR (rS3 0) = _
    rw [install_slot _ rS3_inj]
    exact r0
  · show install rS3 A2 AR (rS3 8) = _
    rw [install_slot _ rS3_inj]
    exact r8
  · show install rS3 A2 AR (rS3 10) = _
    rw [install_slot _ rS3_inj]
    exact r10

/-- The read pass under the all-heads masked reset. -/
theorem read_masked (w deg : ℕ) (rest : List Bool) : ∃ A : Fin (15 + 1) → List Bool,
    Step (MaskedReset.machine readChain (fun _ => true)) (2 * readCost w deg + 2) (fun _ => 0)
      (Fin.addCases (m := 15) (n := 1) (rIn (natWord 3 ++ natWord w ++ natWord deg ++ rest)) (fun _ => [])) (fun _ => 0) A ∧
    A 0 = natWord 3 ++ natWord w ++ natWord deg ++ rest ∧ A 12 = List.replicate deg true ∧
      A 14 = UnaryTemplate.tape deg := by
  obtain ⟨H, A, h, a0, a12, a14⟩ := read_chain w deg rest
  obtain ⟨k, -, mk⟩ := RowsInit.mask_empty h (fun _ => true) (fun _ _ => rfl)
  have hk := (mk.congr_in (RowsInit.zeros_addCases _ _) rfl).congr (RowsInit.zeros_masked _) rfl
  refine ⟨_, hk, ?_, ?_, ?_⟩
  · show Fin.addCases (m := 15) (n := 1) (motive := fun _ => List Bool) A _ (Fin.castAdd 1 0) = _
    rw [Fin.addCases_left]
    exact a0
  · show Fin.addCases (m := 15) (n := 1) (motive := fun _ => List Bool) A _ (Fin.castAdd 1 12) = _
    rw [Fin.addCases_left]
    exact a12
  · show Fin.addCases (m := 15) (n := 1) (motive := fun _ => List Bool) A _ (Fin.castAdd 1 14) = _
    rw [Fin.addCases_left]
    exact a14

theorem dt_run (n : ℕ) :
    Step (RepairSource.ProjectionNormalization.DimensionTemplate.machine false) (2 * n + 8) (fun _ => 0)
      ![List.replicate n true, [], []] (fun _ => 0)
      ![List.replicate n true, UnaryTemplate.tape n, List.replicate (n + 3) false] :=
  RepairSource.CloseoutFinal.C10CompareDockLit.step_of_clock
    (RepairSource.ProjectionNormalization.DimensionTemplate.ready false n)

end
end RowsHeaderW
