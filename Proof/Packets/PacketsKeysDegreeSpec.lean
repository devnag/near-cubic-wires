import Proof.Packets.PacketsKeysNativeStages
import Proof.Packets.PacketsWinSum

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.PacketsKeys.Degree
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketsGlue NearCubicWires.PacketsGlue.RequestMeta
noncomputable section

/-! ## `foldl max` -/

theorem foldl_max_le (L : List ℕ) (d : ℕ) : ∀ b, b ≤ d → (∀ x ∈ L, x ≤ d) → L.foldl max b ≤ d := by
  induction L with
  | nil => intro b hb _; simpa using hb
  | cons y L ih =>
    intro b hb hL
    simp only [List.foldl_cons]
    exact ih _ (max_le hb (hL y (by simp))) (fun x hx => hL x (by simp [hx]))

theorem le_foldl_max (L : List ℕ) : ∀ b, b ≤ L.foldl max b ∧ ∀ x ∈ L, x ≤ L.foldl max b := by
  induction L with
  | nil => intro b; simp
  | cons y L ih =>
    intro b
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (max b y)
    refine ⟨(le_max_left b y).trans h1, ?_⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact (le_max_right b x).trans h1
    · exact h2 x hx

/-- A list's `foldl max 0` is any upper bound that occurs in it. -/
theorem foldl_max_eq (L : List ℕ) (d : ℕ) (hub : ∀ x ∈ L, x ≤ d) (hmem : d ∈ L) : L.foldl max 0 = d :=
  le_antisymm (foldl_max_le L d 0 (Nat.zero_le d) hub) ((le_foldl_max L 0).2 d hmem)

/-! ## The raw coordinate degree is `2 · Σ window` -/

theorem rawFrom_eq (D : ℕ) (w : Fin D → ℕ) (W : ℕ → ℕ) (hw : ∀ l (h : l < D), w ⟨l, h⟩ = W l) (t : ℕ) :
    ∀ k lev, lev + k = D →
      CloseoutRawRows.structuralListCoordinateRawDegreeFrom D w t lev =
        t + 2 * ∑ i ∈ Finset.range k, W (lev + i) := by
  intro k
  induction k with
  | zero =>
    intro lev h
    rw [CloseoutRawRows.structuralListCoordinateRawDegreeFrom, dif_neg (by omega)]
    simp
  | succ k ih =>
    intro lev h
    rw [CloseoutRawRows.structuralListCoordinateRawDegreeFrom, dif_pos (by omega), ih (lev + 1) (by omega),
      hw lev (by omega), Finset.sum_range_succ']
    have e : ∀ i, lev + 1 + i = lev + (i + 1) := fun i => by ring
    simp only [e, Nat.add_zero]
    ring

/-- **`coordinateDegree = walkLength · (windowSum · 2)`** at every request's own family data. -/
theorem coord_eq (a : DecompositionAlgorithm) (r : Request) :
    Packets.coordinateDegree (occ a r) (live a r) (Request.denominator a r) = walkLength a r * (windowSum a r * 2) := by
  unfold Packets.coordinateDegree CloseoutRawRows.structuralListCoordinateRawDegree
  rw [rawFrom_eq (canonicalGradedDepth (LiveRows.bound (occ a r) (live a r))) _ (fun l => window a r l)
    (fun l h => rfl) _ (depth a r) 0 (Nat.zero_add _)]
  simp only [windowSum, walkLength, SupplierListSchedule.gradedTerminalWindow, Nat.zero_add]
  ring

/-! ## Non-emptiness of the family's index lists -/

theorem seedList_pos {q : ℕ} (o : List (SupportedNormalizedGate q)) (I : Finset (Fin q)) (den : ℕ) :
    0 < (Packets.seedList o I den).length := by
  unfold Packets.seedList
  rw [List.length_ofFn, C10SupplierWidth.card_walkSample]
  positivity

theorem symOff_pos (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : ℕ) : 0 < (Packets.symOffsetList r).length := by
  rw [← RowsInit.Count.symSelOf_list r four L target]
  exact Finset.prod_pos (fun i _ => Nat.succ_pos _)

/-! ## The largest prime `≤ cutoff` -/

theorem pmax_spec (c : ℕ) (hc : 2 ≤ c) :
    ∃ h : Fintype.card (PrimeIndex c) - 1 < Fintype.card (PrimeIndex c),
      primeAt c (Fintype.card (PrimeIndex c) - 1) = ((primeIndexFinEquiv c).symm ⟨_, h⟩).val ∧
      ∀ p : PrimeIndex c, p.val ≤ ((primeIndexFinEquiv c).symm ⟨_, h⟩).val := by
  have hN : 1 ≤ Fintype.card (PrimeIndex c) := by
    rw [card_primeIndex, PrimeCount.pc_eq]
    exact Finset.card_pos.mpr ⟨2, mem_primesUpTo.mpr ⟨Nat.prime_two, hc⟩⟩
  have hlt : Fintype.card (PrimeIndex c) - 1 < Fintype.card (PrimeIndex c) := by omega
  refine ⟨hlt, ?_, ?_⟩
  · unfold primeAt
    rw [dif_pos hlt]
  · intro p
    have h1 : (primeIndexFinEquiv c) p ≤ ⟨_, hlt⟩ := by
      rw [Fin.le_def]
      have := ((primeIndexFinEquiv c) p).isLt
      show _ ≤ Fintype.card (PrimeIndex c) - 1
      omega
    have hmono : Monotone (fun i : Fin (Fintype.card (PrimeIndex c)) => (primeIndexFinEquiv c).symm i) :=
      (Fintype.orderIsoFinOfCardEq (PrimeIndex c) rfl).monotone
    have h2 := hmono h1
    simp only [Equiv.symm_apply_apply] at h2
    exact h2

/-! ## The closed form -/

/-- `[n = 0]`. -/
def isZ (n : ℕ) : ℕ := if n = 0 then 1 else 0

/-- The THR largest prime `primeAt cutoff (π(cutoff) - 1)` (`primeAt 0 0 = 1` off THR). -/
def pmaxOf (a : DecompositionAlgorithm) (r : Request) : ℕ := primeAt (cutoffOf a r) (primeCountOf a r - 1)

/-- The per-kind degree factor: SYM `#circuits`, THR `[|Sel| ≠ 0] · digits(pmax)`, terminal `0`. -/
def facOf (a : DecompositionAlgorithm) (r : Request) : ℕ :=
  isZ (thrFlag r) * Native.nCirc r + thrFlag r * (isZ (isZ (RowsInit.Count.thrSelOf a r)) * Nat.clog 2 (pmaxOf a r + 1))

/-- **The request degree in closed form.** -/
theorem degree_eq (a : DecompositionAlgorithm) (r : Request) :
    degree a r = facOf a r * (walkLength a r * (windowSum a r * 2)) := by
  rw [← coord_eq a r]
  cases r with
  | terminal =>
    simp [degree, Request.degree, Request.family, facOf, isZ, thrFlag, Native.nCirc]
  | sym r four L tg =>
    have hf : facOf a (.sym r four L tg) = r.circuits.length := by
      simp [facOf, isZ, thrFlag, Native.nCirc]
    rw [hf]
    unfold degree Request.degree
    apply foldl_max_eq
    · intro x hx
      obtain ⟨row, hrow, rfl⟩ := List.mem_map.1 hx
      obtain ⟨e, _, hrow⟩ := List.mem_flatMap.1 hrow
      obtain ⟨off, _, rfl⟩ := List.mem_map.1 hrow
      exact le_refl _
    · obtain ⟨e0, he0⟩ := List.exists_mem_of_length_pos (seedList_pos (symmetricFourfoldOccurrences r)
        (CyclicChoice.live (symmetricFourfoldOccurrences r) L) (symmetricListDenominator r tg))
      obtain ⟨o0, ho0⟩ := List.exists_mem_of_length_pos (symOff_pos r four L tg)
      exact List.mem_map.2 ⟨_, List.mem_flatMap.2 ⟨e0, he0, List.mem_map.2 ⟨o0, ho0, rfl⟩⟩, rfl⟩
  | thr r four L tg =>
    have h563 : 563 ≤ CloseoutFinalC10ThresholdRows.primeCutoff a r tg := by
      unfold CloseoutFinalC10ThresholdRows.primeCutoff
      exact canonicalPrimeCutoff_ge_563 _ _
    obtain ⟨hlt, hpm, hmax⟩ := pmax_spec (CloseoutFinalC10ThresholdRows.primeCutoff a r tg) (by omega)
    have hp0pos : 0 < ((primeIndexFinEquiv (CloseoutFinalC10ThresholdRows.primeCutoff a r tg)).symm ⟨_, hlt⟩).val :=
      (mem_primesUpTo.mp ((primeIndexFinEquiv (CloseoutFinalC10ThresholdRows.primeCutoff a r tg)).symm
        ⟨_, hlt⟩).property).1.pos
    have hpmax : pmaxOf a (.thr r four L tg) =
        ((primeIndexFinEquiv (CloseoutFinalC10ThresholdRows.primeCutoff a r tg)).symm ⟨_, hlt⟩).val := hpm
    by_cases hs : RowsInit.Count.thrSelOf a (.thr r four L tg) = 0
    · have hnil : Packets.thrSelectionList a r = [] := by
        apply List.eq_nil_of_length_eq_zero
        rw [← RowsInit.Count.thrSelOf_list a r four L tg]
        exact hs
      have hf : facOf a (.thr r four L tg) = 0 := by
        simp [facOf, isZ, thrFlag, hs]
      rw [hf, Nat.zero_mul]
      unfold degree Request.degree
      simp [Request.family, Packets.thrFamily, hnil]
      rfl
    · have hf : facOf a (.thr r four L tg) =
          modulusDigitCount ((primeIndexFinEquiv (CloseoutFinalC10ThresholdRows.primeCutoff a r tg)).symm
            ⟨_, hlt⟩).val := by
        simp only [facOf, isZ, thrFlag, hs, if_false, if_true, Nat.zero_mul, Nat.zero_add, Nat.one_mul]
        rw [hpmax, ← log_succ_eq_clog _ hp0pos]
        simp [modulusDigitCount]
      rw [hf]
      unfold degree Request.degree
      apply foldl_max_eq
      · intro x hx
        obtain ⟨row, hrow, rfl⟩ := List.mem_map.1 hx
        obtain ⟨sel, _, hrow⟩ := List.mem_flatMap.1 hrow
        obtain ⟨p, _, hrow⟩ := List.mem_flatMap.1 hrow
        obtain ⟨e, _, hrow⟩ := List.mem_flatMap.1 hrow
        obtain ⟨off, _, rfl⟩ := List.mem_map.1 hrow
        exact Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.log_mono_right (hmax p)))
      · obtain ⟨s0, hs0⟩ := List.exists_mem_of_length_pos (show 0 < (Packets.thrSelectionList a r).length by
          rw [← RowsInit.Count.thrSelOf_list a r four L tg]; omega)
        obtain ⟨e0, he0⟩ := List.exists_mem_of_length_pos (seedList_pos (thresholdFourfoldOccurrences r)
          (CyclicChoice.live (thresholdFourfoldOccurrences r) L) (CloseoutFinalC10ThresholdRows.listDenominator a r tg))
        exact List.mem_map.2 ⟨_, List.mem_flatMap.2 ⟨s0, hs0, List.mem_flatMap.2 ⟨_, List.mem_ofFn.2 ⟨⟨_, hlt⟩, rfl⟩,
          List.mem_flatMap.2 ⟨e0, he0, List.mem_map.2 ⟨⟨0, hp0pos⟩, List.mem_finRange _, rfl⟩⟩⟩⟩, rfl⟩

end
end NearCubicWires.PacketsKeys.Degree

