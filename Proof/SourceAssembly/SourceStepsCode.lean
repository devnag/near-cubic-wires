import Proof.SourceAssembly.SourceSkelCodeFacts

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.SourceConstruction NearCubicWires.SourceSkeleton
namespace NearCubicWires.SourceSteps
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

/-- Every tape below `F` other than the rewind pair `278/279` is free of the cycle's slot maps. -/
theorem free_below {d : SourceConstruction.Dims} (e : d.Ext) {V : Nat} (hV : d.U ≤ V) (x : Fin V)
    (h1 : x.val ≠ 278) (h1' : x.val ≠ 279) (h2 : x.val < d.F) :
    Cycle.Free (d.slot hV) (d.maskSlots hV) (d.pslots hV) (d.poolSlots hV) (d.familySlots hV)
      (Dims.rewind2Slots e hV) x := by
  have := d.hdesc; have := d.hdesc440; have := d.hout; have := d.hsp; have := e.hF
  refine ⟨⟨fun jj => ne_of_val ?_, fun jj => ne_of_val ?_, fun jj => ne_of_val ?_, fun jj => ne_of_val ?_⟩,
    fun jj => ne_of_val ?_, fun jj => ne_of_val ?_⟩ <;> have := jj.isLt <;> wgeo

section code
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources)
  (res : Nat) (hres : 19 ≤ res) {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources res p k r
set_option hygiene false in
local notation "𝒽" => UOf_le mask packets rows sources res p k r
set_option hygiene false in
local notation "𝒞" => skelCodeR mask packets rows sources res hres p k r ph refill preF

/-- A phase word slot other than the width slots is `i` itself or `offset + 599 + 278·(idx-1) + i`, never `278`/`279`. -/
theorem wd_val (ph : Phase) (i : Fin 278) (h4 : i.val ≠ 274) (h5 : i.val ≠ 275) :
    (SourceParent.Wd sources p k r (scratchOf mask packets rows sources res) ph i).val = i.val ∨
      (SourceParent.Wd sources p k r (scratchOf mask packets rows sources res) ph i).val =
        PCJda54a286946142d3_BranchPhases.offset sources p k r + 599 + ((C10TailUniformSlots.phaseIndex ph).val - 1) * 278 + i.val := by
  simp only [SourceParent.Wd, CloseoutFinalC10RetainedPhaseFold.wordSlots, if_neg h4, if_neg h5]
  dsimp only [CloseoutFinalC10RetainedPhaseFold.phaseBank]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem wd81_ne_wd90 (ph : Phase) :
    (SourceParent.Wd sources p k r (scratchOf mask packets rows sources res) ph 81).val ≠
      (SourceParent.Wd sources p k r (scratchOf mask packets rows sources res) ph 90).val := by
  intro h
  have hi := (CloseoutFinalC10RetainedPhaseFold.maps_injective _ _ (PCJda54a286946142d3_BranchPhases.offset_ge sources p k r)
    (PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r (scratchOf mask packets rows sources res)) ph).1 (Fin.ext h)
  exact absurd hi (by decide)

/-- **`seam3K_spec`'s `happInj`** for the concrete code. -/
theorem app_injective_R (ph : Phase) (refill : Σ s, Machine (UR mask packets rows sources res p k r) s)
    (preF : Σ s, Machine (UR mask packets rows sources res p k r + 1) s) :
    Function.Injective (𝒞).app := by
  have h81 := wordSlot_lt sources p k r (scratchOf mask packets rows sources res) ph 81
  have h90 := wordSlot_lt sources p k r (scratchOf mask packets rows sources res) ph 90
  have hne := wd81_ne_wd90 mask packets rows sources res p k r ph
  simp only [SourceParent.Wd] at h81 h90 hne
  intro a b hab
  have hv := congrArg Fin.val hab
  change appVal mask packets rows sources res p k r ph a = appVal mask packets rows sources res p k r ph b at hv
  fin_cases a <;> fin_cases b <;> simp [appVal] at hv ⊢ <;> omega

/-- **`seam3K_spec`'s `happFree`** for the concrete code: the `app` tapes below `F` (`Wd 81/90`) are `Free`. -/
theorem app_free_R (ph : Phase) (refill : Σ s, Machine (UR mask packets rows sources res p k r) s)
    (preF : Σ s, Machine (UR mask packets rows sources res p k r + 1) s) (e : (𝔇).Ext) :
    ∀ i, ((𝒞).app i).val < (𝔇).F →
      Cycle.Free ((𝔇).slot 𝒽) ((𝔇).maskSlots 𝒽) ((𝔇).pslots 𝒽) ((𝔇).poolSlots 𝒽) ((𝔇).familySlots 𝒽)
        (Dims.rewind2Slots e 𝒽) ((𝒞).app i) := by
  intro i hi
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  have w81 := wd_val mask packets rows sources res p k r ph 81 (by decide) (by decide)
  have w90 := wd_val mask packets rows sources res p k r ph 90 (by decide) (by decide)
  simp only [SourceParent.Wd] at w81 w90
  refine free_below e 𝒽 _ ?_ ?_ hi
  · change appVal mask packets rows sources res p k r ph i ≠ 278
    change appVal mask packets rows sources res p k r ph i < PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 at hi
    fin_cases i <;> simp [appVal] at hi ⊢ <;> omega
  · change appVal mask packets rows sources res p k r ph i ≠ 279
    change appVal mask packets rows sources res p k r ph i < PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 at hi
    fin_cases i <;> simp [appVal] at hi ⊢ <;> omega

/-- **`seam3E_spec`'s `hencInj`** for the concrete code. -/
theorem enc_injective_R (ph : Phase) (refill : Σ s, Machine (UR mask packets rows sources res p k r) s)
    (preF : Σ s, Machine (UR mask packets rows sources res p k r + 1) s) :
    Function.Injective (𝒞).enc := by
  intro a b hab
  have hv := congrArg Fin.val hab
  have ha := a.isLt; have hb := b.isLt
  simp only [skelCodeR] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

/-- The code's `enc i` (`i ≠ 5`) sits at `F + rt + i` (`i < 5`) or `F + rt + i - 1` (`i > 5`). -/
theorem enc_val_R (ph : Phase) (refill : Σ s, Machine (UR mask packets rows sources res p k r) s)
    (preF : Σ s, Machine (UR mask packets rows sources res p k r + 1) s) (i : Fin 11) (h5 : i.val ≠ 5) :
    ((𝒞).enc i).val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 + r_tapes (printerOf sources) +
      (if i.val < 5 then i.val else i.val - 1) := by
  show (if i.val = 5 then _ else _) = _
  rw [if_neg h5]

/-- `encT kk` sits at `F + rt + kk`. -/
theorem encT_val_R (kk : Fin 13) :
    (Dims.encT (d := 𝔇) 𝒽 kk).val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 + r_tapes (printerOf sources) + kk.val := by
  simp only [Dims.encT, dimsOf]

/-- **`seam3E_spec`'s `hcov`** for the concrete code: `encT 3 = enc 3`, `encT 5..9 = enc 6..10`, `encT 10, 11, 12 = app 2, 4, 5`. -/
theorem hcov_R (ph : Phase) (refill : Σ s, Machine (UR mask packets rows sources res p k r) s)
    (preF : Σ s, Machine (UR mask packets rows sources res p k r + 1) s) :
    ∀ kk : Fin 13, (kk.val = 3 ∨ 5 ≤ kk.val) →
      (∃ i, (𝒞).enc i = Dims.encT (d := 𝔇) 𝒽 kk) ∨ (∃ i, (𝒞).app i = Dims.encT (d := 𝔇) 𝒽 kk) := by
  intro kk hk
  have hkl := kk.isLt
  have hT := encT_val_R mask packets rows sources res p k r kk
  rcases (by omega : kk.val = 3 ∨ (5 ≤ kk.val ∧ kk.val ≤ 9) ∨ kk.val = 10 ∨ kk.val = 11 ∨ kk.val = 12) with h | h | h | h | h
  · refine Or.inl ⟨⟨3, by omega⟩, Fin.ext ?_⟩
    rw [enc_val_R mask packets rows sources res hres p k r ph refill preF ⟨3, by omega⟩ (by show (3:Nat) ≠ 5; decide), hT]
    simp only [if_pos (show (3:Nat) < 5 by decide)]
    omega
  · refine Or.inl ⟨⟨kk.val + 1, by omega⟩, Fin.ext ?_⟩
    rw [enc_val_R mask packets rows sources res hres p k r ph refill preF ⟨kk.val + 1, by omega⟩ (by show kk.val + 1 ≠ 5; omega), hT]
    simp only [if_neg (show ¬ (kk.val + 1 < 5) by omega)]
    omega
  · refine Or.inr ⟨2, Fin.ext ?_⟩
    rw [hT]
    show appVal mask packets rows sources res p k r ph 2 = _
    simp [appVal]; omega
  · refine Or.inr ⟨4, Fin.ext ?_⟩
    rw [hT]
    show appVal mask packets rows sources res p k r ph 4 = _
    simp [appVal]; omega
  · refine Or.inr ⟨5, Fin.ext ?_⟩
    rw [hT]
    show appVal mask packets rows sources res p k r ph 5 = _
    simp [appVal]; omega

end code

end
end NearCubicWires.SourceSteps
end
