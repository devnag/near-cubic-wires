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

/-- The entry emitter's bank word `kk < 6` is the framed record field `kk`. -/
theorem ebank_field (b : Nat) (en : Stream.Entry) (D cap : Nat) (payload : List Bool) (i : Fin 6) :
    e_bank b en D cap payload ⟨i.val, by omega⟩ =
      RepairOrdinary.frame (Stream.recordFields b en.coefficient en.count en.denominator i) := by
  fin_cases i <;> rfl

/-- Every framed record field is at most `4b+5` long (`2·(2b+2)+1` for the three coefficient fields and the zero field, `2b+1` for the
two `b`-bit fields). -/
theorem recordField_length_le (b : Nat) (en : Stream.Entry) (i : Fin 6) :
    (RepairOrdinary.frame (Stream.recordFields b en.coefficient en.count en.denominator i)).length ≤ 4*b+5 := by
  fin_cases i <;> simp [Stream.recordFields, CompetitorRationalDecision.width] <;> omega

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

/-- **On `encT kk` (`kk < 5`) the installed bank reads the emitter's word `E kk`** (`encT kk = enc kk`, off every `app` tape). -/
theorem encT_read (ph : Phase) (refill : Σ s, Machine (UR mask packets rows sources res p k r) s)
    (preF : Σ s, Machine (UR mask packets rows sources res p k r + 1) s)
    (A : Fin (UOf mask packets rows sources res p k r) → List Bool) (E : Fin 11 → List Bool) (T : Fin 6 → List Bool)
    (kk : Fin 13) (hk : kk.val < 5) :
    install (𝒞).app (install (𝒞).enc A E) T (Dims.encT (d := 𝔇) 𝒽 kk) = E ⟨kk.val, by omega⟩ := by
  have hinj : Function.Injective (𝒞).enc := by
    intro a b hab
    have hv := congrArg Fin.val hab
    have ha := a.isLt; have hb := b.isLt
    simp only [skelCodeR] at hv
    apply Fin.ext
    split_ifs at hv <;> omega
  have he : (𝒞).enc ⟨kk.val, by omega⟩ = Dims.encT (d := 𝔇) 𝒽 kk := by
    apply Fin.ext
    show (if kk.val = 5 then _ else _) = _
    rw [if_neg (by omega)]
    simp only [Dims.encT, dimsOf]
    rw [if_pos hk]
  have ha' : ∀ i, (𝒞).app i ≠ Dims.encT (d := 𝔇) 𝒽 kk := by
    intro i h
    have hv := congrArg Fin.val h
    have h81 := wordSlot_lt sources p k r (scratchOf mask packets rows sources res) ph 81
    have h90 := wordSlot_lt sources p k r (scratchOf mask packets rows sources res) ph 90
    simp only [SourceParent.Wd] at h81 h90
    change appVal mask packets rows sources res p k r ph i = _ at hv
    simp only [Dims.encT, dimsOf] at hv
    fin_cases i <;> simp [appVal] at hv <;> omega
  have e1 := install_other (𝒞).app (install (𝒞).enc A E) T _ ha'
  have m1 : install (𝒞).enc A E (Dims.encT (d := 𝔇) 𝒽 kk) = E ⟨kk.val, by omega⟩ :=
    he ▸ install_slot _ hinj A E ⟨kk.val, by omega⟩
  exact e1.trans m1

/-- **`seam3_spec`'s `henc0`, verbatim, for ANY per-call data `vd`**, from the one bound `4b+5 ≤ Rc`. -/
theorem henc0_of (ph : Phase) (refill : Σ s, Machine (UR mask packets rows sources res p k r) s)
    (preF : Σ s, Machine (UR mask packets rows sources res p k r + 1) s)
    {Atom : Type} (vd : RCFive.Source.CallValues Atom (𝒞).sourceTapes) (b Rc N : Nat) (h : 4*b+5 ≤ Rc) :
    ∀ j, j < N → ∀ (A0 : Fin (UOf mask packets rows sources res p k r) → List Bool) (kk : Fin 13),
      (kk.val < 3 ∨ kk.val = 4) →
      (install (𝒞).app (install (𝒞).enc A0
        (e_bank b ⟨vd.coefficient j, vd.total j, vd.denominator j⟩ (vd.D j) (vd.cap j)
          (ZeroPadding.pad (vd.D j) (Stream.entryWord b ⟨vd.coefficient j, vd.total j, vd.denominator j⟩))))
        (CloseoutFinalC10AppendPositioning.tapes b (vd.D j) (vd.logSize j) (vd.resetSize j)
          ⟨vd.coefficient j, vd.total j, vd.denominator j⟩
          ((vd.phasePrefix ++ vd.entries.take j) ++ [⟨vd.coefficient j, vd.total j, vd.denominator j⟩]))
        (Dims.encT (d := 𝔇) 𝒽 kk)).length ≤ Rc := by
  intro j _ A0 kk hk
  have hk5 : kk.val < 5 := by omega
  rw [encT_read mask packets rows sources res hres p k r ph refill preF A0 _ _ kk hk5]
  have hf := ebank_field b ⟨vd.coefficient j, vd.total j, vd.denominator j⟩ (vd.D j) (vd.cap j)
    (ZeroPadding.pad (vd.D j) (Stream.entryWord b ⟨vd.coefficient j, vd.total j, vd.denominator j⟩)) ⟨kk.val, by omega⟩
  rw [hf]
  exact (recordField_length_le b _ _).trans h

end code

end
end NearCubicWires.SourceSteps
end
