import Proof.Packets.BudgetDenominator
import Proof.SourceAssembly.SourceClauseChain4
import Proof.SourceAssembly.SourceStepsCode
import Proof.SourceAssembly.SourceStepsTrace
import Proof.SourceAssembly.SourceStepsViewRefute

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.Rest NearCubicWires.SourceConstruction.Bridge
open NearCubicWires.SourceSkeleton NearCubicWires.SourceParent NearCubicWires.SourcePhase
namespace NearCubicWires.SourceSteps
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

/-- The emitter's words other than the record fields `0..2, 4, 5` and the payload do not depend on the record or the payload. -/
theorem ebank_indep (b : Nat) (en en' : Stream.Entry) (D cap : Nat) (pl pl' : List Bool) (i : Fin 11)
    (hi : i.val = 3 ∨ 7 ≤ i.val) : e_bank b en D cap pl i = e_bank b en' D cap pl' i := by
  fin_cases i <;> simp only at hi <;> first | omega | rfl

/-- The appender's words other than the payload `0` do not depend on the record. -/
theorem tapes_indep (b D l rs : Nat) (en en' : Stream.Entry) (xs : List Stream.Entry) (i : Fin 6) (hi : i.val ≠ 0) :
    CloseoutFinalC10AppendPositioning.tapes b D l rs en xs i = CloseoutFinalC10AppendPositioning.tapes b D l rs en' xs i := by
  fin_cases i <;> simp only at hi <;> first | omega | rfl

/-- The record fields `0..2` read only the coefficient. -/
theorem recordFields_coef (b : Nat) (c : CompetitorValidity.Estimate) (t d : Nat) (kk : Fin 3) :
    Stream.recordFields b c t d ⟨kk.val, by omega⟩ = Stream.recordFields b c 0 0 ⟨kk.val, by omega⟩ := by
  fin_cases kk <;> rfl

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

/-- **`seam4U_spec`'s `hcovE`** for the concrete code: `encT kk = enc kk` for `kk < 5`. -/
theorem hcovE_R (ph : Phase) (refill : Σ s, Machine (UR mask packets rows sources res p k r) s)
    (preF : Σ s, Machine (UR mask packets rows sources res p k r + 1) s) :
    ∀ kk : Fin 13, (kk.val < 3 ∨ kk.val = 4) → ∃ i, (𝒞).enc i = Dims.encT (d := 𝔇) 𝒽 kk := fun kk hk =>
  ⟨⟨kk.val, by omega⟩, enc_eq_encT mask packets rows sources res hres p k r ph refill preF kk (by omega)⟩

/-- An `enc` tape equal to `encT kk` (`kk < 5`) is `enc kk`. -/
theorem enc_idx (ph : Phase) (refill : Σ s, Machine (UR mask packets rows sources res p k r) s)
    (preF : Σ s, Machine (UR mask packets rows sources res p k r + 1) s) (i : Fin 11) (kk : Fin 13) (hk : kk.val < 5)
    (h : (𝒞).enc i = Dims.encT (d := 𝔇) 𝒽 kk) : i.val = kk.val := by
  have hv := congrArg Fin.val h
  have hT := encT_val_R mask packets rows sources res p k r kk
  have hrt : 19 ≤ r_tapes (printerOf sources) := by unfold r_tapes; omega
  by_cases h5 : i.val = 5
  · have he : ((𝒞).enc i).val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 + r_tapes (printerOf sources) - 5 := by
      show (if i.val = 5 then _ else _) = _
      rw [if_pos h5]
    omega
  · rw [enc_val_R mask packets rows sources res hres p k r ph refill preF i h5, hT] at hv
    split_ifs at hv with hlt <;> omega

/-- An `app` tape equal to an `enc` tape is `app 0 = enc 6`. -/
theorem app_enc_idx (ph : Phase) (refill : Σ s, Machine (UR mask packets rows sources res p k r) s)
    (preF : Σ s, Machine (UR mask packets rows sources res p k r + 1) s) (i : Fin 11) (i' : Fin 6)
    (h : (𝒞).app i' = (𝒞).enc i) : i.val = 6 ∧ i'.val = 0 := by
  have h81 := wordSlot_lt sources p k r (scratchOf mask packets rows sources res) ph 81
  have h90 := wordSlot_lt sources p k r (scratchOf mask packets rows sources res) ph 90
  simp only [SourceParent.Wd] at h81 h90
  have hi := i.isLt
  have hrt : 19 ≤ r_tapes (printerOf sources) := by unfold r_tapes; omega
  have hv : appVal mask packets rows sources res p k r ph i' =
      (if i.val = 5 then PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 + r_tapes (printerOf sources) - 5
      else PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 + r_tapes (printerOf sources) +
        (if i.val < 5 then i.val else i.val - 1)) := congrArg Fin.val h
  fin_cases i' <;> simp [appVal] at hv ⊢ <;> split_ifs at hv <;> omega

/-- `enc 6` is `app 0` (the emitter's payload tape is the appender's payload port). -/
theorem enc6_app0 (ph : Phase) (refill : Σ s, Machine (UR mask packets rows sources res p k r) s)
    (preF : Σ s, Machine (UR mask packets rows sources res p k r + 1) s) : (𝒞).enc 6 = (𝒞).app 0 := by
  apply Fin.ext
  rw [enc_val_R mask packets rows sources res hres p k r ph refill preF 6 (by decide)]
  show _ = appVal mask packets rows sources res p k r ph 0
  simp [appVal]

/-- `enc 5` is a slot (the family's sum slot). -/
theorem enc5_slot (ph : Phase) (refill : Σ s, Machine (UR mask packets rows sources res p k r) s)
    (preF : Σ s, Machine (UR mask packets rows sources res p k r + 1) s) :
    ∃ i', (𝒞).slots i' = (𝒞).enc 5 := by
  have hrt : 19 ≤ r_tapes (printerOf sources) := by unfold r_tapes; omega
  refine ⟨⟨r_tapes (printerOf sources) - 5, by show _ < r_tapes (printerOf sources); omega⟩, Fin.ext ?_⟩
  have he : ((𝒞).enc 5).val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 + r_tapes (printerOf sources) - 5 := by
    simp [skelCodeR]
  rw [he]
  show PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 + (r_tapes (printerOf sources) - 5) = _
  omega

end code

section clause
variable (mask : MaskProducer) (selector : CyclicChoice.Laws)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (compiler : Packets.CompilerLaws)
    (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
    (code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph) (ph : Phase)
    (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (L : Nat)
    (lay : TraceData.LayoutFamily (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) selector) (deg : Nat → Nat) (V : Nat)
    (dflt : P1TopDownPaidReusable.Datum) (b Dw capw logw resetw : Nat)
    (H : Nat → Fin (code ph).sourceTapes → Nat) (A : Nat → Fin (code ph).sourceTapes → List Bool)
    (Rc familyCost refillCost firstCost counterReserve : Nat)

set_option hygiene false in
local notation "coordC" => PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits
set_option hygiene false in
local notation "tgtC" => C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)
set_option hygiene false in
local notation "modeC" => PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp
set_option hygiene false in
local notation "vdO" => clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw (oldAt coordC ph ci sources L tgtC modeC b Dw) H A Rc familyCost refillCost firstCost counterReserve

theorem coef_succ (j : Nat) (hm : j + 1 < (monomials coordC ph ci).length) :
    (vdO).coefficient (j+1) =
      CloseoutFinalC10SupplierCalls.coefficientEstimate ((monomials coordC ph ci)[j+1]).coefficient := by
  show CloseoutFinalC10SupplierCalls.coefficientEstimate
      (((TraceData.order coordC ph ci).map (fun m => m.coefficient)).getD (j+1) 0) = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hm]
  rfl

theorem encIn_coef (j : Nat) (hm : j + 1 < (monomials coordC ph ci).length) (kk : Fin 3) :
    encInOf (code ph) b vdO (j+1) ⟨kk.val, by omega⟩ =
      RepairOrdinary.frame (CloseoutRowsEstimatorCoefficients.Stream.recordFields b
        (CloseoutFinalC10SupplierCalls.coefficientEstimate ((monomials coordC ph ci)[j+1]).coefficient) 0 0 ⟨kk.val, by omega⟩) := by
  have h := ebank_field b ⟨(vdO).coefficient (j+1), (vdO).total (j+1), (vdO).denominator (j+1)⟩ ((vdO).D (j+1)) ((vdO).cap (j+1))
    ((vdO).old (j+1)) ⟨kk.val, by omega⟩
  refine h.trans ?_
  refine congrArg RepairOrdinary.frame ?_
  rw [coef_succ mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt b Dw
    capw logw resetw H A Rc familyCost refillCost firstCost counterReserve j hm]
  exact recordFields_coef b _ _ _ kk

theorem encIn_den (j : Nat) :
    encInOf (code ph) b vdO (j+1) 4 = RepairOrdinary.frame (SignedSortKey.binary b
      (PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC (j+1)) *
        PacketsGlue.RequestMeta.seedCount (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC (j+1)) *
        2 ^ (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity)) := by
  show RepairOrdinary.frame (SignedSortKey.binary b ((vdO).denominator (j+1))) = _
  rw [show (vdO).denominator (j+1) = (TraceData.fractionOf coordC ph ci sources L tgtC modeC (j+1)).2 from rfl,
    SourceBudget.denominator_at sources coordC ph ci L tgtC modeC (j+1)]
  rfl

/-- **`hvEnc` at `clauseVals`**: the emitter words `3, 7..10` are the last call's. -/
theorem encIn_keep (j : Nat) (i : Fin 11) (hi : i.val = 3 ∨ 7 ≤ i.val) :
    encInOf (code ph) b vdO (j+1) i = Bridge.encWOf b vdO j i :=
  ebank_indep b _ _ Dw capw _ _ i hi

/-- **`hvEA` at `clauseVals`**: the carried payload `old (j+1)` is the appender's payload word of call `j`. -/
theorem encIn_payload (j : Nat) :
    encInOf (code ph) b vdO (j+1) 6 = Bridge.appTOf b vdO j 0 := rfl

/-- **`hvApp` at `clauseVals`**: the appender's words other than the payload see the stream grown by call `j`'s record. -/
theorem appIn_keep (j : Nat) (hj : j < (vdO).entries.length) (i : Fin 6) (hi : i.val ≠ 0) :
    appInOf (code ph) b vdO (j+1) i = Bridge.appTOf b vdO j i := by
  have ht : (vdO).phasePrefix ++ (vdO).entries.take (j+1) =
      ((vdO).phasePrefix ++ (vdO).entries.take j) ++ [⟨(vdO).coefficient j, (vdO).total j, (vdO).denominator j⟩] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.append_assoc]
    congr 3
    exact TraceData.hentries coordC ph ci sources L tgtC modeC j hj
  show CloseoutFinalC10AppendPositioning.tapes b Dw logw resetw _ ((vdO).phasePrefix ++ (vdO).entries.take (j+1)) i = _
  rw [ht]
  exact tapes_indep b Dw logw resetw _ _ _ i hi

end clause

section seam
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources)
  (res : Nat) (hres : 19 ≤ res) {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources res p k r
set_option hygiene false in
local notation "𝒽" => UOf_le mask packets rows sources res p k r
set_option hygiene false in
local notation "𝒞" => skelCodeR mask packets rows sources res hres p k r ph (refill3 mask packets rows sources res p k r se sp e (g7F ph).2) (preFF ph)
set_option hygiene false in
local notation "codeF" => fun ph' => skelCodeR mask packets rows sources res hres p k r ph' (refill3 mask packets rows sources res p k r se sp e (g7F ph').2) (preFF ph')
set_option hygiene false in
local notation "oracleC" => C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits
set_option hygiene false in
local notation "coordC" => PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x oracleC bits
set_option hygiene false in
local notation "tgtC" => C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)
set_option hygiene false in
local notation "modeC" => PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp
set_option hygiene false in
local notation "vQ" => (req sources k (PolynomialClock.ordinaryClock k) x oracleC).arity
set_option hygiene false in
local notation "layA" => layoutAtOf sources selector coordC ph ci L tgtC modeC lay
set_option hygiene false in
local notation "factsA" => factsAtOf sources selector compiler coordC ph ci L tgtC modeC
set_option hygiene false in
local notation "vWS" => P1TopDownPaidReusableReserves.workspace (printerOf sources) V
set_option hygiene false in
local notation "vRW" => P1TopDownPaidReusableReserves.rewind (printerOf sources) V
set_option hygiene false in
local notation "vBF" => P1TopDownPaidReusableReserves.buffer V
set_option hygiene false in
local notation "vMB" => InitRun.Mb L vQ
set_option hygiene false in
local notation "vMS" => InitPost.Ms L vQ
set_option hygiene false in
local notation "vU0" => InitRun.U0 L vQ
set_option hygiene false in
local notation "vdC" => clauseVals mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site codeF ph ci L lay (degOf sources selector coordC ph ci L tgtC modeC lay) V dflt Dw capw logw resetw (oldAt coordC ph ci sources L tgtC modeC b Dw) Hd Ad Rc familyCost refillCost firstCost counterReserve

end seam

end
end NearCubicWires.SourceSteps
end
