import Proof.SourceAssembly.SourceStepsEntryInv4
import Proof.SourceAssembly.SourceStepsNextHole
import Proof.SourceAssembly.SourceStepsNums
import Proof.SourceAssembly.SourceStepsParts1

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

section clause
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources)
  (res : Nat) (hres : 19 ≤ res) {gamma : Real} (p : Parameters sources gamma) (k r : Nat)
  (ph : Phase)
  (se : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) (PacketsGlue.RequestMeta.seedCount (decompositionOf sources)))
  (sp : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) (PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources))) {gW : Nat}
  (e : (dimsOf mask packets rows sources res p k r).RestExt3 se.extra sp.extra gW)
  (g7F : Phase → Σ s, Machine (UOf mask packets rows sources res p k r) s)
  (preFF : Phase → Σ s, Machine (UOf mask packets rows sources res p k r + 1) s)
  (compiler : Packets.CompilerLaws) (den : Nat) (hden : 0 < den) (n : Nat) (x : BitInput n) (bits : List Bool)
  (hp : P1Independent.CappedLegalAdmission.passed sources p
    (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
    (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
  (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res)) states)
  (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)))
  (L Rc Rk : Nat)
  (lay : TraceData.LayoutFamily (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp) selector)
  (K : Fin (UOf mask packets rows sources res p k r) → Prop)
  (K0 : Fin (UOf mask packets rows sources res p k r) → List Bool)
  (KH0 : Fin (UOf mask packets rows sources res p k r) → Nat)
  (V : Nat) (dflt : P1TopDownPaidReusable.Datum)
  (Hd : Nat → Fin (UOf mask packets rows sources res p k r) → Nat) (Ad : Nat → Fin (UOf mask packets rows sources res p k r) → List Bool)
  (familyCost firstCost counterReserve refillCost : Nat)
  (A : Fin (ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res)) → List Bool)
  (H : Fin (ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res)) → Nat)
  (H' : Fin (UOf mask packets rows sources res p k r + 1) → Nat) (A' : Fin (UOf mask packets rows sources res p k r + 1) → List Bool)

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
local notation "bS" => C10PartsSchedule.entryWidthSchedule sources k r n
set_option hygiene false in
local notation "w0S" => (A ((𝒞).whole (Dims.encT (d := 𝔇) 𝒽 5).castSucc)).take (InitRun.D0 bS)
set_option hygiene false in
local notation "oldS" => fun j => if j = 0 then w0S else oldAt coordC ph ci sources L tgtC modeC bS (InitRun.D0 bS) j
set_option hygiene false in
local notation "vdS" => clauseVals mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site codeF ph ci L lay (degOf sources selector coordC ph ci L tgtC modeC lay) V dflt (InitRun.D0 bS) (InitRun.cap0 bS) (CloseoutFinalC10AppendWorkspaceInit.capacity bS) (CloseoutFinalC10AppendWorkspaceInit.capacity bS) oldS Hd Ad Rc familyCost refillCost firstCost counterReserve
set_option hygiene false in
local notation "NS" => (vdS).entries.length
set_option hygiene false in
local notation "Inv5S" => Inv5 mask packets rows sources res hres p k r ph se sp e g7F preFF compiler den hden n x bits hp site ci L Rc Rk bS lay K K0 KH0 V dflt (InitRun.D0 bS) (InitRun.cap0 bS) (CloseoutFinalC10AppendWorkspaceInit.capacity bS) (CloseoutFinalC10AppendWorkspaceInit.capacity bS) Hd Ad oldS familyCost firstCost counterReserve refillCost Rc Rc Rc Rc NS H' A'
set_option hygiene false in
local notation "H0cS" => (fun y : Fin (UOf mask packets rows sources res p k r) => H' y.castSucc)
set_option hygiene false in
local notation "A0cS" => chainView 𝒞 bS vdS NS 0 (fun y : Fin (UOf mask packets rows sources res p k r) => A' y.castSucc)
set_option hygiene false in
local notation "CSP" => ChainStartP mask packets rows sources res hres p k r ph se sp e g7F preFF compiler den hden n x bits hp site ci L Rc Rk bS lay K K0 KH0 V dflt Hd Ad familyCost firstCost counterReserve refillCost Rc Rc Rc Rc w0S A H H' A'
set_option hygiene false in
local notation "BTS" => ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res)
set_option hygiene false in
local notation "OFFS" => PCJda54a286946142d3_BranchPhases.offset sources p k r
set_option hygiene false in
local notation "CACHES" => PCJda54a286946142d3_BranchPhases.cache sources p k r (scratchOf mask packets rows sources res) modeC
set_option hygiene false in
local notation "RF" => refill3 mask packets rows sources res p k r se sp e (g7F ph).2

/-- **The chain invariant at the chain start** (`Inv5` at call `0`), from the first cycle's exit facts (`ChainStartP` (2), (3)). -/
theorem h0S (hS : CSP) : Inv5S 0 H0cS A0cS := by
  unfold ChainStartP at hS
  obtain ⟨-, -, -, hR, -, -, h3, -, -⟩ := hS
  unfold Inv5
  exact ⟨hR, fun _ _ _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, fun h => absurd h (lt_irrefl 0)⟩, fun _ => rfl, h3,
    fun _ h => absurd h (lt_irrefl 0)⟩

/-- The site code's `encT kk`, one tape up, is the counter universe's `encT kk`. -/
theorem encT_castSucc (kk : Fin 13) :
    (Dims.encT (d := 𝔇) 𝒽 kk).castSucc = Dims.encT (d := 𝔇) (UOf_le_succ mask packets rows sources res p k r) kk :=
  Fin.ext (by simp only [Fin.val_castSucc, Dims.encT])

/-- The `encT` index of `enc i`. -/
theorem encIdx_lt (i : Fin 11) : (if i.val < 5 then i.val else i.val - 1) < 13 := by
  have := i.isLt; split_ifs <;> omega

/-- `r_tapes` of the code is at least `19`. -/
theorem rt_ge : 19 ≤ r_tapes (𝒞).a := by
  show 19 ≤ r_tapes (printerOf sources)
  unfold r_tapes; omega

/-- The code's `enc 5` is a slot. -/
theorem enc5_slotC (i : Fin 11) (h5 : i.val = 5) :
    (𝒞).slots ⟨r_tapes (𝒞).a - 5, Nat.sub_lt (lt_of_lt_of_le (by decide) (rt_ge mask packets rows sources res hres p k r ph se sp e g7F preFF)) (by decide)⟩ = (𝒞).enc i := by
  apply Fin.ext
  rw [(𝒞)._hs, (𝒞)._he, if_pos h5]
  have := rt_ge mask packets rows sources res hres p k r ph se sp e g7F preFF
  simp only
  omega

/-- The code's `enc i` (`i ≠ 5`) is `encT (i or i-1)`. -/
theorem enc_encT (i : Fin 11) (h5 : i.val ≠ 5) :
    (𝒞).enc i = Dims.encT (d := 𝔇) 𝒽 ⟨if i.val < 5 then i.val else i.val - 1, encIdx_lt i⟩ := by
  apply Fin.ext
  rw [enc_val_R mask packets rows sources res hres p k r ph RF (preFF ph) i h5, encT_val_R mask packets rows sources res p k r]

/-- **E13, `enc` heads**: at every call, off the slots, the `enc` heads are `0` (`Inv5` conjunct 4 + `ChainStartP` (5)). -/
theorem hEncH_S (hS : CSP) : ∀ j, j ≤ NS → ∀ (Hc : Fin (𝒞).sourceTapes → Nat) (Ac : Fin (𝒞).sourceTapes → List Bool), Inv5S j Hc Ac →
    ∀ i, (∀ i', (𝒞).slots i' ≠ (𝒞).enc i) → Hc ((𝒞).enc i) = 0 := by
  intro j _ Hc Ac hI i hi
  unfold Inv5 at hI
  obtain ⟨-, -, -, h4, -, -⟩ := hI
  unfold ChainStartP at hS
  obtain ⟨-, -, -, -, -, -, -, -, ⟨hEH, -, -, -⟩⟩ := hS
  by_cases h5 : i.val = 5
  · exact absurd (enc5_slotC mask packets rows sources res hres p k r ph se sp e g7F preFF i h5) (hi _)
  · rw [enc_encT mask packets rows sources res hres p k r ph se sp e g7F preFF i h5, h4]
    show H' (Dims.encT (d := 𝔇) 𝒽 _).castSucc = 0
    rw [encT_castSucc]
    exact hEH _

/-- **E14, the words**: `Inv5` conjunct 5. -/
theorem hWords_S : ∀ j, j < NS → ∀ (Hc : Fin (𝒞).sourceTapes → Nat) (Ac : Fin (𝒞).sourceTapes → List Bool), Inv5S j Hc Ac →
    (∀ i, (∀ i', (𝒞).slots i' ≠ (𝒞).enc i) → Ac ((𝒞).enc i) = encInOf 𝒞 bS vdS j i) ∧
    (∀ i, (∀ i', (𝒞).slots i' ≠ (𝒞).app i) → (∀ i', (𝒞).enc i' ≠ (𝒞).app i) → Ac ((𝒞).app i) = appInOf 𝒞 bS vdS j i) := by
  intro j hj Hc Ac hI
  unfold Inv5 at hI
  exact hI.2.2.2.2.1 hj

/-- The phase word slots avoid the rewind block `278..284`. -/
theorem wd_off_block (j : Fin 278) (h4 : j.val ≠ 274) (h5 : j.val ≠ 275) :
    (Wd sources p k r (scratchOf mask packets rows sources res) ph j).val < 278 ∨
      284 < (Wd sources p k r (scratchOf mask packets rows sources res) ph j).val := by
  have h300 := offset_ge_300 sources p k r
  have hj := j.isLt
  rcases wd_val mask packets rows sources res p k r ph j h4 h5 with h | h <;> omega

/-- The code's `app` tapes below `F` are `Free`, off the cache and the rewind block, and are `Wd ph 81/90` on the body. -/
theorem app_low_facts (i : Fin 6) (hlo : ((𝒞).app i).val < (𝔇).F) :
    Cycle.Free ((𝔇).slot 𝒽) ((𝔇).maskSlots 𝒽) ((𝔇).pslots 𝒽) ((𝔇).poolSlots 𝒽) ((𝔇).familySlots 𝒽)
      (Dims.rewind2Slots e.ext2.ext1.ext 𝒽) ((𝒞).app i) ∧
    (∀ i', ((𝒞).app i).val ≠ (CACHES i').val) ∧
    (((𝒞).app i).val < 278 ∨ 284 < ((𝒞).app i).val) ∧
    ((𝒞).whole ((𝒞).app i).castSucc = Wd sources p k r (scratchOf mask packets rows sources res) ph 81 ∨
      (𝒞).whole ((𝒞).app i).castSucc = Wd sources p k r (scratchOf mask packets rows sources res) ph 90) := by
  have hv := app_low mask packets rows sources res hres p k r ph se sp e g7F preFF i hlo
  refine ⟨app_free_R mask packets rows sources res hres p k r ph RF (preFF ph) e.ext2.ext1.ext i hlo, ?_, ?_, ?_⟩
  · intro i' h
    rcases hv with hv | hv
    · exact SourcePhase.app_not_cache (sources := sources) (p := p) (k := k) (r := r)
        (scratch := scratchOf mask packets rows sources res) (mode := modeC) (ph := ph) 81 (Or.inl rfl) i' (Fin.ext (hv.symm.trans h))
    · exact SourcePhase.app_not_cache (sources := sources) (p := p) (k := k) (r := r)
        (scratch := scratchOf mask packets rows sources res) (mode := modeC) (ph := ph) 90 (Or.inr rfl) i' (Fin.ext (hv.symm.trans h))
  · rcases hv with hv | hv
    · rw [hv]; exact wd_off_block mask packets rows sources res p k r ph 81 (by decide) (by decide)
    · rw [hv]; exact wd_off_block mask packets rows sources res p k r ph 90 (by decide) (by decide)
  · rcases hv with hv | hv
    · exact Or.inl (Fin.ext (by show ((𝒞).app i).castSucc.val = _; rw [Fin.val_castSucc]; exact hv))
    · exact Or.inr (Fin.ext (by show ((𝒞).app i).castSucc.val = _; rw [Fin.val_castSucc]; exact hv))

/-- The code's `app` tapes at or above `F` sit at `F + rt + 5/10/11/12` (`app 0/2/4/5`). -/
theorem app_high2 (i : Fin 6) (hhi : (𝔇).F ≤ ((𝒞).app i).val) :
    (i.val = 0 ∧ ((𝒞).app i).val = OFFS + 1155 + r_tapes (printerOf sources) + 5) ∨
    (i.val = 2 ∧ ((𝒞).app i).val = OFFS + 1155 + r_tapes (printerOf sources) + 10) ∨
    (i.val = 4 ∧ ((𝒞).app i).val = OFFS + 1155 + r_tapes (printerOf sources) + 11) ∨
    (i.val = 5 ∧ ((𝒞).app i).val = OFFS + 1155 + r_tapes (printerOf sources) + 12) := by
  have h81 := wordSlot_lt sources p k r (scratchOf mask packets rows sources res) ph 81
  have h90 := wordSlot_lt sources p k r (scratchOf mask packets rows sources res) ph 90
  fin_cases i
  · exact Or.inl ⟨rfl, rfl⟩
  · exact absurd (lt_of_lt_of_le h81 hhi) (lt_irrefl _)
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact absurd (lt_of_lt_of_le h90 hhi) (lt_irrefl _)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))

/-- The code's `app` tapes at or above `F` are `encT` tapes. -/
theorem app_encT (i : Fin 6) (hhi : (𝔇).F ≤ ((𝒞).app i).val) : ∃ kk : Fin 13, (𝒞).app i = Dims.encT (d := 𝔇) 𝒽 kk := by
  rcases app_high2 mask packets rows sources res hres p k r ph se sp e g7F preFF i hhi with ⟨-, hv⟩ | ⟨-, hv⟩ | ⟨-, hv⟩ | ⟨-, hv⟩
  · exact ⟨5, Fin.ext (by rw [encT_val_R mask packets rows sources res p k r]; exact hv)⟩
  · exact ⟨10, Fin.ext (by rw [encT_val_R mask packets rows sources res p k r]; exact hv)⟩
  · exact ⟨11, Fin.ext (by rw [encT_val_R mask packets rows sources res p k r]; exact hv)⟩
  · exact ⟨12, Fin.ext (by rw [encT_val_R mask packets rows sources res p k r]; exact hv)⟩

/-- **E13, `app` heads**: at every call the `app` heads are `0` (`Inv5` conjuncts 3, 4; `ChainStartP` (4), (5); the entry's phase-word heads). -/
theorem hAppH_S (hS : CSP) (hW81 : H (Wd sources p k r (scratchOf mask packets rows sources res) ph 81) = 0)
    (hW90 : H (Wd sources p k r (scratchOf mask packets rows sources res) ph 90) = 0) :
    ∀ j, j ≤ NS → ∀ (Hc : Fin (𝒞).sourceTapes → Nat) (Ac : Fin (𝒞).sourceTapes → List Bool), Inv5S j Hc Ac →
      ∀ i, Hc ((𝒞).app i) = 0 := by
  intro j _ Hc Ac hI i
  unfold Inv5 at hI
  obtain ⟨-, -, h3, h4, -, -⟩ := hI
  unfold ChainStartP at hS
  obtain ⟨-, -, -, -, -, -, -, h4S, ⟨hEH, -, -, -⟩⟩ := hS
  rcases happP_R mask packets rows sources res hres p k r ph RF (preFF ph) i with hlo | ⟨hhi, -⟩
  · rw [(h3 i hlo).1]
    obtain ⟨hf, hnc, hb, hw⟩ := app_low_facts mask packets rows sources res hres p k r ph se sp e g7F preFF den hden n x bits hp i hlo
    show H' ((𝒞).app i).castSucc = 0
    rw [(h4S _ hlo hf hnc hb).2]
    rcases hw with hw | hw
    · rw [hw]; exact hW81
    · rw [hw]; exact hW90
  · obtain ⟨kk, hk⟩ := app_encT mask packets rows sources res hres p k r ph se sp e g7F preFF i hhi
    rw [hk, h4]
    show H' (Dims.encT (d := 𝔇) 𝒽 kk).castSucc = 0
    rw [encT_castSucc]
    exact hEH kk

/-- The code's `app` tapes are never slots. -/
theorem hAppNS_S : ∀ i i', (𝒞).slots i' ≠ (𝒞).app i := by
  intro i i' h
  have hv := congrArg Fin.val h
  rw [(𝒞)._hs] at hv
  have hi' := i'.isLt
  have ha : r_tapes (𝒞).a = r_tapes (printerOf sources) := rfl
  have hF : (𝔇).F = OFFS + 1155 := rfl
  rcases happP_R mask packets rows sources res hres p k r ph RF (preFF ph) i with hlo | ⟨hhi, -⟩
  · omega
  · rcases app_high2 mask packets rows sources res hres p k r ph se sp e g7F preFF i hhi with ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ <;> omega

/-- The only `enc` slot is the family's sum slot `5`. -/
theorem hEncS_S : ∀ i i', (𝒞).slots i' = (𝒞).enc i → i = 5 ∧ i' = P1TopDownPaidFamilySum.sumSlots (f_raw (𝒞).a) 5 := by
  intro i i' h
  have hv := congrArg Fin.val h
  rw [(𝒞)._hs, (𝒞)._he] at hv
  have hi' := i'.isLt
  have hs5 : (P1TopDownPaidFamilySum.sumSlots (f_raw (𝒞).a) 5).val + 5 = r_tapes (𝒞).a := rfl
  split_ifs at hv with h5
  · exact ⟨Fin.ext h5, Fin.ext (by omega)⟩
  all_goals (exfalso; omega)

/-- `app 0 = enc 6` is the only `enc`/`app` coincidence. -/
theorem hAppE_S : ∀ i i', (𝒞).enc i' = (𝒞).app i → i' = 6 ∧ i = 0 := by
  intro i i' h
  have hv := congrArg Fin.val h
  have hE := (hencP_R mask packets rows sources res hres p k r ph RF (preFF ph) i').1
  have hF : (𝔇).F = OFFS + 1155 := rfl
  have hhi : (𝔇).F ≤ ((𝒞).app i).val := hv ▸ hE
  have hA := app_high2 mask packets rows sources res hres p k r ph se sp e g7F preFF i hhi
  rw [(𝒞)._he] at hv
  have ha : r_tapes (𝒞).a = r_tapes (printerOf sources) := rfl
  have hi' := i'.isLt
  have hrt := rt_ge mask packets rows sources res hres p k r ph se sp e g7F preFF
  have hc : i'.val = 6 ∧ i.val = 0 := by
    split_ifs at hv <;> omega
  exact ⟨Fin.ext hc.1, Fin.ext hc.2⟩

set_option hygiene false in
local notation "VVS" => chainVals 𝒞 bS vdS seam H0cS A0cS
set_option hygiene false in
local notation "INV" => Nat → (Fin (UOf mask packets rows sources res p k r) → Nat) → (Fin (UOf mask packets rows sources res p k r) → List Bool) → Prop

/-- **THE CLAUSE TRACE** (census D1, E13, E14, E16): `trace5` at the concrete code, the chain `seam` (any invariant refining `Inv5`) from
the first cycle's exit. -/
theorem trace_S (hS : CSP) (hW81 : H (Wd sources p k r (scratchOf mask packets rows sources res) ph 81) = 0)
    (hW90 : H (Wd sources p k r (scratchOf mask packets rows sources res) ph 90) = 0) (siteFuel : Nat)
    (Inv : INV) (hInv : ∀ j Hc Ac, Inv j Hc Ac → Inv5S j Hc Ac)
    (seam : SeamSpec NS (fun _ => 0) (𝒞).slots (inTOf 𝒞 bS vdS) Inv (goodOf 𝒞 bS vdS)) (h0 : Inv 0 H0cS A0cS)
    (TN : TraceNums mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site codeF ph ci L lay
      (degOf sources selector coordC ph ci L tgtC modeC lay) V dflt (InitRun.D0 bS) (InitRun.cap0 bS) (CloseoutFinalC10AppendWorkspaceInit.capacity bS)
      (CloseoutFinalC10AppendWorkspaceInit.capacity bS) oldS Hd Ad Rc familyCost refillCost firstCost counterReserve H A siteFuel NS VVS)
    (hsite : site modeC ph = SourceParent.siteOfCode 𝒞) :
    RCFive.Source.SourceTrace mask selector packets rows compiler sources p k den r (scratchOf mask packets rows sources res) (PolynomialClock.ordinaryClock k) n x oracleC bits
      site modeC ph ci H (finalH mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site codeF ph H VVS)
      A (finalA mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site codeF ph ci A VVS)
      bS siteFuel 𝒞 VVS := by
  have hEH := hEncH_S mask packets rows sources res hres p k r ph se sp e g7F preFF compiler den hden n x bits hp site ci L Rc Rk lay K K0 KH0 V dflt Hd Ad
    familyCost firstCost counterReserve refillCost A H H' A' hS
  have hAH := hAppH_S mask packets rows sources res hres p k r ph se sp e g7F preFF compiler den hden n x bits hp site ci L Rc Rk lay K K0 KH0 V dflt Hd Ad
    familyCost firstCost counterReserve refillCost A H H' A' hS hW81 hW90
  have hWo := hWords_S mask packets rows sources res hres p k r ph se sp e g7F preFF compiler den hden n x bits hp site ci L Rc Rk lay K K0 KH0 V dflt Hd Ad
    familyCost firstCost counterReserve refillCost A H' A'
  unfold ChainStartP at hS
  obtain ⟨h1, h2a, h2b, -, h2d, h2e, -, -, -⟩ := hS
  rw [queriedAt_fin sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp ci A] at h1
  exact trace5 mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site codeF ph ci L lay
    (degOf sources selector coordC ph ci L tgtC modeC lay) V dflt (InitRun.D0 bS) (InitRun.cap0 bS) (CloseoutFinalC10AppendWorkspaceInit.capacity bS)
    (CloseoutFinalC10AppendWorkspaceInit.capacity bS) oldS Hd Ad Rc familyCost refillCost firstCost counterReserve H A siteFuel NS Inv seam H0cS A0cS
    h0 (Nat.le_refl _) h2a h2b _ rfl TN.hdeg TN.hC TN.hD TN.hcap TN.hlog TN.h_hw TN.h_hfit TN.h_hold TN.h_hr
    (fun j hj Hc Ac hI => hEH j hj Hc Ac (hInv j Hc Ac hI)) (fun j hj Hc Ac hI => hAH j hj Hc Ac (hInv j Hc Ac hI))
    (fun j hj Hc Ac hI => hWo j hj Hc Ac (hInv j Hc Ac hI))
    (hAppNS_S mask packets rows sources res hres p k r ph se sp e g7F preFF)
    (hEncS_S mask packets rows sources res hres p k r ph se sp e g7F preFF)
    (hAppE_S mask packets rows sources res hres p k r ph se sp e g7F preFF)
    (enc_injective_R mask packets rows sources res hres p k r ph RF (preFF ph)) TN.h_hcost
    (hfirst_of_start mask selector packets rows sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp codeF ph ci H A VVS H' A' h1 h2d h2e)
    ((hcode_of_siteOfCode 𝒞).trans hsite.symm) TN.hbudget

/-- **The chain's end** satisfies `Inv5`. -/
theorem end_S (Inv : INV) (hInv : ∀ j Hc Ac, Inv j Hc Ac → Inv5S j Hc Ac)
    (seam : SeamSpec NS (fun _ => 0) (𝒞).slots (inTOf 𝒞 bS vdS) Inv (goodOf 𝒞 bS vdS)) (h0 : Inv 0 H0cS A0cS) :
    Inv5S NS ((VVS).H NS) ((VVS).A NS) :=
  hInv _ _ _ (callChain_inv seam H0cS A0cS h0 NS le_rfl)

/-- (chain start) off the slots, `enc` and `app`, the start is the first cycle's exit. -/
theorem start_other_S (z : Fin (UOf mask packets rows sources res p k r)) (hs : ∀ i, (𝒞).slots i ≠ z) (he : ∀ i, (𝒞).enc i ≠ z)
    (happ : ∀ i, (𝒞).app i ≠ z) : A0cS z = A' z.castSucc := by
  by_cases hN : 0 < NS
  · rw [chainView_lt 𝒞 bS vdS NS 0 hN]
    exact viewOf_other 𝒞 bS vdS 0 _ z hs he happ
  · rw [chainView_ge 𝒞 bS vdS NS 0 (by omega)]
    exact install_other _ _ _ z hs

/-- The chain at a call index equal to `0` is its start. -/
theorem chain_zero_S (Inv : INV) (seam : SeamSpec NS (fun _ => 0) (𝒞).slots (inTOf 𝒞 bS vdS) Inv (goodOf 𝒞 bS vdS)) :
    ∀ j, j = 0 → ((VVS).H j, (VVS).A j) = (H0cS, A0cS) := by
  rintro j rfl
  rfl

/-- The code's `app` tapes below `F` are `app 1`, `app 3`. -/
theorem app_lt_F (i : Fin 6) (hlo : ((𝒞).app i).val < (𝔇).F) : i = 1 ∨ i = 3 := by
  have hF : (𝔇).F = OFFS + 1155 := rfl
  have h0 : ∀ t : Nat, ¬ (OFFS + 1155 + r_tapes (printerOf sources) + t < (𝔇).F) := fun t h =>
    absurd h (Nat.not_lt.mpr (Nat.le_trans (Nat.le_add_right (OFFS + 1155) (r_tapes (printerOf sources))) (Nat.le_add_right _ t)))
  fin_cases i
  · exact absurd hlo (h0 5)
  · exact Or.inl rfl
  · exact absurd hlo (h0 10)
  · exact Or.inr rfl
  · exact absurd hlo (h0 11)
  · exact absurd hlo (h0 12)

set_option hygiene false in
local notation "ES" => (⟨𝔇, se.extra, sp.extra, gW, eR, eV, X, (𝒞).sourceTapes + 1, (𝒞).whole, pl, e, Rc, Rk, Ce, Kc, K0e, KH0e, cnt, c15, q284, c17, c18,
  bS, vQ, vMB, vMS, vWS, vRW, vBF, vU0⟩ : EntrySite (ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res)))

theorem parts_S (hS : CSP) {eR eV X : Nat}
    (pl : Phase → InitRun.Place 𝔇 se.extra sp.extra gW eR eV X ((𝒞).sourceTapes + 1)) (Ce : Nat)
    (Kc : Fin ((𝒞).sourceTapes + 1) → Prop) (K0e : Phase → Nat → Fin ((𝒞).sourceTapes + 1) → List Bool) (KH0e : Fin ((𝒞).sourceTapes + 1) → Nat)
    (cnt c15 q284 c17 c18 : Fin ((𝒞).sourceTapes + 1))
    (EF : Phase → Fin (NC sources k (PolynomialClock.ordinaryClock k) x oracleC) → List Stream.Entry)
    (hI : entryInvAt4 sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp ES EF ph ci.val A H)
    (siteFuel : Nat) (Inv : INV) (hInv : ∀ j Hc Ac, Inv j Hc Ac → Inv5S j Hc Ac)
    (seam : SeamSpec NS (fun _ => 0) (𝒞).slots (inTOf 𝒞 bS vdS) Inv (goodOf 𝒞 bS vdS)) (h0 : Inv 0 H0cS A0cS)
    (TN : TraceNums mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site codeF ph ci L lay
      (degOf sources selector coordC ph ci L tgtC modeC lay) V dflt (InitRun.D0 bS) (InitRun.cap0 bS) (CloseoutFinalC10AppendWorkspaceInit.capacity bS)
      (CloseoutFinalC10AppendWorkspaceInit.capacity bS) oldS Hd Ad Rc familyCost refillCost firstCost counterReserve H A siteFuel NS VVS)
    (hsite : site modeC ph = SourceParent.siteOfCode 𝒞)
    (hK : KeepHole mask selector packets rows sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp codeF ph ci H A VVS)
    (hC : CacheHole mask selector packets rows sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp codeF ph ci VVS)
    (hH : HappHole mask selector packets rows sources p k r (scratchOf mask packets rows sources res) n x bits codeF ph A VVS)
    (hN : NextHole mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site codeF ph ci H A VVS
      𝔇 pl e 𝒽 Rc Rk Ce Kc K0e KH0e cnt c15 q284 c17 c18 bS vQ vMB vMS vWS vRW vBF vU0 EF K K0 KH0 (fuelOf 𝒞 bS vdS NS))
    -- the site's facts
    (hcR : counterReserve = Rc) (hNR : NS + 2 ≤ Rc) (hwR : (CompareMachine.word NS).length ≤ Rc) (hcnt : cnt = Fin.last (𝒞).sourceTapes)
    (hcacheK : ∀ (i : Fin 19) (s : Fin (𝒞).sourceTapes), (𝒞).whole s.castSucc = CACHES i →
      K s ∧ K0 s = CD sources k (PolynomialClock.ordinaryClock k) x oracleC ci.val i ∧ KH0 s = 0)
    (hKc1 : ∀ y : Fin (𝒞).sourceTapes, Kc y.castSucc → K y ∧ KH0e y.castSucc = KH0 y ∧
      ((∀ i, (𝒞).whole y.castSucc ≠ CACHES i) → K0e ph (ci.val+1) y.castSucc = K0 y))
    (hKc2 : ∀ y (i : Fin 19), Kc y → (𝒞).whole y = CACHES i → K0e ph (ci.val+1) y = cdAt sources p k n x bits (ci.val+1) i ∧ KH0e y = 0)
    (hKlast : ¬ Kc (Fin.last (𝒞).sourceTapes))
    (h15 : (𝒞).whole c15 = CACHES 15) (h17 : (𝒞).whole c17 = CACHES 17) (h18 : (𝒞).whole c18 = CACHES 18)
    (hq284F : q284.val < (𝔇).F) (hq284c : ∀ i, (𝒞).whole q284 ≠ CACHES i)
    (hq284 : ∃ y : Fin (𝒞).sourceTapes, y.castSucc = q284 ∧ K y ∧ (K0 y).length ≤ capC sources k (PolynomialClock.ordinaryClock k) x oracleC ∧ KH0 y = 0)
    (hEF : (vdS).entries = EF ph ci) (hpre : (vdS).phasePrefix = prefixEntries (EF ph) ci.val)
    -- the chain end's `encT` words (S's seam extension)
    (henc : EncWords 𝒽 Rc bS ((VVS).H NS) ((VVS).A NS)) :
    ClauseParts mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site codeF ph ci H A siteFuel VVS
      (fun c A2 H2 => entryInvAt4 sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp ES EF ph c A2 H2) := by
  have hE := end_S mask packets rows sources res hres p k r ph se sp e g7F preFF compiler den hden n x bits hp site ci L Rc Rk lay K K0 KH0 V dflt Hd Ad
    familyCost firstCost counterReserve refillCost A H' A' Inv hInv seam h0
  unfold Inv5 at hE
  obtain ⟨hR, hKL, hAP, -, -, -⟩ := hE
  have hS' := hS
  unfold ChainStartP at hS'
  obtain ⟨-, -, -, -, -, -, -, h4S, -⟩ := hS'
  have hPW := (entryInvAt4_to3 sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp ES EF ph ci.val A H hI).2.1
  have hPW' := hPW
  unfold PhaseWords at hPW'
  obtain ⟨-, -, hW81, hW90, -⟩ := hPW'
  have hF : (𝔇).F = OFFS + 1155 := rfl
  have hkeep := hK A0cS H0cS A' H' (fun _ => rfl)
    (fun i => by rw [(𝒞)._hs]; exact Nat.le_add_right _ _)
    (fun i => (hencP_R mask packets rows sources res hres p k r ph RF (preFF ph) i).1)
    (fun i hi => app_low mask packets rows sources res hres p k r ph se sp e g7F preFF i hi)
    (fun z hz h1 h2 ha => hKL z hz (free_below e.ext2.ext1.ext 𝒽 z h1 h2 hz) ha)
    (fun i hi => (hAP i hi).1)
    (fun z hs he ha => start_other_S mask packets rows sources res hres p k r ph se sp e g7F preFF compiler den hden n x bits hp site ci L Rc lay V dflt Hd Ad
      familyCost firstCost counterReserve refillCost A A' z hs he ha)
    (fun _ => rfl)
    (fun z hz h1 h2 hnc hb => h4S z hz (free_below e.ext2.ext1.ext 𝒽 z h1 h2 hz) hnc hb)
  have happ := hH (fun _ => rfl) rfl rfl
    (fun i hi => by
      rcases app_lt_F mask packets rows sources res hres p k r ph se sp e g7F preFF i hi with h | h
      · exact Or.inl h
      · exact Or.inr h)
    (fun hpos i hi => (hAP i hi).2 hpos)
    (fun hz i hi => by
      have hc := chain_zero_S mask packets rows sources res hres p k r ph se sp e g7F preFF compiler den hden n x bits hp site ci L Rc lay V dflt Hd Ad
        familyCost firstCost counterReserve refillCost A H' A' Inv seam NS hz
      have hA0 : (VVS).A NS = A0cS := congrArg Prod.snd hc
      rw [hA0]
      obtain ⟨hf, hnc, hb, hw⟩ := app_low_facts mask packets rows sources res hres p k r ph se sp e g7F preFF den hden n x bits hp i hi
      have hv : A0cS ((𝒞).app i) = A' ((𝒞).app i).castSucc := by
        rw [chainView_ge 𝒞 bS vdS NS 0 (Nat.le_of_eq hz)]
        exact install_other _ _ _ _ (fun i' => hAppNS_S mask packets rows sources res hres p k r ph se sp e g7F preFF i i')
      rw [hv, (h4S _ hi hf hnc hb).1]
      refine queriedAt_off sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp ci.val A _ ?_
      intro i' h
      rcases hw with hw | hw
      · exact SourcePhase.app_not_cache (sources := sources) (p := p) (k := k) (r := r)
          (scratch := scratchOf mask packets rows sources res) (mode := modeC) (ph := ph) 81 (Or.inl rfl) i' (hw.symm.trans h)
      · exact SourcePhase.app_not_cache (sources := sources) (p := p) (k := k) (r := r)
          (scratch := scratchOf mask packets rows sources res) (mode := modeC) (ph := ph) 90 (Or.inr rfl) i' (hw.symm.trans h))
    (fun j hj => by
      rw [List.getElem?_eq_getElem hj]
      exact congrArg some (TraceData.hentries coordC ph ci sources L tgtC modeC j hj))
  refine ⟨trace_S mask packets rows sources res hres p k r ph se sp e g7F preFF compiler den hden n x bits hp site ci L Rc Rk lay K K0 KH0 V dflt Hd Ad
      familyCost firstCost counterReserve refillCost A H H' A' hS hW81 hW90 siteFuel Inv hInv seam h0 TN hsite,
    hkeep.1, hkeep.2, hC K K0 KH0 (fun z hz => hR.kept z hz) hcacheK, happ, ?_⟩
  exact entryInvAt4_succ sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp ES EF ph ci.val _ _
    (hN (fun _ => rfl) hF rfl hcnt rfl hcR hNR hwR hR henc hKc1 hKc2 hKlast h15 h17 h18 hq284F hq284c hq284 hPW hEF hpre hkeep.1 hkeep.2 happ)

end clause

end
end NearCubicWires.SourceSteps
end

