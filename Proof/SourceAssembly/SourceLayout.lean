import Proof.SourceAssembly.SourceParent
import Proof.SourceAssembly.SLoadPrepared

/-! # Source layout (B2) and the forced choices (B1): one concrete `CodeFamily`.

Consumer obligation realized: `CodeFamily` / `SourceChoices`
(`source-parent-20260923/SourceParent.lean:237-283`), i.e. `RCFive.Source.SourceCode`
(`closeout-five-checks-20260921/RCFiveSourceCode.lean:27-70`) at every `(sources, p, mode, ph)`,
plus the loader's own slot premises (`source-loaders-20260922/SLoadPrepared.lean:360`
`prepared_code`, `Proof/SourceAssembly/SLoadPoolReady.lean` `pool_seed_ready`). Paper: codes and capacities are
frozen before `n x bits` (`paper.tex:4280-4290`), so every map here depends on
`(mask, packets, rows, sources, p, k, r, ph)` only. Budget: none (layout); the private region
size `prepT` is linear in the producers' own tape counts.

The body layout above the phase region is (`F := offset + 1155`, `rt := r_tapes a`, `G := F+rt+13`):

```
F .. F+rt-1          the fixed family bank `slots` (source port at F+sp, sp = P+3)
F+rt .. F+rt+12      enc/app (the consumer's own value equations)
G .. G+R1-1          the row family bank `familySlots` (descriptor aliased to F+sp)
G+R1 .. G+R1+372     the cold-cache pool (pool 34 aliased to family header 0)
G+R1+373, +374       rewind 1, 2 (rewind 0 = F+sp)
G+R1+375 .. +387     the suffix frame `slot` (slot 0 = mask output, slot 11 = packet input)
G+R1+388 .. +392+w   the mask worker (index 4 folded onto slot 0)
G+R1+394+w ..        the packet program (tape 0 → slot 11, output → family header 262)
.. +396+w+tc         the four retained request fields `ret`
.. +407+w+tc         retDrv log rawDrv rawDst rawLog s1 d1 l1 s2 d2 l2
+408+w+tc, +409      the prologue clear's driver and log (SourceClear / Scrub.entry)
+410+w+tc ..         the reserved prologue region (res tapes)
U := G + prepT,  prepT := R1+410+w+tc+res,  and U+1 = bodyTapes (the loop counter)
```
`R1 = rowTapes a pw + 1`, `w = mask.work`, `tc = packet tape count`. The printer is the paper's
Williams source `williamsOf sources` (`$W/RepairCloseoutFinalSources.lean:31`).
-/
section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceConstruction
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

theorem ne_of_val {n : Nat} {x y : Fin n} (h : x.val ≠ y.val) : x ≠ y :=
  fun e => h (congrArg Fin.val e)

/-! ## 1. The layout, on plain numbers -/

/-- The dimensions the layout reads. -/
structure Dims where
  F : Nat
  rt : Nat
  sp : Nat
  R1 : Nat
  w : Nat
  tc : Nat
  outV : Nat
  descV : Nat
  /-- The reserved prologue region (driver producer and provenance workspaces), fixed before
  `n x bits`. -/
  res : Nat
  hsp : sp < rt
  hdesc : descV < R1
  hdesc440 : 440 ≤ descV
  hout0 : outV ≠ 0
  hout : outV < tc

namespace Dims
variable (d : Dims)

def G : Nat := d.F + d.rt + 13
def prepT : Nat := d.R1 + 410 + d.w + d.tc + d.res
def U : Nat := d.G + d.prepT
def famV (j : Nat) : Nat := if j = d.descV then d.F + d.sp else d.G + j
def poolV (i : Nat) : Nat := if i = 34 then d.G else d.G + d.R1 + i
def rewV (i : Nat) : Nat := if i = 0 then d.F + d.sp else d.G + d.R1 + 372 + i
def slotV (j : Nat) : Nat := d.G + d.R1 + 375 + j
def maskV (i : Nat) : Nat := if i = 4 then d.slotV 0 else d.G + d.R1 + 388 + i
def pV (j : Nat) : Nat :=
  if j = d.outV then d.G + 262 else if j = 0 then d.slotV 11 else d.G + d.R1 + 393 + d.w + j
def retV (k : Nat) : Nat := d.G + d.R1 + 393 + d.w + d.tc + k
/-- `0 retDrv · 1 log · 2 rawDrv · 3 rawDst · 4 rawLog · 5 s1 · 6 d1 · 7 l1 · 8 s2 · 9 d2 · 10 l2 ·
11 clear driver · 12 clear log`. -/
def scrV (m : Nat) : Nat := d.G + d.R1 + 397 + d.w + d.tc + m

/-! ### the maps, into any universe `V ≥ U` -/
variable {V : Nat} (hV : d.U ≤ V)

def familySlots (j : Fin d.R1) : Fin V :=
  ⟨d.famV j.val, Nat.lt_of_lt_of_le (by
    have := j.isLt; have := d.hsp; unfold famV U G prepT; split_ifs <;> omega) hV⟩
def poolSlots (i : Fin 373) : Fin V :=
  ⟨d.poolV i.val, Nat.lt_of_lt_of_le (by
    have := i.isLt; unfold poolV U G prepT; split_ifs <;> omega) hV⟩
def rewindSlots (i : Fin 3) : Fin V :=
  ⟨d.rewV i.val, Nat.lt_of_lt_of_le (by
    have := i.isLt; have := d.hsp; unfold rewV U G prepT; split_ifs <;> omega) hV⟩
def slot (j : Fin 13) : Fin V :=
  ⟨d.slotV j.val, Nat.lt_of_lt_of_le (by have := j.isLt; unfold slotV U G prepT; omega) hV⟩
def maskSlots (i : Fin (5 + d.w)) : Fin V :=
  ⟨d.maskV i.val, Nat.lt_of_lt_of_le (by
    have := i.isLt; unfold maskV slotV U G prepT; split_ifs <;> omega) hV⟩
def pslots (j : Fin d.tc) : Fin V :=
  ⟨d.pV j.val, Nat.lt_of_lt_of_le (by
    have := j.isLt; have := d.hdesc; have := d.hdesc440
    unfold pV slotV U G prepT; split_ifs <;> omega) hV⟩
def ret (k : Fin 4) : Fin V :=
  ⟨d.retV k.val, Nat.lt_of_lt_of_le (by have := k.isLt; unfold retV U G prepT; omega) hV⟩
def scr (m : Fin 13) : Fin V :=
  ⟨d.scrV m.val, Nat.lt_of_lt_of_le (by have := m.isLt; unfold scrV U G prepT; omega) hV⟩

/-! ### injectivity and the three aliases -/

theorem familySlots_injective : Function.Injective (d.familySlots hV) := by
  intro i j h
  have hv := congrArg Fin.val h
  have hi := i.isLt; have hj := j.isLt; have := d.hsp
  simp only [familySlots, famV, G] at hv
  apply Fin.ext
  split_ifs at hv <;> omega
theorem poolSlots_injective : Function.Injective (d.poolSlots hV) := by
  intro i j h
  have hv := congrArg Fin.val h
  have hi := i.isLt; have hj := j.isLt; have := d.hdesc
  simp only [poolSlots, poolV] at hv
  apply Fin.ext
  split_ifs at hv <;> omega
theorem slot_injective : Function.Injective (d.slot hV) := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [slot, slotV] at hv
  exact Fin.ext (by omega)
theorem maskSlots_injective : Function.Injective (d.maskSlots hV) := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [maskSlots, maskV, slotV] at hv
  apply Fin.ext
  split_ifs at hv <;> omega
theorem pslots_injective : Function.Injective (d.pslots hV) := by
  intro i j h
  have hv := congrArg Fin.val h
  have hi := i.isLt; have hj := j.isLt; have := d.hdesc; have := d.hdesc440; have := d.hout
  simp only [pslots, pV, slotV] at hv
  apply Fin.ext
  split_ifs at hv <;> omega


/-! ### every slot premise of `pool_seed_ready` and `prepared_code` -/

/-- Unfold the layout values and close an interval (in)equality. -/
macro "geo" : tactic => `(tactic| (simp only [Dims.slot, Dims.maskSlots, Dims.pslots, Dims.poolSlots,
  Dims.ret, Dims.scr, Dims.familySlots, Dims.rewindSlots, Dims.slotV, Dims.maskV, Dims.pV, Dims.poolV,
  Dims.retV, Dims.scrV, Dims.famV, Dims.rewV, Dims.G]; (try split_ifs) <;> omega))

/-- The loader's geometric premises (`pool_seed_ready`), discharged once for this layout. -/
theorem seed_geometry :
    d.slot hV 0 = d.maskSlots hV ⟨4, by omega⟩ ∧
    (∀ j : Fin 13, j ≠ 0 → ∀ i, d.maskSlots hV i ≠ d.slot hV j) ∧
    (∀ j : Fin d.tc, j.val = 0 → d.pslots hV j = d.slot hV 11) ∧
    (∀ j : Fin d.tc, j.val ≠ 0 → ∀ k, d.slot hV k ≠ d.pslots hV j) ∧
    (∀ (j : Fin d.tc) (i : Fin (5 + d.w)), d.maskSlots hV i ≠ d.pslots hV j) ∧
    (∀ (i : Fin 4) (j : Fin (5 + d.w)), d.ret hV i ≠ d.maskSlots hV j) ∧
    (∀ i, d.ret hV i ≠ d.scr hV 1) ∧ (∀ j, d.scr hV 1 ≠ d.maskSlots hV j) ∧
    (∀ i, d.slot hV 1 ≠ d.ret hV i) ∧ d.slot hV 1 ≠ d.scr hV 1 ∧
    d.scr hV 0 ≠ d.slot hV 1 ∧ d.scr hV 0 ≠ d.scr hV 1 ∧
    (∀ j : Fin 13, d.slot hV j ≠ d.scr hV 2) ∧ (∀ j : Fin 13, d.slot hV j ≠ d.scr hV 3) ∧
    (∀ j : Fin 13, d.slot hV j ≠ d.scr hV 4) ∧
    (∀ i, d.maskSlots hV i ≠ d.scr hV 2) ∧ (∀ i, d.maskSlots hV i ≠ d.scr hV 3) ∧
    (∀ i, d.maskSlots hV i ≠ d.scr hV 4) ∧
    (∀ j, d.pslots hV j ≠ d.scr hV 2) ∧ (∀ j, d.pslots hV j ≠ d.scr hV 3) ∧
    (∀ j, d.pslots hV j ≠ d.scr hV 4) ∧
    d.scr hV 2 ≠ d.scr hV 3 ∧ d.scr hV 2 ≠ d.scr hV 4 ∧ d.scr hV 3 ≠ d.scr hV 4 ∧
    (∀ (j : Fin 13) (i : Fin 373), d.slot hV j ≠ d.poolSlots hV i) ∧
    (∀ (j : Fin (5 + d.w)) (i : Fin 373), d.maskSlots hV j ≠ d.poolSlots hV i) ∧
    (∀ (j : Fin d.tc) (i : Fin 373), d.pslots hV j ≠ d.poolSlots hV i) ∧
    (∀ i : Fin 373, d.poolSlots hV i ≠ d.scr hV 3) := by
  have h1 := d.hdesc; have h2 := d.hdesc440; have h3 := d.hout0; have h4 := d.hout
  refine ⟨Fin.ext (by geo), fun j hj i => ne_of_val (by
      have := i.isLt; have := j.isLt; have hj' : j.val ≠ 0 := fun e => hj (Fin.ext e); geo),
    fun j hj => Fin.ext (by have := j.isLt; geo),
    fun j hj k => ne_of_val (by have := j.isLt; have := k.isLt; geo),
    fun j i => ne_of_val (by have := j.isLt; have := i.isLt; geo),
    fun i j => ne_of_val (by have := j.isLt; have := i.isLt; geo),
    fun i => ne_of_val (by have := i.isLt; geo), fun j => ne_of_val (by have := j.isLt; geo),
    fun i => ne_of_val (by have := i.isLt; geo), ne_of_val (by geo),
    ne_of_val (by geo), ne_of_val (by geo),
    fun j => ne_of_val (by have := j.isLt; geo), fun j => ne_of_val (by have := j.isLt; geo),
    fun j => ne_of_val (by have := j.isLt; geo),
    fun i => ne_of_val (by have := i.isLt; geo), fun i => ne_of_val (by have := i.isLt; geo),
    fun i => ne_of_val (by have := i.isLt; geo),
    fun j => ne_of_val (by have := j.isLt; geo), fun j => ne_of_val (by have := j.isLt; geo),
    fun j => ne_of_val (by have := j.isLt; geo),
    ne_of_val (by geo), ne_of_val (by geo), ne_of_val (by geo),
    fun j i => ne_of_val (by have := j.isLt; have := i.isLt; geo),
    fun j i => ne_of_val (by have := j.isLt; have := i.isLt; geo),
    fun j i => ne_of_val (by have := j.isLt; have := i.isLt; geo),
    fun i => ne_of_val (by have := i.isLt; geo)⟩

/-- The setup-loader and rewind premises of `prepared_code`, for any two family ports. -/
theorem prepared_geometry (req caps : Fin d.R1) :
    (∀ j, d.familySlots hV j ≠ d.rewindSlots hV 1) ∧ (∀ j, d.familySlots hV j ≠ d.rewindSlots hV 2) ∧
    (∀ i, d.poolSlots hV i ≠ d.rewindSlots hV 1) ∧ (∀ i, d.poolSlots hV i ≠ d.rewindSlots hV 2) ∧
    d.scr hV 5 ≠ d.scr hV 6 ∧ d.scr hV 5 ≠ d.familySlots hV req ∧ d.scr hV 5 ≠ d.scr hV 7 ∧
    d.scr hV 6 ≠ d.familySlots hV req ∧ d.scr hV 6 ≠ d.scr hV 7 ∧ d.familySlots hV req ≠ d.scr hV 7 ∧
    d.scr hV 8 ≠ d.scr hV 9 ∧ d.scr hV 8 ≠ d.familySlots hV caps ∧ d.scr hV 8 ≠ d.scr hV 10 ∧
    d.scr hV 9 ≠ d.familySlots hV caps ∧ d.scr hV 9 ≠ d.scr hV 10 ∧ d.familySlots hV caps ≠ d.scr hV 10 ∧
    d.familySlots hV req ≠ d.scr hV 8 ∧ d.familySlots hV req ≠ d.scr hV 9 ∧
    d.familySlots hV req ≠ d.scr hV 10 := by
  have h1 := d.hdesc; have h2 := d.hsp; have hr := req.isLt; have hc := caps.isLt
  refine ⟨fun j => ne_of_val (by have := j.isLt; geo), fun j => ne_of_val (by have := j.isLt; geo),
    fun i => ne_of_val (by have := i.isLt; geo), fun i => ne_of_val (by have := i.isLt; geo),
    ne_of_val (by geo), ne_of_val (by geo), ne_of_val (by geo), ne_of_val (by geo),
    ne_of_val (by geo), ne_of_val (by geo), ne_of_val (by geo), ne_of_val (by geo),
    ne_of_val (by geo), ne_of_val (by geo), ne_of_val (by geo), ne_of_val (by geo),
    ne_of_val (by geo), ne_of_val (by geo), ne_of_val (by geo)⟩

end Dims

/-! ## 2. The dimensions of the actual producers -/

/-- The paper's Williams printer. -/
abbrev printerOf (sources : EightSources) : WilliamsAlgorithm := williamsOf sources

/-- The cycle's private region size: linear in the producers' own tape counts, plus the
reserved prologue region `res`. -/
def prepTOf (mask : MaskProducer) {selector : CyclicChoice.Laws}
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources) (res : Nat) : Nat :=
  (rowTapes (printerOf sources) (rows (decompositionOf sources) (printerOf sources)).privateWork + 1) +
    410 + mask.work + (packets (decompositionOf sources)).ordinary.program.tapeCount + res

/-- **Forced B1: `scratch`.** `SourceCode._hsize` fixes it as `r_tapes a + 14 + prepT`. -/
def scratchOf (mask : MaskProducer) {selector : CyclicChoice.Laws}
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources) (res : Nat) : Nat :=
  r_tapes (printerOf sources) + 14 + prepTOf mask packets rows sources res

def dimsOf (mask : MaskProducer) {selector : CyclicChoice.Laws}
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources) (res : Nat)
    {gamma : Real} (p : Parameters sources gamma) (k r : Nat) : Dims where
  F := PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155
  rt := r_tapes (printerOf sources)
  sp := P1TopDownPaidPayload.tapes (printerOf sources) + 1 + 2
  R1 := rowTapes (printerOf sources) (rows (decompositionOf sources) (printerOf sources)).privateWork + 1
  w := mask.work
  tc := (packets (decompositionOf sources)).ordinary.program.tapeCount
  outV := (packets (decompositionOf sources)).ordinary.program.outputTape.val
  descV := 440 + P1TopDownPaidPayload.tapes (printerOf sources)
  res := res
  hsp := by simp only [r_tapes]; omega
  hdesc := by simp only [rowTapes, rowWork, PCJ38fbfed565f64139_Ready.tapes]; omega
  hdesc440 := by omega
  hout0 := (packets (decompositionOf sources)).ordinary.program.outputFresh
  hout := (packets (decompositionOf sources)).ordinary.program.outputTape.isLt

theorem dims_U (mask : MaskProducer) {selector : CyclicChoice.Laws}
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources) (res : Nat)
    {gamma : Real} (p : Parameters sources gamma) (k r : Nat) :
    (dimsOf mask packets rows sources res p k r).U + 1 =
      ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res) := by
  have ht := WorkspaceSelectedEntryReady.old_size sources p k
  simp only [Dims.U, Dims.G, Dims.prepT, dimsOf, scratchOf, prepTOf,
    ControllerSelectedContinuation.bodyTapes, ControllerSelectedContinuation.extra,
    PCJda54a286946142d3_BranchPhases.offset]
  omega

/-- A phase word slot lies below the family base `offset + 1155`. -/
theorem wordSlot_lt (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k r scratch : Nat) (ph : Phase) (i : Fin 278) :
    (SourceParent.Wd sources p k r scratch ph i).val < PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 := by
  have hi := i.isLt
  simp only [SourceParent.Wd, CloseoutFinalC10RetainedPhaseFold.wordSlots]
  split_ifs
  · have h := C10TailSlotsUniform.widthSlotT_range ph 0
    simp only [CloseoutFinalC10RetainedPhaseFold.tailSlots]; split_ifs <;> omega
  · have h := C10TailSlotsUniform.widthSlotT_range ph 1
    simp only [CloseoutFinalC10RetainedPhaseFold.tailSlots]; split_ifs <;> omega
  · have hp := (C10TailUniformSlots.phaseIndex ph).isLt
    dsimp only [CloseoutFinalC10RetainedPhaseFold.phaseBank]
    split
    · have := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
      simp only; omega
    · simp only
      have e : (C10TailUniformSlots.phaseIndex ph).val - 1 ≤ 1 := by omega
      have e2 : ((C10TailUniformSlots.phaseIndex ph).val - 1) * 278 ≤ 278 := by
        calc ((C10TailUniformSlots.phaseIndex ph).val - 1) * 278 ≤ 1 * 278 := Nat.mul_le_mul_right _ e
          _ = 278 := by omega
      omega

end
end NearCubicWires.SourceConstruction
end
