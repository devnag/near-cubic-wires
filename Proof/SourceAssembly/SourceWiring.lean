import Proof.SourceAssembly.SourceCycle

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

namespace Dims
variable (d : Dims)

/-- The start of the reserved region. -/
def B : Nat := d.G + d.R1 + 410 + d.w + d.tc
def rw2V (i : Nat) : Nat := if i = 0 then d.F + d.sp else 277 + i
def csV (k : Nat) : Nat :=
  if k = 3 then d.G + (d.R1 - 1) else if k = 1 then d.B + 13 else if k = 2 then d.B + 14
  else if k = 0 then d.B else d.B + (k - 3)
def drvV (k : Nat) : Nat :=
  if k = 3 then d.B + 1 else if k = 5 then d.G + (d.R1 - 1) else if k = 6 then d.B + 2
  else if k = 0 then d.B + 15 else if k = 1 then d.B + 16 else if k = 2 then d.B + 17 else d.B + 18

/-- The extra facts this placement needs. -/
structure Ext : Prop where
  hF : 285 < d.F
  hres : 19 ≤ d.res
  hlast : d.descV + 1 < d.R1

variable {d} (e : d.Ext) {V : Nat} (hV : d.U ≤ V)

def rewind2Slots (i : Fin 3) : Fin V :=
  ⟨d.rw2V i.val, Nat.lt_of_lt_of_le (by
    have := i.isLt; have := d.hsp; have := e.hF; unfold rw2V U G prepT; split_ifs <;> omega) hV⟩
def csSlots (k : Fin 16) : Fin V :=
  ⟨d.csV k.val, Nat.lt_of_lt_of_le (by
    have := k.isLt; have := e.hres; have := e.hlast; unfold csV B U G prepT; split_ifs <;> omega) hV⟩
def drvSlots (k : Fin 7) : Fin V :=
  ⟨d.drvV k.val, Nat.lt_of_lt_of_le (by
    have := k.isLt; have := e.hres; have := e.hlast; unfold drvV B U G prepT; split_ifs <;> omega) hV⟩
def natSlots (i : Fin d.rt) : Fin V :=
  ⟨d.F + i.val, Nat.lt_of_lt_of_le (by have := i.isLt; unfold U G prepT; omega) hV⟩
def lenTape : Fin V := ⟨d.B, Nat.lt_of_lt_of_le (by have := e.hres; unfold B U G prepT; omega) hV⟩
/-- E6's query copy (below `F`, outside SP's `Region`). -/
def queryCopy : Fin V := ⟨284, Nat.lt_of_lt_of_le (by have := e.hF; unfold U G prepT; omega) hV⟩

end Dims

/-- Unfold every layout value and close an interval (in)equality. -/
macro "wgeo" : tactic => `(tactic| (simp only [Dims.slot, Dims.maskSlots, Dims.pslots, Dims.poolSlots,
  Dims.ret, Dims.scr, Dims.familySlots, Dims.rewind2Slots, Dims.csSlots, Dims.drvSlots, Dims.natSlots,
  Dims.lenTape, Dims.slotV, Dims.maskV, Dims.pV, Dims.poolV, Dims.retV, Dims.scrV, Dims.famV, Dims.rw2V,
  Dims.csV, Dims.drvV, Dims.B, Dims.G, Fin.val_mk] at * <;> (try split_ifs at *) <;> omega))

namespace Dims
variable {d : Dims} (e : d.Ext) {V : Nat} (hV : d.U ≤ V)

/-- Setup: every family tape other than the two aliased ones is outside the seed loader. -/
theorem outside_family (i : Fin d.R1) (h0 : i.val ≠ 0) (h262 : i.val ≠ 262) :
    SourceRequest.Outside (d.slot hV) (d.maskSlots hV) (d.pslots hV) (d.poolSlots hV) (d.familySlots hV i) := by
  have h1 := d.hdesc; have h2 := d.hdesc440; have h3 := d.hout; have h4 := d.hsp; have hi := i.isLt
  refine ⟨fun j => ne_of_val ?_, fun j => ne_of_val ?_, fun j => ne_of_val ?_, fun j => ne_of_val ?_⟩ <;>
    have := j.isLt <;> wgeo

theorem family_zero (i : Fin d.R1) (hi : i.val = 0) : d.familySlots hV i = d.poolSlots hV 34 := by
  have h2 := d.hdesc440
  exact Fin.ext (by wgeo)

theorem family_262 (i : Fin d.R1) (hi : i.val = 262) (j : Fin d.tc) (hj : j.val = d.outV) :
    d.familySlots hV i = d.pslots hV j := by
  have h2 := d.hdesc440; have h3 := d.hout0
  exact Fin.ext (by wgeo)

theorem family_ne_rewind (j : Fin d.R1) (i : Fin 3) (hi : i.val ≠ 0) :
    d.familySlots hV j ≠ rewind2Slots e hV i := by
  have h1 := e.hF; have h2 := i.isLt; have h3 := j.isLt; have h4 := d.hsp
  exact ne_of_val (by wgeo)

theorem outside_rewind (i : Fin 3) (hi : i.val ≠ 0) :
    SourceRequest.Outside (d.slot hV) (d.maskSlots hV) (d.pslots hV) (d.poolSlots hV) (rewind2Slots e hV i) := by
  have h1 := e.hF; have h2 := i.isLt; have h3 := d.hdesc; have h4 := d.hout
  refine ⟨fun j => ne_of_val ?_, fun j => ne_of_val ?_, fun j => ne_of_val ?_, fun j => ne_of_val ?_⟩ <;>
    have := j.isLt <;> wgeo

theorem outside_scr (m : Fin 13) (hm : 5 ≤ m.val) :
    SourceRequest.Outside (d.slot hV) (d.maskSlots hV) (d.pslots hV) (d.poolSlots hV) (d.scr hV m) := by
  have h1 := d.hdesc; have h2 := d.hdesc440; have h3 := d.hout; have hmm := m.isLt
  refine ⟨fun j => ne_of_val ?_, fun j => ne_of_val ?_, fun j => ne_of_val ?_, fun j => ne_of_val ?_⟩ <;>
    have := j.isLt <;> wgeo

/-- A reserved-region tape is `Free`. -/
theorem free_res (x : Fin V) (hx : d.B ≤ x.val) :
    Cycle.Free (d.slot hV) (d.maskSlots hV) (d.pslots hV) (d.poolSlots hV) (d.familySlots hV)
      (rewind2Slots e hV) x := by
  have h1 := d.hdesc; have h2 := d.hdesc440; have h3 := d.hout; have h4 := d.hsp; have h5 := e.hF
  refine ⟨⟨fun j => ne_of_val ?_, fun j => ne_of_val ?_, fun j => ne_of_val ?_, fun j => ne_of_val ?_⟩,
    fun j => ne_of_val ?_, fun j => ne_of_val ?_⟩ <;> have := j.isLt <;> wgeo

/-- A native family tape off the source port is `Free`. -/
theorem free_nat (i : Fin d.rt) (hi : i.val ≠ d.sp) :
    Cycle.Free (d.slot hV) (d.maskSlots hV) (d.pslots hV) (d.poolSlots hV) (d.familySlots hV)
      (rewind2Slots e hV) (natSlots hV i) := by
  have h1 := d.hdesc; have h2 := d.hdesc440; have h3 := d.hout; have h4 := d.hsp; have h5 := e.hF
  have h6 := i.isLt
  refine ⟨⟨fun j => ne_of_val ?_, fun j => ne_of_val ?_, fun j => ne_of_val ?_, fun j => ne_of_val ?_⟩,
    fun j => ne_of_val ?_, fun j => ne_of_val ?_⟩ <;> have := j.isLt <;> wgeo

theorem cs_injective : Function.Injective (csSlots e hV) := by
  intro a b h
  have hv := congrArg Fin.val h
  clear h
  have := a.isLt; have := b.isLt; have := e.hres; have := e.hlast
  simp only [csSlots, csV, B, G, Fin.val_mk] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem drv_injective : Function.Injective (drvSlots e hV) := by
  intro a b h
  have hv := congrArg Fin.val h
  clear h
  have := a.isLt; have := b.isLt; have := e.hres; have := e.hlast
  simp only [drvSlots, drvV, B, G, Fin.val_mk] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem nat_injective : Function.Injective (natSlots (d := d) hV) := fun a b h => Fin.ext (by
  have hv := congrArg Fin.val h; wgeo)

theorem nat_ne_drv (i : Fin d.rt) (k : Fin 7) : natSlots hV i ≠ drvSlots e hV k := by
  have := i.isLt; have := k.isLt; have := e.hlast
  exact ne_of_val (by wgeo)

theorem nat_ne_cs (i : Fin d.rt) (k : Fin 16) : natSlots hV i ≠ csSlots e hV k := by
  have := i.isLt; have := k.isLt; have := e.hlast
  exact ne_of_val (by wgeo)

theorem drv_ne_cs (c : Fin 7) (hc : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 4) (k : Fin 16) :
    drvSlots e hV c ≠ csSlots e hV k := by
  have := k.isLt; have := e.hlast; have := e.hres
  rcases hc with h | h | h | h <;> subst h <;> exact ne_of_val (by wgeo)

theorem drv_res (c : Fin 7) (hc : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 4) : d.B ≤ (drvSlots e hV c).val := by
  rcases hc with h | h | h | h <;> subst h <;> wgeo

theorem cs_res (k : Fin 16) (hk : k.val ≠ 3) : d.B ≤ (csSlots e hV k).val := by
  have := k.isLt; wgeo

theorem drv_links : drvSlots e hV 3 = csSlots e hV 4 ∧ drvSlots e hV 5 = csSlots e hV 3 ∧
    drvSlots e hV 6 = csSlots e hV 5 :=
  ⟨Fin.ext (by wgeo), Fin.ext (by wgeo), Fin.ext (by wgeo)⟩

theorem cs_zero : csSlots e hV 0 = lenTape e hV := Fin.ext (by wgeo)

theorem cs_three (j : Fin d.R1) (hj : j.val = d.R1 - 1) : csSlots e hV 3 = d.familySlots hV j := by
  have := e.hlast
  exact Fin.ext (by wgeo)

theorem rewind_ne_last (i : Fin 3) (j : Fin d.R1) (hj : j.val = d.R1 - 1) :
    rewind2Slots e hV i ≠ d.familySlots hV j := by
  have := e.hlast; have := e.hF; have := i.isLt; have := d.hsp
  exact ne_of_val (by wgeo)

theorem nat_src : natSlots hV ⟨d.sp, d.hsp⟩ = rewind2Slots e hV 0 := Fin.ext (by wgeo)

end Dims

section concrete
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources) (res : Nat)
  {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

theorem dims_ext (hres : 19 ≤ res) : (dimsOf mask packets rows sources res p k r).Ext where
  hF := by simp only [dimsOf]; omega
  hres := hres
  hlast := by simp only [dimsOf, rowTapes, rowWork, PCJ38fbfed565f64139_Ready.tapes]; omega

theorem sourcePort_eq :
    PCJ515eaa990d75455b_FamilyInit.sourcePort (printerOf sources) =
      ⟨(dimsOf mask packets rows sources res p k r).sp, (dimsOf mask packets rows sources res p k r).hsp⟩ := by
  apply Fin.ext
  simp only [PCJ515eaa990d75455b_FamilyInit.sourcePort, dimsOf]

/-- **The wiring, discharged on the concrete layout.** -/
theorem wiring (hres : 19 ≤ res) {V : Nat} (hV : (dimsOf mask packets rows sources res p k r).U ≤ V) :
    Cycle.Wiring mask (packets (decompositionOf sources))
      (rows (decompositionOf sources) (printerOf sources))
      ((dimsOf mask packets rows sources res p k r).maskSlots hV)
      ((dimsOf mask packets rows sources res p k r).pslots hV)
      ((dimsOf mask packets rows sources res p k r).slot hV)
      ((dimsOf mask packets rows sources res p k r).ret hV)
      ((dimsOf mask packets rows sources res p k r).scr hV 0)
      ((dimsOf mask packets rows sources res p k r).scr hV 1)
      ((dimsOf mask packets rows sources res p k r).familySlots hV)
      ((dimsOf mask packets rows sources res p k r).poolSlots hV)
      (Dims.rewind2Slots (dims_ext mask packets rows sources res p k r hres) hV)
      ((dimsOf mask packets rows sources res p k r).scr hV 5)
      ((dimsOf mask packets rows sources res p k r).scr hV 6)
      ((dimsOf mask packets rows sources res p k r).scr hV 7)
      ((dimsOf mask packets rows sources res p k r).scr hV 8)
      ((dimsOf mask packets rows sources res p k r).scr hV 9)
      ((dimsOf mask packets rows sources res p k r).scr hV 10)
      (Dims.lenTape (dims_ext mask packets rows sources res p k r hres) hV)
      (Dims.csSlots (dims_ext mask packets rows sources res p k r hres) hV)
      (Dims.natSlots hV)
      (Dims.drvSlots (dims_ext mask packets rows sources res p k r hres) hV) := by
  have e := dims_ext mask packets rows sources res p k r hres
  obtain ⟨hmsk, hoffm, hslot0, hoffp, hmp, hrm, hrl, hlm, hdr, hdl, hDd, hDl, -, -, -, -, -, -, -, -, -,
    -, -, -, hpS, hpM, hpP, -⟩ := (dimsOf mask packets rows sources res p k r).seed_geometry hV
  obtain ⟨-, -, -, -, e1, e2, e3, e4, e5, e6, k1, k2, k3, k4, k5, k6, m1, m2, m4⟩ :=
    (dimsOf mask packets rows sources res p k r).prepared_geometry hV
      (rowRequestPort (printerOf sources) (rows (decompositionOf sources) (printerOf sources)).privateWork)
      (rowCapsPort (printerOf sources) (rows (decompositionOf sources) (printerOf sources)).privateWork)
  have hsrc := sourcePort_eq mask packets rows sources res p k r
  have hlastV : (Fin.last (rowTapes (printerOf sources)
      (rows (decompositionOf sources) (printerOf sources)).privateWork)).val =
      (dimsOf mask packets rows sources res p k r).R1 - 1 := (Nat.add_sub_cancel _ 1).symm
  exact
    { hinj := (dimsOf mask packets rows sources res p k r).slot_injective hV
      hmsk := hmsk, hoffm := hoffm, hslot0 := hslot0, hoffp := hoffp, hmp := hmp, hrm := hrm
      hrl := hrl, hlm := hlm, hdr := hdr, hdl := hdl, hDd := hDd, hDl := hDl
      hpS := hpS, hpM := hpM, hpP := hpP
      hpool0 := fun i hi => Dims.family_zero hV i hi
      hraw262 := fun i hi => Dims.family_262 hV i hi _ rfl
      hfamOut := fun i h0 h262 => Dims.outside_family hV i h0 h262
      os1 := Dims.outside_scr hV 5 (by decide), od1 := Dims.outside_scr hV 6 (by decide)
      ol1 := Dims.outside_scr hV 7 (by decide), os2 := Dims.outside_scr hV 8 (by decide)
      od2 := Dims.outside_scr hV 9 (by decide), ol2 := Dims.outside_scr hV 10 (by decide)
      e1 := e1, e2 := e2, e3 := e3, e4 := e4, e5 := e5, e6 := e6
      k1 := k1, k2 := k2, k3 := k3, k4 := k4, k5 := k5, k6 := k6, m1 := m1, m2 := m2, m4 := m4
      h1 := fun j => Dims.family_ne_rewind e hV j 1 (by decide)
      h2 := fun j => Dims.family_ne_rewind e hV j 2 (by decide)
      or1 := Dims.outside_rewind e hV 1 (by decide)
      or2 := Dims.outside_rewind e hV 2 (by decide)
      hcs := Dims.cs_injective e hV
      hjoin := Finish.joinSlots_injective _ _ _ (Dims.nat_injective hV) (Dims.drv_injective e hV)
        (Dims.nat_ne_drv e hV)
      hd3 := (Dims.drv_links e hV).1
      hd5 := (Dims.drv_links e hV).2.1
      hd6 := (Dims.drv_links e hV).2.2
      hfam_cs := Dims.nat_ne_cs e hV
      hdu_cs := Dims.drv_ne_cs e hV
      hlen := Dims.cs_zero e hV
      hcnt := Dims.cs_three e hV _ hlastV
      hcntRew := fun i => Dims.rewind_ne_last e hV i _ hlastV
      hsrcp := by rw [hsrc]; exact Dims.nat_src e hV
      fcs := fun c hc => by
        by_cases h0 : c.val = 3
        · exact absurd h0 hc
        · exact Dims.free_res e hV _ (Dims.cs_res e hV c h0)
      fdrv := fun c hc => Dims.free_res e hV _ (Dims.drv_res e hV c hc)
      ffam := fun i hi => Dims.free_nat e hV i (by
        intro h; apply hi; rw [hsrc]; exact Fin.ext h) }

end concrete

end
end NearCubicWires.SourceConstruction
end
