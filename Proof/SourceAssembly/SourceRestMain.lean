import Proof.SourceAssembly.SourceRestRun

/-! # `rest_run`: the refill prologue after the clear, on the concrete layout

**Consumer.** `SourceRefillStep.refill_step`'s `hrest` and `SourceCyclePad.cycle_prepared_pad`'s `hM`/`res`/`hM2`;
the record bank's `enc 0..2, 4` (`SourceTrace._hfields`). See `SourceRestRun` for the statement's shape.

**Paper.** As `SourceRest`. **Budget**: `cursorCost j + 1 + (g7cost (j+1) + 1 + backCost …)`.
-/
section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
namespace NearCubicWires.SourceConstruction.Rest
noncomputable section

/-- The cursor's dock `[curT, cur, scratch]`. -/
def curSlots {d : SourceConstruction.Dims} {eX pX gW : Nat} (e : d.RestExt eX pX gW) {V : Nat} (hV : d.U ≤ V) :
    Fin 3 → Fin V :=
  ![d.rsT e hV 2, d.pcT e hV ⟨64, by unfold restPc; omega⟩, d.pcT e hV ⟨65, by unfold restPc; omega⟩]

theorem curSlots_injective {d : SourceConstruction.Dims} {eX pX gW : Nat} (e : d.RestExt eX pX gW) {V : Nat}
    (hV : d.U ≤ V) : Function.Injective (curSlots e hV) := by
  intro a b h
  have hv := congrArg Fin.val h
  fin_cases a <;> fin_cases b <;> simp [curSlots, SourceConstruction.Dims.pcT, SourceConstruction.Dims.rsT,
    restPc] at hv ⊢ <;> omega

def restMachine {a : DecompositionAlgorithm} {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage a vE) (sp : PacketsGlue.RequestMeta.UnaryStage a vP)
    {d : SourceConstruction.Dims} {gW : Nat} (e : d.RestExt se.extra sp.extra gW) {V : Nat} (hV : d.U ≤ V)
    {s7 : Nat} (g7M : Machine V s7) :=
  Composition.machine (RecoveryFocus.machine (curSlots e hV) cursorMachine)
    (Composition.machine g7M (backMachine se sp e hV))

theorem notOut_pcv (d : SourceConstruction.Dims) (eX pX gW i : Nat)
    (hi : i < 61 ∨ (64 ≤ i ∧ i < 70) ∨ (71 ≤ i ∧ i < 71 + eX + pX)) :
    ¬ OutV d eX pX gW (d.B + 19 + i) := by
  have vB : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  have vp : d.pscr = d.R1 + 408 + d.w + d.tc := rfl
  unfold OutV restPc; omega
theorem isOut_coef (d : SourceConstruction.Dims) (eX pX gW i : Nat) (hi : 61 ≤ i ∧ i < 64) :
    OutV d eX pX gW (d.B + 19 + i) := by
  unfold OutV; omega
theorem notOut_enc (d : SourceConstruction.Dims) (eX pX gW i : Nat) (hi : i < 13) :
    ¬ OutV d eX pX gW (d.F + d.rt + i) := by
  have vG : d.G = d.F + d.rt + 13 := rfl
  have vB : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  unfold OutV restPc; omega
theorem notOut_rs (d : SourceConstruction.Dims) (eX pX gW i : Nat) :
    ¬ OutV d eX pX gW (d.B + 19 + restPc eX pX gW + i) := by
  have vB : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  have vp : d.pscr = d.R1 + 408 + d.w + d.tc := rfl
  unfold OutV restPc; omega
theorem notOut_scr (d : SourceConstruction.Dims) (eX pX gW m : Nat) (hm : 11 ≤ m) (hm2 : m ≤ 12) :
    ¬ OutV d eX pX gW (d.G + d.R1 + 397 + d.w + d.tc + m) := by
  have vB : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  have vp : d.pscr = d.R1 + 408 + d.w + d.tc := rfl
  unfold OutV restPc; omega
theorem notOut_cs1 (d : SourceConstruction.Dims) (eX pX gW : Nat) : ¬ OutV d eX pX gW (d.B + 13) := by
  have vB : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  have vp : d.pscr = d.R1 + 408 + d.w + d.tc := rfl
  unfold OutV restPc; omega

section concrete
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources) (res : Nat)
  {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources res p k r

end concrete

end
end NearCubicWires.SourceConstruction.Rest
end
