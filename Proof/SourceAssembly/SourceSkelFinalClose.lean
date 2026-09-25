import Proof.SourceAssembly.SourceSkelFinal
import Proof.SourceAssembly.SourceStepsSite
import Proof.SourceAssembly.SourceFactorSelOnsetFin

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJc4297ab269d8423a_Source
open NearCubicWires.SourceConstruction
open NearCubicWires.SourceSkeleton
open NearCubicWires.SourceSteps
namespace NearCubicWires.SourceSkeleton.Final
noncomputable section

section close
variable (selector : CyclicChoice.Laws) (compiler : Packets.CompilerLaws)

set_option hygiene false in
local notation "𝔛" => NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector
set_option hygiene false in
local notation "𝔊" => NearCubicWires.SourceFactorSel.G7W.G7Site selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector)
set_option hygiene false in
local notation "CODE" => skelFamilyR mask packets rows (FillV5.resPV5 selector mask packets rows)
  (resChoiceX_ge (restDataOf (ParamsR.gWR selector mask packets rows)) (FillV5.xRV5 selector mask packets rows))
  (ParamsV4.fPW selector 𝔛 mask packets rows)
  (refillFam3 mask packets rows (ParamsR.gWR selector mask packets rows) (FillV5.xRV5 selector mask packets rows) (FillV5.hxRV5 selector mask packets rows) _
    (FirstW.g7OfW selector 𝔛 𝔊 mask packets rows)) (FirstW.firstW selector 𝔛 𝔊 mask packets rows)

theorem res284W_le_xtraFin :
    ∀ (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
      (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma),
      NearCubicWires.SourceStart.EntryW.res284W selector mask packets rows sources gamma hg hh p ≤ 𝔛 mask packets rows sources gamma hg hh p :=
  fun mask packets rows sources gamma hg hh p =>
    (NearCubicWires.SourceFactorSel.OnsetFin.res284W_le_oFinal selector mask packets rows sources gamma hg hh p).trans
      (NearCubicWires.SourceFactorSel.OnsetFin.oFinal_le_xtraFin selector mask packets rows sources gamma hg hh p)

theorem sourceFinalTop_of
    (hsteps : ∀ (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector),
      StepsFam4 mask packets rows compiler (FillV5.resPV5 selector mask packets rows) (ParamsV4.fPW selector 𝔛 mask packets rows) (CODE)
        (ParamsV4.sfPW selector mask packets rows) (NearCubicWires.SourceStart.EntryW.EWFam selector 𝔛 mask packets rows (CODE))
        (EFSite selector 𝔛 𝔊 mask packets rows)) :
    SourceGenHoles3 selector compiler :=
  sourceFinalAt selector compiler 𝔛
    (stepsHoleSite selector compiler 𝔛 𝔊 (NearCubicWires.SourceFactorSel.OnsetFin.xtraF_le_xtraFin selector)
      (res284W_le_xtraFin selector) hsteps)

end close

end
end NearCubicWires.SourceSkeleton.Final
end

