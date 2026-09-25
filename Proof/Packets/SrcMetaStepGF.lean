import Proof.Packets.SrcMetaStep
import Proof.SourceAssembly.SourceFactorSelMetaVals

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ1fef9807c6954e94_Native
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
namespace NearCubicWires.SourceStart.MetaStepGF
open NearCubicWires.SourceSkeleton.InitS (MetaRun ResExt)
noncomputable section

variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T) {NS : Nat}
  (hh : HeadExt d eX pX gW X NS)

def metaMG (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (L u : ℕ) :=
  MetaStep.metaM pl hh (SourceFactorSel.MetaPipe.metaVals2 selector s p packets L) u

/-- Its cost. -/
def metaCostG (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (L q : ℕ) : ℕ :=
  MetaStep.metaCost (SourceFactorSel.MetaPipe.metaVals2 selector s p packets L) q

/-- Its extension width. -/
def wMG (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (L : ℕ) : ℕ :=
  191 + (SourceFactorSel.MetaPipe.metaVals2 selector s p packets L).NP

/-- **POOL-9 at POOL-10.** -/
theorem meta_stepG (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) {NR NE : Nat} (hNR19 : 19 ≤ NR) (hNR : NR ≤ 32)
    (hE : ResExt d eX pX gW X NS NE) {L cS cR q b Rc Vv CP CW CL DP DW DL : Nat} {mode : Bool} {tg : Nat}
    (u : ℕ) (hu : u + wMG selector s p packets L ≤ NE) (hR : 1 ≤ Rc)
    (hcap : CloseoutRowsEstimatorParity.Capacity.value q ≤ Rc) (hK : 2 * normalizedLiveCount q L + 1 ≤ Rc) :
    MetaRun pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg (MetaRun.MBof selector s p packets L q) u
      (metaMG pl hh selector s p packets L u) (metaCostG selector s p packets L q) (wMG selector s p packets L) :=
  MetaStep.meta_step pl hh hNR19 hNR hE (SourceFactorSel.MetaPipe.metaVals2 selector s p packets L) u hu hR hcap hK

end
end NearCubicWires.SourceStart.MetaStepGF

