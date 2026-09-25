import Proof.MachineModel.RuntimeShape
import Proof.SourceAssembly.SourceBundle

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.RuntimeShape
open PCJ6e421fabe2aa4155_SourceBundle
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.P1TopDown

/-- The recipe's own worker continuation at choices `d` (verbatim from `Runtime`). -/
noncomputable abbrev workerC (d : Choices) (sources : EightSources) (gamma : ℝ)
    (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) :
    SelectedAssembly.ContinuationData sources p :=
  ControllerCappedRuntime.continuation sources p (Choices.capIndex d sources gamma hg hh p+1)
    (Choices.remainingDegree d sources gamma hg hh p) (Choices.r d sources gamma hg hh p)
    (Choices.base d sources gamma hg hh p) (Choices.scratch d sources gamma hg hh p)
    (Choices.site d sources gamma hg hh p) (Choices.remainingFuel d sources gamma hg hh p)

/-- **The source's runtime obligation after R1.** At every admitted parameter tuple the
remaining fuel lies in the three paper classes at the worker's own width, with the live scale
after the table exponent and the source degree equal to the recipe's `remainingDegree`. -/
def SplitRuntime (d : Choices) : Prop :=
  ∀ (sources : EightSources) (gamma : ℝ) (hg : 0 < gamma) (hh : gamma < 1/2)
    (p : Parameters sources gamma),
    Nonempty (Split (SelectedRuntime.sigma sources)
      (SelectedRuntime.width (workerC d sources gamma hg hh p))
      (Choices.remainingDegree d sources gamma hg hh p)
      (Choices.remainingFuel d sources gamma hg hh p))

noncomputable def splitOf {d : Choices} (h : SplitRuntime d) (sources : EightSources)
    (gamma : ℝ) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) :=
  Classical.choice (h sources gamma hg hh p)

/-- The same eight physical choices; the four runtime witnesses read off the split, with
`tableDegree = 0`. -/
noncomputable def withSplit (d : Choices) (h : SplitRuntime d) : Choices :=
  ⟨d.1, d.2.1, d.2.2.1, d.2.2.2.1, d.2.2.2.2.1, d.2.2.2.2.2.1, d.2.2.2.2.2.2.1,
    d.2.2.2.2.2.2.2.1,
    fun sources gamma hg hh p => (splitOf h sources gamma hg hh p).remainingCoefficient,
    fun sources gamma hg hh p => (splitOf h sources gamma hg hh p).remainingOnset,
    fun sources gamma hg hh p => (splitOf h sources gamma hg hh p).remainingTable,
    fun _ _ _ _ _ => 0⟩

/-- **The runtime field is discharged by the split.** -/
theorem runtime_withSplit (d : Choices) (h : SplitRuntime d) : Runtime (withSplit d h) := by
  intro sources gamma hg hh p _C n hn
  exact (splitOf h sources gamma hg hh p).runtime (workerC d sources gamma hg hh p) n hn

/-- `SourceBundle.Construction` from physical choices whose fuel splits. -/
theorem construction_of_split (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws)
    (compiler : PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws)
    (tables : PCJ9eff70d512234a4c_Fixed.TableCertificate)
    (semantics : PCJ9eff70d512234a4c_Fixed.Certificate)
    (built : ∀ mask packets rows buildSource, ∃ d : Choices,
      Physical mask selector packets rows compiler tables semantics buildSource d ∧
        SplitRuntime d) :
    Construction selector compiler tables semantics := by
  intro mask packets rows buildSource
  obtain ⟨d, hphys, hsplit⟩ := built mask packets rows buildSource
  exact ⟨withSplit d hsplit, hphys, runtime_withSplit d hsplit⟩

theorem remainingSource_of_split (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws)
    (compiler : PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws)
    (tables : PCJ9eff70d512234a4c_Fixed.TableCertificate)
    (semantics : PCJ9eff70d512234a4c_Fixed.Certificate)
    (built : ∀ mask packets rows buildSource, ∃ d : Choices,
      Physical mask selector packets rows compiler tables semantics buildSource d ∧
        SplitRuntime d) :
    PCJc4297ab269d8423a_Source.RemainingSource selector compiler tables semantics :=
  assemble selector compiler tables semantics
    (construction_of_split selector compiler tables semantics built)


end NearCubicWires.RuntimeShape
