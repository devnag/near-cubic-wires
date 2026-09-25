import Proof.Packets.PacketsWalk
import Proof.Packets.PacketsSetup

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsGlue.BitWord
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch

/-- Copy the first cell of tape 0 to tape 1 (one step). -/
def machine : Machine 2 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q b => if q.val = 0 then some ⟨1, ![none, some (b 0)], ![.stay, .stay]⟩ else none

theorem run (x : ℕ) : Step machine 1 (fun _ => 0) ![List.replicate x true, []] (fun _ => 0)
    ![List.replicate x true, [decide (0 < x)]] := by
  have hs : step machine ⟨0, fun _ => 0, ![List.replicate x true, []]⟩ =
      some ⟨1, fun _ => 0, ![List.replicate x true, [decide (0 < x)]]⟩ := by
    simp only [step, machine, Configuration.scanned]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i
      fin_cases i
      · rfl
      · cases x <;> rfl
  exact NatAt.Timed.toStep (Timed.single (p := machine) rfl hs) rfl rfl

end NearCubicWires.PacketsGlue.BitWord

namespace NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.BlockPlatform
open NearCubicWires.SupplierWalkBridge
open RowsInit.Count (thrSelOf)
noncomputable section

/-- Transport a word stage along a pointwise equality of words. -/
def WordStage.ofEq {a : DecompositionAlgorithm} {v w : Request → List Bool} (s : WordStage a v)
    (h : ∀ r, v r = w r) : WordStage a w where
  extra := s.extra
  states := s.states
  machine := s.machine
  cost := s.cost
  coefficient := s.coefficient
  degree := s.degree
  cost_le := s.cost_le
  run := fun r => by
    obtain ⟨H', A', hs, h0, hh0, h1, hh1⟩ := s.run r
    exact ⟨H', A', hs, h0, hh0, by rw [h1, h r], hh1⟩

/-- `1^x ↦ [decide (0 < x)]`. -/
def bitWordMap : WordMap (fun x => [decide (0 < x)]) where
  extra := 0
  states := 2
  machine := BitWord.machine
  cost := fun _ => 1
  run := by
    intro x
    refine ⟨_, _, (BitWord.run x).congr_in rfl ?_, rfl, rfl⟩
    funext i; fin_cases i <;> rfl

def symBit : Request → Bool
  | .sym _ _ _ _ => true
  | _ => false

/-- **The mode bit word** `[symBit r]`. -/
def modeWordStage (a : DecompositionAlgorithm) : WordStage a (fun r => [symBit r]) :=
  (((notThrStage a).pairP (liveFlagStage a) mulMap2 8 2 mul_cost).thenWordP bitWordMap 1 0
    (by intro x; simp [bitWordMap])).ofEq
    (by intro r; cases r <;> simp [symBit, thrFlag, liveFlag])

end
end NearCubicWires.PacketsGlue.RequestMeta

