import Proof.Packets.PacketsXWalkLiteralProducedCopies

/-! The physically prepared boundary is obtained from the actual graded master
outputs. Every copy is an ordinary run and every new tape starts empty. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralProduced
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer Completion
noncomputable section
attribute [local irreducible] WalkLiteralMasters.gradedMachine

def copiesMachine := Composition.machine (Composition.machine rawMachine templateMachine) fanoutMachine
def prepareMachine := Composition.machine copiesMachine countRaise
attribute [local irreducible] rawMachine templateMachine fanoutMachine countRaise

theorem prepare_run (C R root rank depth population S n : Nat) (mask x y code : List Bool)
    (masters : Fin 95→List Bool)
    (hp : ∀i,masters (paletteSlots i)=WalkLiteralMasters.palette C R root rank depth population mask i)
    (hk : rank+2≤R) (hx : x.length≤R) (hy : y.length≤R) :
    Step prepareMachine (6*R+22) (fun _=>0) (bank0 masters S n x y code)
      preparedHeads (prepared masters rank R S n x y code) := by
  have p2 : masters 71=UnaryTemplate.tape R := hp 2
  have p3 : masters 41=List.replicate R true := hp 3
  have p9 : masters 88=ZeroPadding.pad R (UnaryTemplate.tape rank) :=
    (hp 9).trans (CycleLiveSuccessor.pad_compare_template R rank (by omega))
  have first:=raw_run R (bank0 masters S n x y code) p2 rfl rfl
  have second:=template_run R (rawBank (bank0 masters S n x y code) R)
    (by simp [rawBank]) (by rfl) (by rfl)
  have third:=fanout_run rank R x y (templateBank (rawBank (bank0 masters S n x y code) R) R)
    hk hx hy
    (by simpa [templateBank,rawBank,bank0,Fin.addCases] using p9)
    (by rfl) (by rfl)
    (by simpa [templateBank,rawBank,bank0,Fin.addCases] using p3)
    (by rfl) (by rfl) (by rfl) (by rfl)
  have joined:=((first.seq second).seq third).seq (count_raise_run _)
  simpa only [prepareMachine,copiesMachine,prepared,
    show (2*R+6+1+(2*R+8)+1+(2*R+4))+1+1=6*R+22 by omega] using joined

def mastersMachine := TapeEmbedding.machine 338 WalkLiteralMasters.gradedMachine
def entryMachine := Composition.machine mastersMachine prepareMachine
def entryBudget (C R root population active : Nat) (mask : List Bool) :=
  WalkLiteralMasters.gradedBudget C R root population active mask+1+(6*R+22)
attribute [local irreducible] mastersMachine prepareMachine

end
end Theorem25Completion.WalkLiteralProduced
