import Proof.Packets.ScalarCounterSeed
import Proof.Packets.DescendingWindowPrepare
import Proof.MachineModel.UWalkUnary

/-! Actual zero-head seed operations for the window bank. Every variable
length is read from a resident count or reserve tape; no scalar or template
is installed by a configuration equality. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open SignedSortKey
noncomputable section

def source (R n : Nat) := ZeroPadding.pad R (CompareMachine.word n)
def rawData (R n : Nat) (out : List Bool) : Fin 3→List Bool :=
  ![source R n,ZeroPadding.pad R out,List.replicate (R+3) false]
def raw := UWalkUnary.machine false false

theorem raw_run (R n : Nat) (hn : n≤R+1) :
    Step raw (2*n+6) (fun _=>0) (rawData R n []) (fun _=>0)
      (rawData R n (List.replicate n true)) := by
  obtain ⟨r,hr,ht,hh,hs⟩:=UWalkUnary.ready false false R n
  have base : Step raw (2*n+6) (fun _=>0) (UWalkUnary.input R n) (fun _=>0) (UWalkUnary.result false false R n) :=
    ⟨r,hr,funext hh,ht,hs⟩
  have h:=base.pad (![0,R,R+3] : Fin 3→Nat)
  convert h using 1 <;> first | rfl |
    (funext i;fin_cases i <;>simp [rawData,source,UWalkUnary.input,UWalkUnary.result,
      UWalkUnary.source,UWalkUnary.output,UWalkUnary.lead,ZeroPadding.pad_zero,ZeroPadding.pad,
      Rewind.Workspace.pad_zeros,Nat.max_eq_left (show n+2≤R+3 by omega)] <;> omega)

def copyData (R : Nat) (src dst : List Bool) : Fin 4→List Bool :=
  ![src,dst,List.replicate R true,List.replicate (R+3) false]
def copy := RecoveryBoundedTapeCopy.machine

theorem copy_run (R : Nat) (src : List Bool) (hs : src.length≤R) :
    Step copy (2*R+4) (fun _=>0) (copyData R src (List.replicate R false)) (fun _=>0)
      (copyData R src (ZeroPadding.pad R src)) := by
  have h:=(Step.of_ready (CloseoutRowsMetadataCopy.copy_ready src R hs)).pad (![0,0,0,R+3] : Fin 4→Nat)
  convert h using 1 <;> first | rfl |
    (funext i;fin_cases i <;>simp [copyData,CloseoutRowsMetadataCopy.input,CloseoutRowsMetadataCopy.output,
      ZeroPadding.pad_zero,Rewind.Workspace.pad_zeros,Nat.max_eq_left (show R+1≤R+3 by omega)])

def firstSlot : Fin 1→Fin 3 := ![0]
def up := RecoveryFocus.machine firstSlot (Completion.PhysicalDriverMoves.machine 1 .right)
def down := RecoveryFocus.machine firstSlot (Completion.PhysicalDriverMoves.machine 1 .left)
def scalarZero := Composition.machine up (Composition.machine ScalarCounterSeed.machine down)
def scalarData (R u : Nat) (out : List Bool) : Fin 3→List Bool :=
  ![source R u,ZeroPadding.pad R out,List.replicate (R+3) false]
def scalarHeads : Fin 3→Nat := ![1,0,0]

theorem scalar_moves (R u : Nat) (out : List Bool) :
    Step up 1 (fun _=>0) (scalarData R u out) scalarHeads (scalarData R u out) ∧
    Step down 1 scalarHeads (scalarData R u out) (fun _=>0) (scalarData R u out) := by
  constructor
  · apply PhysicalFocusBoundary.focus
      (Completion.PhysicalDriverMoves.run .right (fun _ : Fin 1=>0) (fun _=>source R u))
      firstSlot (by decide) (fun _=>0) scalarHeads (scalarData R u out) (scalarData R u out)
    · intro i;fin_cases i;rfl
    · intro i;fin_cases i;rfl
    · intro i;fin_cases i;rfl
    · intro i;fin_cases i;rfl
    · intro i away;fin_cases i <;>first | exact ⟨rfl,rfl⟩ | exact False.elim (away 0 rfl)
  · apply PhysicalFocusBoundary.focus
      (Completion.PhysicalDriverMoves.run .left (fun _ : Fin 1=>1) (fun _=>source R u))
      firstSlot (by decide) scalarHeads (fun _=>0) (scalarData R u out) (scalarData R u out)
    · intro i;fin_cases i;rfl
    · intro i;fin_cases i;rfl
    · intro i;fin_cases i;rfl
    · intro i;fin_cases i;rfl
    · intro i away;fin_cases i <;>first | exact ⟨rfl,rfl⟩ | exact False.elim (away 0 rfl)

theorem scalar_zero_run (R u : Nat) (hu : 2*u+1≤R+3) :
    Step scalarZero (8*u+11) (fun _=>0) (scalarData R u []) (fun _=>0)
      (scalarData R u (frame (binary u 0))) := by
  have middle := (ScalarCounterSeed.run u (R+3) hu).pad (![R,R,0] : Fin 3→Nat)
  have middle' : Step ScalarCounterSeed.machine (8*u+7) scalarHeads (scalarData R u [])
      scalarHeads (scalarData R u (frame (binary u 0))) := by
    convert middle using 1 <;> first | rfl |
      (funext i;fin_cases i <;>simp [ScalarCounterSeed.data,scalarData,source,ZeroPadding.pad_zero])
  have all := (scalar_moves R u []).1.seq (middle'.seq (scalar_moves R u (frame (binary u 0))).2)
  have fuel : 1+1+((8*u+7)+1+1)=8*u+11 := by omega
  simpa only [scalarZero,fuel] using all

end
end PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
