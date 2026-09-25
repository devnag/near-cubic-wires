import Proof.Packets.PacketsXMajorityCompletePalette
import Proof.Packets.PhysicalPrepend
import Proof.Rows.SourceDockCore

/-! The reusable 137-tape arena: ten retained scalar masters, the 125-tape
majority worker, and two physical fanout/erase drivers. The column and the
quadratic rewind template are outside every initializer/reset write port. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.Bootstrap
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open Completion.SourceDock
noncomputable section

def arenaSlots (i : Fin 125) : Fin 137 := ⟨10+i.val,by omega⟩
def fanoutSlots (i : Fin 135) : Fin 137 :=
  if i.val<44 then ⟨i.val,by omega⟩ else
  if i.val<133 then ⟨i.val+1,by omega⟩ else ⟨i.val+2,by omega⟩
def base (S : Nat) (source : List Bool) (i : Fin 137) : List Bool :=
  if i=44 then source else if i=134 then UnaryTemplate.tape S else []
def baseH (i : Fin 137) : Nat := if i=134 then 1 else 0

def pack (palette : Fin 10→List Bool) (S : Nat) (work : Fin 123→List Bool) : Fin 135→List Bool :=
  Fin.append (Fin.append palette (Fin.append work (fun _ : Fin 1=>List.replicate S true)))
    (fun _ : Fin 1=>List.replicate (S+1) false)
def data (palette : Fin 10→List Bool) (S : Nat) (source : List Bool) (work : Fin 123→List Bool) :=
  install fanoutSlots (base S source) (pack palette S work)
def cold (palette : Fin 10→List Bool) (S : Nat) (source : List Bool) :=
  install fanoutSlots (base S source) (NativeFanout.input (m:=123) palette S)
def readyWork (C R S : Nat) (ps : List (Ring.Poly Nat)) (i : Fin 123) :=
  ZeroPadding.pad S (MajorityComplete.input C R ps (Palette.privatePort i))
def readyData (C R S : Nat) (ps : List (Ring.Poly Nat)) :=
  data (Palette.words C R ps.length) S (OrderedPacketStep.bank C R ps) (readyWork C R S ps)
def heads (i : Fin 137) : Nat :=
  if i.val∈([41,45,48,80,84,87,95,127,131,133,134] : List Nat) then 1 else 0

def headSlots : Fin 10→Fin 137 := ![41,45,48,80,84,87,95,127,131,133]
def raise := RecoveryFocus.machine headSlots (Completion.PhysicalDriverMoves.machine 10 .right)
def lower := RecoveryFocus.machine headSlots (Completion.PhysicalDriverMoves.machine 10 .left)
def fanout := RecoveryFocus.machine fanoutSlots (NativeFanout.machine Palette.privateSelect)
def machine := Composition.machine fanout raise

theorem arena_injective : Function.Injective arenaSlots := by
  intro i j he
  apply Fin.ext
  have hv:=congrArg Fin.val he
  dsimp only [arenaSlots] at hv
  omega

theorem fanout_injective : Function.Injective fanoutSlots := by
  intro i j he
  apply Fin.ext
  have hv:=congrArg Fin.val he
  dsimp only [fanoutSlots] at hv
  split_ifs at hv <;>simp only [Fin.val_mk] at hv <;>omega

theorem fanout_not_source (i : Fin 135) : fanoutSlots i≠44 := by
  intro he
  have hv:=congrArg Fin.val he
  dsimp only [fanoutSlots] at hv
  split_ifs at hv <;>simp only [Fin.val_mk] at hv <;>omega

theorem fanout_not_width (i : Fin 135) : fanoutSlots i≠134 := by
  intro he
  have hv:=congrArg Fin.val he
  dsimp only [fanoutSlots] at hv
  split_ifs at hv <;>simp only [Fin.val_mk] at hv <;>omega

theorem source_data (palette : Fin 10→List Bool) (S : Nat) (source : List Bool)
    (work : Fin 123→List Bool) : data palette S source work 44=source := by
  rw [data,install_other fanoutSlots _ _ _ fanout_not_source]
  rfl

theorem width_data (palette : Fin 10→List Bool) (S : Nat) (source : List Bool)
    (work : Fin 123→List Bool) : data palette S source work 134=UnaryTemplate.tape S := by
  rw [data,install_other fanoutSlots _ _ _ fanout_not_width]
  rfl

theorem target_slot (i : Fin 123) :
    fanoutSlots (((i.castAdd 1).natAdd 10).castAdd 1)=arenaSlots (Palette.privatePort i) := by
  apply Fin.ext
  dsimp only [fanoutSlots,arenaSlots,Palette.privatePort,Fin.val_castAdd,Fin.val_natAdd]
  split_ifs <;>simp only [Fin.val_mk] <;>omega

theorem private_data (palette : Fin 10→List Bool) (S : Nat) (source : List Bool)
    (work : Fin 123→List Bool) (i : Fin 123) :
    data palette S source work (arenaSlots (Palette.privatePort i))=work i := by
  rw [←target_slot,data,install_slot fanoutSlots fanout_injective]
  simp only [pack,Fin.append,Fin.addCases_left,Fin.addCases_right]

theorem master_data (palette : Fin 10→List Bool) (S : Nat) (source : List Bool)
    (work : Fin 123→List Bool) (i : Fin 10) :
    data palette S source work (i.castAdd 127)=palette i := by
  have hs : fanoutSlots ((i.castAdd 124).castAdd 1)=i.castAdd 127 := by
    apply Fin.ext
    have hi:=i.isLt
    simp [fanoutSlots,show i.val<44 by omega]
  rw [←hs,data,install_slot fanoutSlots fanout_injective]
  simp only [pack,Fin.append,Fin.addCases_left]

theorem dock_base_heads : dockH fanoutSlots baseH (fun _=>0)=baseH := by
  apply heads_existing
  intro i
  exact if_neg (fanout_not_width i)

theorem private_cover (i : Fin 125) (hi : i≠34) (hw : i≠124) :
    ∃j,Palette.privatePort j=i := by
  have hival:=i.isLt
  have hi34 : i.val≠34 := by intro he;apply hi;exact Fin.ext he
  have hi124 : i.val≠124 := by intro he;apply hw;exact Fin.ext he
  by_cases h : i.val<34
  · refine ⟨⟨i.val,by omega⟩,?_⟩
    apply Fin.ext
    simp [Palette.privatePort,h]
  · refine ⟨⟨i.val-1,by omega⟩,?_⟩
    apply Fin.ext
    simp only [Palette.privatePort,Fin.val_mk]
    rw [if_neg (by omega)]
    dsimp
    omega

theorem arena_heads (i : Fin 125) : heads (arenaSlots i)=inputH i := by
  have all : ∀i:Fin 125,heads (arenaSlots i)=inputH i := by decide
  exact all i

end
end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.Bootstrap
