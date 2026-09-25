import Proof.Packets.PacketsXMajorityCompleteWords
import Proof.Packets.MajorityCompleteWidth
import Proof.Packets.PacketsXMajorityScalarProducer

/-! A cold178-tape arena. Its only nonempty inputs are the real input column,
four resident arithmetic width fields, and the retained Compare n word.
The scalar and square programs populate all other initialization metadata. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.Cold
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open Completion.SourceDock
noncomputable section

def arenaSlots (i : Fin 137) : Fin 178 := i.castAdd 41
def lowerSlots (i : Fin 5) : Fin 178 := (i.castAdd 36).natAdd 137
def scalarSlots (i : Fin 30) : Fin 178 := ⟨141+i.val,by omega⟩
def widthSlots : Fin 9→Fin 178 := ![139,171,172,173,174,135,175,134,176]
def copySlots : Fin 22→Fin 178 :=
  ![137,138,139,140,150,146,148,152,169,167,0,1,2,3,4,5,6,7,8,9,135,177]
def identitySelect : Fin 10→Option (Fin 10) := fun i=>some i

def input (C R n : Nat) (source : List Bool) : Fin 178→List Bool :=
  Fin.append (fun i : Fin 137=>if i=44 then source else [])
    (Fin.append (metadata C R)
      (Fin.append (fun _ : Fin 1=>CompareMachine.word n) (fun _ : Fin 36=>[])))
def inputHeads (H : Fin 5→Nat) : Fin 178→Nat :=
  Fin.append (fun _ : Fin 137=>0) (Fin.append H (fun _ : Fin 36=>0))
def widthHeads (i : Fin 178) : Nat := if i=134 then 1 else 0

def lower := RecoveryFocus.machine lowerSlots (Completion.PhysicalDriverMoves.machine 5 .left)
def scalar := RecoveryFocus.machine scalarSlots Completion.MajorityScalarProducer.machine
def square := RecoveryFocus.machine widthSlots Width.readyMachine
def copy := RecoveryFocus.machine copySlots (NativeFanout.machine identitySelect)
def initializeMachine := RecoveryFocus.machine arenaSlots Bootstrap.machine

def scalarOutput (n : Nat) : Fin 30→List Bool :=
  Classical.choose (Completion.MajorityScalarProducer.run n)
def afterScalar (C R n : Nat) (source : List Bool) := install scalarSlots (input C R n source) (scalarOutput n)
def afterSquare (C R n : Nat) (source : List Bool) := install widthSlots (afterScalar C R n source) (Width.output R)
def afterCopy (C R n : Nat) (source : List Bool) :=
  install copySlots (afterSquare C R n source)
    (NativeFanout.output identitySelect (palette C R (n+1)) (R^2))
def result (C R n : Nat) (ps : List (Ring.Poly Nat)) :=
  install arenaSlots (afterCopy C R n (OrderedPacketStep.bank C R ps))
    (Bootstrap.readyWith (masters C R (n+1) (R^2)) C R (R^2) ps)
def resultHeads := dockH arenaSlots widthHeads Bootstrap.heads

theorem arena_injective : Function.Injective arenaSlots := by
  intro i j h
  have hv:=congrArg (fun z : Fin 178=>z.val) h
  exact Fin.ext hv
theorem scalar_injective : Function.Injective scalarSlots := by
  intro i j h
  apply Fin.ext
  have hv:=congrArg Fin.val h
  dsimp only [scalarSlots] at hv
  omega
theorem lower_injective : Function.Injective lowerSlots := by
  intro i j h
  apply Fin.ext
  have hv:=congrArg Fin.val h
  simp only [lowerSlots,Fin.val_natAdd,Fin.val_castAdd] at hv
  omega
theorem width_injective : Function.Injective widthSlots := by decide
theorem copy_injective : Function.Injective copySlots := by decide

theorem scalar_input (C R n : Nat) (source : List Bool) (i : Fin 30) :
    input C R n source (scalarSlots i)=Completion.MajorityScalarProducer.input n i := by
  fin_cases i <;>rfl

theorem width_input (C R n : Nat) (source : List Bool) (i : Fin 9) :
    afterScalar C R n source (widthSlots i)=Width.input R i := by
  rw [afterScalar,install_other scalarSlots _ _ _ (by
    have all : ∀i:Fin 9,∀j,scalarSlots j≠widthSlots i := by decide
    exact all i)]
  fin_cases i <;>rfl

theorem lower_run (C R n : Nat) (source : List Bool) (H : Fin 5→Nat)
    (hH : ∀i,H i≤1) : Step lower 1 (inputHeads H) (input C R n source)
      (fun _=>0) (input C R n source) := by
  apply PhysicalFocusBoundary.focus
    (Completion.PhysicalDriverMoves.run .left H (fun i=>input C R n source (lowerSlots i)))
    lowerSlots lower_injective
  · intro i;simp only [inputHeads,lowerSlots,Fin.append,Fin.addCases_left,Fin.addCases_right]
  · intros;rfl
  · intro i
    change H i-1=0
    exact Nat.sub_eq_zero_of_le (hH i)
  · intros;rfl
  · intro i hi
    refine ⟨?_,rfl⟩
    have outside : ∀i:Fin 178,(∀j,lowerSlots j≠i)→inputHeads H i=0 := by
      intro i
      refine Fin.addCases (m:=137) (n:=41) (fun j=>?_) (fun j=>?_) i
      · intro _;simp only [inputHeads,Fin.append,Fin.addCases_left]
      · refine Fin.addCases (m:=5) (n:=36) (fun j=>?_) (fun j=>?_) j
        · intro away;exact False.elim (away j rfl)
        · intro _;simp only [inputHeads,Fin.append,Fin.addCases_right]
    exact outside i hi

theorem scalar_run (C R n : Nat) (source : List Bool) :
    Step scalar (Completion.MajorityScalarProducer.budget n) (fun _=>0) (input C R n source)
      (fun _=>0) (afterScalar C R n source) := by
  have hr:=Completion.SourceDock.dock (Classical.choose_spec (Completion.MajorityScalarProducer.run n)).1
    scalarSlots scalar_injective (fun _ : Fin 178=>0) (input C R n source)
    (by intros;rfl) (scalar_input C R n source)
  exact hr.congr (Completion.MajorityScalarProducer.zero_heads scalarSlots) rfl

theorem square_run (C R n : Nat) (source : List Bool) :
    Step square (Width.budget R+2) (fun _=>0) (afterScalar C R n source)
      widthHeads (afterSquare C R n source) := by
  have hr:=Completion.SourceDock.dock (Width.ready_run R) widthSlots width_injective
    (fun _ : Fin 178=>0) (afterScalar C R n source) (by intros;rfl) (width_input C R n source)
  have hh : dockH (t:=9) (u:=178) widthSlots (fun _=>0) Width.readyH=widthHeads := by
    funext i
    by_cases hi : i=134
    · subst i
      change dockH widthSlots _ _ (widthSlots 7)=_
      rw [dockH_slot widthSlots width_injective]
      rfl
    · unfold dockH
      cases hp : RecoveryFocus.pick widthSlots i with
      | none=>simp only [hp,widthHeads,if_neg hi]
      | some j=>
        have hj : j≠7 := by
          intro he;subst j
          exact hi (RecoveryFocus.slot_of_pick widthSlots hp).symm
        have he : Width.readyH j=0:=if_neg hj
        simp only [hp]
        rw [he]
        exact (if_neg hi).symm
  exact hr.congr hh rfl

end
end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.Cold
