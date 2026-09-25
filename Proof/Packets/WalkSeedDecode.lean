import Proof.Packets.WalkSeedReady

/-! Complete fixed nine-tape physical seed decoding from the two framed
vertex coordinates and the actual rank template. All other tapes are empty. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 12000
set_option warningAsError true
namespace Theorem25Completion.WalkSeedDecode
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound Completion

attribute [local irreducible] WalkVertexBits.ready WalkSeedReady.machine

def slots : Fin 6→Fin 9:=![2,4,5,6,7,8]
noncomputable def vertex : Machine 9 8:=TapeEmbedding.machine 5 WalkVertexBits.ready
noncomputable def slice : Machine 9 19:=RecoveryFocus.machine slots WalkSeedReady.machine
noncomputable def machine : Machine 9 27:=Composition.machine vertex slice
def input (rank : Nat) (x y : List Bool) : Fin 9→List Bool:=
  ![frame x,frame y,[],[],UnaryTemplate.tape rank,[],[],[],[]]
def middle (rank : Nat) (x y log : List Bool) : Fin 9→List Bool:=
  ![frame x,frame y,y++x,log,UnaryTemplate.tape rank,[],[],[],[]]
noncomputable def output (rank : Nat) (x y low up tr firstLog lastLog : List Bool) : Fin 9→List Bool:=
  install slots (middle rank x y firstLog)
    (WalkSeedReady.output rank (y++x) low up tr lastLog)
def budget (rank : Nat) (x y : List Bool):=2*WalkVertexBits.budget x y+2+1+(16*rank+30)

theorem embedded_zero : Fin.addCases (m:=4) (n:=5) (motive:=fun _=>Nat)
    (fun _=>0) (fun _=>0)=(fun _ : Fin 9=>0) := by
  funext i;fin_cases i <;>rfl

theorem embedded_input (rank : Nat) (x y : List Bool) :
    Fin.addCases (m:=4) (n:=5) (motive:=fun _=>List Bool) (WalkVertexBits.readyInput x y)
      (![UnaryTemplate.tape rank,[],[],[],[]])=input rank x y := by
  funext i;fin_cases i <;>rfl

theorem embedded_middle (rank : Nat) (x y log : List Bool) :
    Fin.addCases (m:=4) (n:=5) (motive:=fun _=>List Bool) (![frame x,frame y,y++x,log])
      (![UnaryTemplate.tape rank,[],[],[],[]])=middle rank x y log := by
  funext i;fin_cases i <;>rfl

theorem slice_input (rank : Nat) (x y pad low up tr log : List Bool)
    (hword : y++x=WalkSeedSlice.source pad low up tr) :
    ∀i,middle rank x y log (slots i)=WalkSeedReady.input rank (WalkSeedSlice.source pad low up tr) i := by
  intro i;fin_cases i
  · exact hword
  all_goals rfl

theorem slice_output (rank : Nat) (x y pad low up tr a b : List Bool)
    (hword : y++x=WalkSeedSlice.source pad low up tr) :
    install slots (middle rank x y a)
      (WalkSeedReady.output rank (WalkSeedSlice.source pad low up tr) low up tr b)=
      output rank x y low up tr a b := by
  rw [←hword]
  rfl

theorem output_selected (rank : Nat) (x y low up tr a b : List Bool) (i : Fin 6) :
    output rank x y low up tr a b (slots i)=
      WalkSeedReady.output rank (y++x) low up tr b i :=
  install_slot slots (by decide) _ _ i

theorem output_ambient (rank : Nat) (x y low up tr a b : List Bool) (i : Fin 9)
    (hi : ∀j, slots j≠i) :
    output rank x y low up tr a b i=middle rank x y a i :=
  install_other slots _ _ i hi

theorem run (rank : Nat) (hr : 0<rank) (x y pad low up tr : List Bool)
    (hword : y++x=WalkSeedSlice.source pad low up tr)
    (hp : pad.length=WalkSeedPadding.padding rank) (hl : low.length=rank)
    (hu : up.length=rank-1) (ht : tr.length=rank) : ∃firstLog lastLog,
    Step machine (budget rank x y) (fun _=>0) (input rank x y) (fun _=>0)
      (output rank x y low up tr firstLog lastLog) ∧
    firstLog.length≤WalkVertexBits.budget x y ∧ lastLog.length≤8*rank+14 := by
  obtain ⟨a,ha,hla⟩:=WalkVertexBits.ready_run x y
  have first:=ha.embed (fun _ : Fin 5=>0) (![UnaryTemplate.tape rank,[],[],[],[]])
  have first':Step vertex (2*WalkVertexBits.budget x y+2) (fun _=>0)
      (input rank x y) (fun _=>0) (middle rank x y a):=
    (first.congr_in embedded_zero (embedded_input rank x y)).congr embedded_zero (embedded_middle rank x y a)
  obtain ⟨b,hb,hlb⟩:=WalkSeedReady.run rank hr pad low up tr hp hl hu ht
  have last:=SourceDock.dock hb slots (by decide) (fun _=>0) (middle rank x y a)
    (by intro i;rfl) (slice_input rank x y pad low up tr a hword)
  have finalH:dockH slots (fun _=>0) (fun _=>0)=(fun _=>0):=
    SourceDock.heads_existing slots _ _ (by intro i;rfl)
  exact ⟨a,b,first'.seq (last.congr finalH (slice_output rank x y pad low up tr a b hword)),hla,hlb⟩

end Theorem25Completion.WalkSeedDecode
