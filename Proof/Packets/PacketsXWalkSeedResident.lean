import Proof.Packets.PacketsXWalkLabelDispatch
import Proof.Packets.WalkSeedTyped

/-! The seed decoder executes directly on the resident canonical walk bank.
Coordinates, label cursor and reusable edge resources stay in their fixed ports. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 15000
set_option warningAsError true
namespace Theorem25Completion.WalkSeedResident
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces NearCubicWires.SupplierWalkBridge
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.SignedSortKey
noncomputable section

def slots : Fin 9→Fin 15:=![0,1,8,9,10,11,12,13,14]
def heads (position : Nat) : Fin 15→Nat:=
  Fin.addCases (m:=8) (n:=7) (motive:=fun _=>Nat) (WalkLabelDispatch.heads position) (fun _=>0)
def extras (rank R : Nat) : Fin 7→List Bool:=
  ![List.replicate R false,List.replicate R false,ZeroPadding.pad R (UnaryTemplate.tape rank),
    List.replicate R false,List.replicate R false,List.replicate R false,List.replicate R false]
def input (rank R L : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank)) (code : List Bool) : Fin 15→List Bool:=
  Fin.addCases (m:=8) (n:=7) (motive:=fun _=>List Bool)
    (WalkLabelDispatch.bank (toeplitzWalkSideBits rank) R L v code) (extras rank R)
def fields (rank : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank)) : Fin 3→List Bool:=
  ![List.ofFn (fun i : Fin rank=>decide ((toeplitzWalkEncoding rank v).1.1.1 i=1)),
    List.ofFn (fun i : Fin (rank-1)=>decide ((toeplitzWalkEncoding rank v).1.1.2 i=1)),
    List.ofFn (fun i : Fin rank=>decide ((toeplitzWalkEncoding rank v).1.2 i=1))]
def decoded (rank : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank)) (a b : List Bool):=
  WalkSeedDecode.output rank (binary (toeplitzWalkSideBits rank) v.1.val)
    (binary (toeplitzWalkSideBits rank) v.2.val) (fields rank v 0) (fields rank v 1) (fields rank v 2) a b
def output (rank R L : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank))
    (code a b : List Bool):=install slots (input rank R L v code)
      (fun i=>ZeroPadding.pad R (decoded rank v a b i))
def machine:=RecoveryFocus.machine slots WalkSeedDecode.machine

theorem input_selected (rank R L : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank))
    (code : List Bool) (i : Fin 9) :
    input rank R L v code (slots i)=ZeroPadding.pad R
      (WalkSeedDecode.input rank (binary (toeplitzWalkSideBits rank) v.1.val)
        (binary (toeplitzWalkSideBits rank) v.2.val) i) := by
  fin_cases i <;>rfl

theorem run (rank R L position : Nat) (hr : 0<rank)
    (v : MargulisVertex (2^toeplitzWalkSideBits rank)) (code : List Bool) : ∃a b,
    Step machine (28*rank+43) (heads position) (input rank R L v code)
      (heads position) (output rank R L v code a b) ∧
      a.length≤6*rank+5 ∧ b.length≤8*rank+14 := by
  obtain ⟨a,b,h,ha,hb⟩:=WalkSeedTyped.run rank hr v
  refine ⟨a,b,?_,ha,hb⟩
  exact CycleFields.Primitives.focus_existing (h.pad (fun _=>R)) slots (by decide)
    (heads position) (input rank R L v code) (by intro i;fin_cases i <;>rfl)
    (input_selected rank R L v code)

theorem output_field (rank R L : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank))
    (code a b : List Bool) (i : Fin 3) :
    output rank R L v code a b ⟨11+i.val,by omega⟩=ZeroPadding.pad R (fields rank v i) := by
  fin_cases i
  · change install slots _ _ (slots 5)=_
    rw [install_slot slots (by decide)]
    change ZeroPadding.pad R (WalkSeedDecode.output _ _ _ _ _ _ _ _ (WalkSeedDecode.slots 2))=_
    rw [WalkSeedDecode.output_selected]
    rfl
  · change install slots _ _ (slots 6)=_
    rw [install_slot slots (by decide)]
    change ZeroPadding.pad R (WalkSeedDecode.output _ _ _ _ _ _ _ _ (WalkSeedDecode.slots 3))=_
    rw [WalkSeedDecode.output_selected]
    rfl
  · change install slots _ _ (slots 7)=_
    rw [install_slot slots (by decide)]
    change ZeroPadding.pad R (WalkSeedDecode.output _ _ _ _ _ _ _ _ (WalkSeedDecode.slots 4))=_
    rw [WalkSeedDecode.output_selected]
    rfl

end
end Theorem25Completion.WalkSeedResident
