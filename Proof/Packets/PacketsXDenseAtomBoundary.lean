import Proof.Packets.DenseAtomPadded
import Proof.Packets.PacketsXCycleDenseAtomCost

/-! Actual paid cursor boundary for repeated dense literal materialization.
The reserve cursor remains at one; both loop counters return to zero. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DenseAtomBoundary
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open CloseoutRowsRawPairSeek (Pair cacheWord)
open Theorem25Completion.CycleBounds Theorem25Completion.CycleDenseAtomCost

attribute [local irreducible] DenseAtomMaterialize.machine DenseAtomCold.machine

def heads (i : Fin 46) : Nat := if i=33 then 1 else 0
def movePorts : Fin 2→Fin 46 := ![44,45]
noncomputable def move (d : HeadMove) := RecoveryFocus.machine movePorts (Completion.PhysicalDriverMoves.machine 2 d)
noncomputable def machine := Composition.machine (move .right)
  (Composition.machine DenseAtomMaterialize.machine (move .left))
noncomputable def cold := Composition.machine (move .right)
  (Composition.machine DenseAtomCold.machine (move .left))
def budget (C R count : Nat) := DenseAtomMaterialize.budget C R count+4

theorem raise_run (A : Fin 46→List Bool) :
    Step (move .right) 1 heads A (DenseAtomMaterialize.H 0) A := by
  apply PhysicalFocusBoundary.focus
    (Completion.PhysicalDriverMoves.run .right (fun _ : Fin 2=>0) (fun j=>A (movePorts j)))
    movePorts (by decide) heads (DenseAtomMaterialize.H 0) A A
  · intro i;fin_cases i;rfl;rfl
  · intro i;rfl
  · intro i;fin_cases i;rfl;rfl
  · intro i;rfl
  · intro i away
    fin_cases i <;>first | exact ⟨rfl,rfl⟩ | exact False.elim (away 0 rfl) | exact False.elim (away 1 rfl)

theorem lower_run (A : Fin 46→List Bool) :
    Step (move .left) 1 (DenseAtomMaterialize.H 0) A heads A := by
  apply PhysicalFocusBoundary.focus
    (Completion.PhysicalDriverMoves.run .left (fun _ : Fin 2=>1) (fun j=>A (movePorts j)))
    movePorts (by decide) (DenseAtomMaterialize.H 0) heads A A
  · intro i;fin_cases i;rfl;rfl
  · intro i;rfl
  · intro i;fin_cases i;rfl;rfl
  · intro i;rfl
  · intro i away
    fin_cases i <;>first | exact ⟨rfl,rfl⟩ | exact False.elim (away 0 rfl) | exact False.elim (away 1 rfl)

attribute [local irreducible] machine cold

theorem run (C w tag : Nat) (cs : List Pair) (initial : List PacketVector.Packet)
    (hw : 1≤w) (hcount : cs.length≤C) (hcodes : ∀i<cs.length,Nat.pair tag i<C)
    (hshape : ∀p∈cs,AtomShape C p)
    (hinit : initial.length=C) (hinits : ∀P∈initial,PacketVector.Fits (commonReserve C w) P) :
    Step machine (budget C (commonReserve C w) cs.length)
      heads (DenseAtomMaterialize.paddedA C (commonReserve C w) tag cs initial 0)
      heads (DenseAtomMaterialize.paddedA C (commonReserve C w) tag cs
        (DenseAtomProgram.table C tag cs initial cs.length) 0) := by
  have middle:=(Theorem25Completion.CycleDenseAtomCost.run C w tag cs initial
    hw hcount hcodes hshape hinit hinits).pad (DenseAtomMaterialize.cacheCaps (commonReserve C w))
  have inputEq : (fun i : Fin 46=>ZeroPadding.pad (DenseAtomMaterialize.cacheCaps (commonReserve C w) i)
      (DenseAtomMaterialize.A C (commonReserve C w) tag cs initial 0 i))=
      DenseAtomMaterialize.paddedA C (commonReserve C w) tag cs initial 0 := by funext i;rfl
  have outputEq : (fun i : Fin 46=>ZeroPadding.pad (DenseAtomMaterialize.cacheCaps (commonReserve C w) i)
      (DenseAtomMaterialize.A C (commonReserve C w) tag cs (DenseAtomProgram.table C tag cs initial cs.length) 0 i))=
      DenseAtomMaterialize.paddedA C (commonReserve C w) tag cs (DenseAtomProgram.table C tag cs initial cs.length) 0 := by funext i;rfl
  have actual:=(middle.congr_in rfl inputEq).congr rfl outputEq
  have whole:=(raise_run _).seq (actual.seq (lower_run _))
  have he : 1+1+(DenseAtomMaterialize.budget C (commonReserve C w) cs.length+1+1)=budget C (commonReserve C w) cs.length := by unfold budget;omega
  simpa only [he,machine] using whole

end PCJ9eff70d512234a4c_Fixed.Materializer.DenseAtomBoundary
