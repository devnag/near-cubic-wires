import Proof.Packets.PacketsXDenseAtomBoundary
import Proof.Packets.WindowProviderPorts

/-! The actual dense literal-table machine in the fixed provider arena.
It changes only the dense bank, retaining both physical source caches. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open CloseoutRowsRawPairSeek (Pair)
open Theorem25Completion.CycleBounds Theorem25Completion.CycleDenseAtomCost

attribute [local irreducible] DenseAtomBoundary.machine DenseAtomBoundary.cold

def densePorts : Fin 46→Fin 256 := Fin.addCases (m:=36) (n:=10) nativePorts
  (![125,130,131,124,186,126,140,127,128,129] : Fin 10→Fin 256)
theorem dense_injective : Function.Injective densePorts := by decide
noncomputable def buildDense := RecoveryFocus.machine densePorts DenseAtomBoundary.machine

theorem dense_bank_update (C R tag : Nat) (cs : List Pair) (before after : List PacketVector.Packet) :
    DenseAtomMaterialize.paddedA C R tag cs after 0=
      Function.update (DenseAtomMaterialize.paddedA C R tag cs before 0) 42 (PacketVector.bank R after) := by
  funext i
  fin_cases i <;>try rfl
  change ZeroPadding.pad 0 (PacketVector.bank R after)=PacketVector.bank R after
  exact ZeroPadding.pad_zero _

private theorem dense_focus {s : Nat} {M : Machine 46 s} {cost C R tag : Nat} {cs : List Pair}
    {before after : List PacketVector.Packet}
    (execution : Step M cost DenseAtomBoundary.heads (DenseAtomMaterialize.paddedA C R tag cs before 0)
      DenseAtomBoundary.heads (DenseAtomMaterialize.paddedA C R tag cs after 0))
    (H : Fin 256→Nat) (A : Fin 256→List Bool)
    (hH : ∀i,DenseAtomBoundary.heads i=H (densePorts i))
    (hA : ∀i,A (densePorts i)=DenseAtomMaterialize.paddedA C R tag cs before 0 i) :
    Step (RecoveryFocus.machine densePorts M) cost H A H (Function.update A 140 (PacketVector.bank R after)) := by
  apply PhysicalFocusBoundary.focus execution densePorts dense_injective H H A _ hH (fun i=>(hA i).symm) hH
  · intro i
    rw [dense_bank_update C R tag cs before after]
    by_cases hi : i=42
    · subst i;rfl
    · have hp : densePorts i≠140 := by
        intro he
        exact hi (dense_injective (show densePorts i=densePorts 42 from he))
      simp only [Function.update_of_ne hi,Function.update_of_ne hp]
      exact (hA i).symm
  · intro i away
    have hi : i≠140 := by intro he;subst i;exact away 42 rfl
    exact ⟨rfl,by simp only [Function.update_of_ne hi]⟩

theorem build_dense_run (C w tag : Nat) (cs : List Pair) (initial : List PacketVector.Packet)
    (hw : 1≤w) (hcount : cs.length≤C) (hcodes : ∀i<cs.length,Nat.pair tag i<C)
    (hshape : ∀p∈cs,AtomShape C p)
    (hinit : initial.length=C) (hinits : ∀P∈initial,PacketVector.Fits (commonReserve C w) P)
    (H : Fin 256→Nat) (A : Fin 256→List Bool)
    (hH : ∀i,DenseAtomBoundary.heads i=H (densePorts i))
    (hA : ∀i,A (densePorts i)=DenseAtomMaterialize.paddedA C (commonReserve C w) tag cs initial 0 i) :
    Step buildDense (DenseAtomBoundary.budget C (commonReserve C w) cs.length) H A H
      (Function.update A 140 (PacketVector.bank (commonReserve C w)
        (DenseAtomProgram.table C tag cs initial cs.length))) :=
  dense_focus (DenseAtomBoundary.run C w tag cs initial hw hcount hcodes hshape hinit hinits) H A hH hA

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
