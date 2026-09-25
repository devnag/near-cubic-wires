import Proof.Packets.PacketsXLiteralCacheReuse
import Proof.Packets.PhysicalIndexReload

/-! The actual reflected-cache refill with a uniform head-zero boundary for
every private tape. The retained common reserve driver alone stays at head1. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.LiteralCacheTransaction
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open Theorem25Completion.CycleLiteralPairCost

def heads (i : Fin 68) : Nat := if i=62 then 1 else 0
def movePorts : Fin 2→Fin 68 := ![1,61]
noncomputable def move (d : HeadMove) := RecoveryFocus.machine movePorts (Completion.PhysicalDriverMoves.machine 2 d)
def padMetadata (R : Nat) (A : Fin 68→List Bool) (i : Fin 68) :=
  ZeroPadding.pad (if i=64 then R else if i=65 then R else 0) (A i)
def input (R tag count : Nat) (b : Fin 68→List Bool) := padMetadata R (LiteralCacheReload.input R tag count b)
def output (R tag count : Nat) := padMetadata R (LiteralCacheReuse.output R tag count)
noncomputable def machine := Composition.machine (move .right)
  (Composition.machine LiteralCacheReuse.machine (move .left))
def budget (R tag count : Nat) := LiteralCacheReuse.budget R tag count+4

theorem raise_run (A : Fin 68→List Bool) :
    Step (move .right) 1 heads A LiteralCacheReuse.heads A := by
  apply PhysicalFocusBoundary.focus
    (Completion.PhysicalDriverMoves.run .right (fun _ : Fin 2=>0) (fun j=>A (movePorts j)))
    movePorts (by decide) heads LiteralCacheReuse.heads A A
  · intro i;fin_cases i;rfl;rfl
  · intro i;rfl
  · intro i;fin_cases i;rfl;rfl
  · intro i;rfl
  · intro i away
    have h1 : i≠1 := by intro he;subst i;exact away 0 rfl
    have h61 : i≠61 := by intro he;subst i;exact away 1 rfl
    exact ⟨by simp [heads,LiteralCacheReuse.heads,LiteralCacheReload.heads,LiteralCacheAllocate.heads,h1,h61],rfl⟩

theorem lower_run (A : Fin 68→List Bool) :
    Step (move .left) 1 LiteralCacheReuse.heads A heads A := by
  apply PhysicalFocusBoundary.focus
    (Completion.PhysicalDriverMoves.run .left (fun _ : Fin 2=>1) (fun j=>A (movePorts j)))
    movePorts (by decide) LiteralCacheReuse.heads heads A A
  · intro i;fin_cases i;rfl;rfl
  · intro i;rfl
  · intro i;fin_cases i;rfl;rfl
  · intro i;rfl
  · intro i away
    have h1 : i≠1 := by intro he;subst i;exact away 0 rfl
    have h61 : i≠61 := by intro he;subst i;exact away 1 rfl
    exact ⟨by simp [heads,LiteralCacheReuse.heads,LiteralCacheReload.heads,LiteralCacheAllocate.heads,h1,h61],rfl⟩

theorem run (C w tag count : Nat) (b : Fin 68→List Bool) (ht : tag≤C) (hc : count≤C)
    (hcode : ∀i,i<count→Nat.pair tag i≤C)
    (hb : ∀i,i≠59→i≠60→i≠62→i≠64→i≠65→(b i).length≤commonReserve C w) :
    Step machine (budget (commonReserve C w) tag count) heads
      (input (commonReserve C w) tag count b) heads (output (commonReserve C w) tag count) := by
  have middle:=LiteralCacheReuse.run_metadata_pad C w tag count (commonReserve C w) (commonReserve C w)
    b ht hc hcode hb
  have h:=(raise_run _).seq (middle.seq (lower_run _))
  have inputEq : (fun i : Fin 68=>ZeroPadding.pad
      (if i=64 then commonReserve C w else if i=65 then commonReserve C w else 0)
      (LiteralCacheReload.input (commonReserve C w) tag count b i))=
      input (commonReserve C w) tag count b := by funext i;rfl
  have outputEq : (fun i : Fin 68=>ZeroPadding.pad
      (if i=64 then commonReserve C w else if i=65 then commonReserve C w else 0)
      (LiteralCacheReuse.output (commonReserve C w) tag count i))=
      output (commonReserve C w) tag count := by funext i;rfl
  have actual:=(h.congr_in rfl inputEq).congr rfl outputEq
  have he : 1+1+(LiteralCacheReuse.budget (commonReserve C w) tag count+1+1)=
      budget (commonReserve C w) tag count := by unfold budget;omega
  simpa only [he,machine] using actual

theorem output_cache (R tag count : Nat) :
    output R tag count 2=ZeroPadding.pad R (ReflectedLiteralCache.stream tag count) := by
  simp only [output,padMetadata,show (2 : Fin 68)≠64 by decide,show (2 : Fin 68)≠65 by decide,
    if_false,ZeroPadding.pad_zero]
  rfl

end PCJ9eff70d512234a4c_Fixed.Materializer.LiteralCacheTransaction
