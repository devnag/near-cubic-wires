import Proof.Packets.PhysicalSupportReturn

/-! The literal monomial-support union consumes a retained padded mask and one row
of the second monomial mask. It returns the mask and width sentinel for
the next row while both global source/output cursors continue streaming. -/
namespace NearCubicWires.RepairOrdinary.PhysicalSupportUnion
open LocalBitMultitape RecoveryExecution
open PhysicalSupportReturn (cfg)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def values (pairs : List (Bool×Bool)) := pairs.map (fun x => x.1 || x.2)

/-- Canonical finite support representation consumed by the multiplication primitive. -/
def supportMask {B : Nat} (support : Finset (Fin B)) : List Bool :=
  List.ofFn (fun i : Fin B => decide (i ∈ support))

end NearCubicWires.RepairOrdinary.PhysicalSupportUnion
