import Proof.Packets.IdentityAtomMaterialize
import Proof.Packets.IdentityCodeBounds
import Proof.Packets.PacketsXCycleAddressedAtomCost
import Proof.Packets.PacketsXDenseAtomBoundary

/-! All individual parser, normalization, output-cache and indexed-write
capacity guards of the identity materializer follow from the actual atom
shape and common reserve. Paid outer counter moves restore the provider's
uniform head boundary. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.IdentityAtomBounded
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open CloseoutRowsRawPairSeek (Pair)
open Theorem25Completion.CycleBounds Theorem25Completion.CycleDenseAtomCost

theorem stream_reserve (C w N : Nat) (hN : N≤C) : (IdentityCodeLoop.stream N).length≤commonReserve C w :=
  (IdentityCodeLoop.stream_length_le N).trans
    ((Nat.mul_le_mul hN (by omega : N+6≤C+8)).trans (reserve_small C w).2)


end PCJ9eff70d512234a4c_Fixed.Materializer.IdentityAtomBounded
