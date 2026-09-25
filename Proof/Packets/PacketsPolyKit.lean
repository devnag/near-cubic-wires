import Proof.Packets.PacketsLevelBound
import Proof.Packets.PacketsXCycleBoundedArithmetic
import Proof.Packets.PacketVector

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.PolyKit
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.CanonicalFourfoldRowProgram
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
noncomputable section

abbrev Poly := Ring.Poly ℕ

/-! ## Codec and capacity -/

/-- The kit codec of one polynomial: its support masks over the code range `[0, C)`. -/
def masks (C : ℕ) (P : Poly) : List (List Bool) := P.map (NormalizedFiniteTransport.maskNat C)

/-- The single scratch reserve of the kit. -/
def reserve (C w : ℕ) : ℕ := Theorem25Completion.CycleBounds.commonReserve C w

/-- A polynomial vector (e.g. a level vector over `pop+1` candidates), entry after entry. -/
def vector (C w : ℕ) (ps : List Poly) : List Bool := PacketVector.bank (reserve C w) (ps.map (masks C))

/-! ## Arena operations (REUSED: `ReusableArithmetic.nat_{add,mul}{,_left}_bounded`) -/

/-! ## `ElementarySymmetric` from arena add/mul (the one constructor with no transplant machine)

`E l k := structuralGF2ElementarySymmetric l k = Ring.norm (l.sublistsLen k)`. For an increasing
code list, `E (a :: l) (n+1) = add (E l (n+1)) (mul [[a]] (E l n))`, `E l 0 = [[]]`,
`E [] (n+1) = []`: a dynamic program over suffixes whose steps are arena ops plus the variable
register `[[a]]`. The delta and terminal literal codes are increasing (`deltaCodes_increasing`). -/

end
end NearCubicWires.PacketsConstruction.PolyKit
