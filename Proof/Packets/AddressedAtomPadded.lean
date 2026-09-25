import Proof.Packets.AddressedAtom
import Proof.Packets.AddressedAtomMeaning

/-! Native atom and generated-code caches retain actual common-R backing
on first entry and every reentry. No logical padding is used as a tape write:
these are executions from the already backed producer outputs. -/
set_option autoImplicit false
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.AddressedAtomMaterialize
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open CloseoutRowsRawPairSeek (Pair cacheWord)
open AddressedAtomProgram (table codes)
open PacketVector (Packet)

def cacheCaps (R : Nat) (i : Fin 46) : Nat := if i=36 ∨ i=40 then R else 0
def paddedA (C R : Nat) (coding : Nat→Nat) (cs : List Pair) (ps : List Packet) (index : Nat) (i : Fin 46) :=
  ZeroPadding.pad (cacheCaps R i) (A C R coding cs ps index i)

theorem cold_padded (C R : Nat) (coding : Nat→Nat) (cs : List Pair)
    (hR : C+2≤R) (hcount : cs.length≤C) (hcodes : ∀i<cs.length,coding i<C)
    (hcache : (cacheWord cs).length≤R) (hcodeword : (codes coding cs).length≤R)
    (hcopy : ∀p∈cs,CloseoutRowsRawPairCopy.budget p≤R+3)
    (hfits : ∀p∈cs,∀m∈p.1++p.2,∀i∈m,i<C)
    (hdata : ∀p∈cs,∀i,(NativeNormalized.A C (p.1++p.2) [] i).length≤R)
    (hfuel : ∀p∈cs,NativeNormalized.budget C (p.1++p.2)+3≤R) :
    Step AddressedAtomCold.machine (AddressedAtomCold.budget C R cs.length) (H 0) (paddedA C R coding cs [] 0)
      (H 0) (paddedA C R coding cs (table C coding cs (List.replicate C []) cs.length) 0) :=
  (AddressedAtomCold.run C R coding cs hR hcount hcodes hcache hcodeword hcopy hfits hdata hfuel).pad (cacheCaps R)

end PCJ9eff70d512234a4c_Fixed.Materializer.AddressedAtomMaterialize
