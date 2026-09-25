import Proof.Packets.PacketsXSubstitutionReusableNat
import Proof.Packets.SubstitutionCallAllocate

/-! First actual substitution call, including physical allocation of the nine
private scratch tapes. The checked arithmetic bank and atom table are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionCall
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.CanonicalFourfoldRowProgram
open NormalizedFiniteTransport SubstitutionCensus Theorem25Completion.CycleBounds
open SubstitutionOuter SubstitutionInvariant

noncomputable def coldExecute:=Composition.machine SubstitutionScratch.machine execute
def coldBudget (C R M : Nat):=2*R+4+1+totalBudget C R M

theorem cold_nat_run (C w d : Nat) (S : Finset Nat) (hS : ∀ j∈S,j<C)
    (hw : 1≤w) (hfit : (S.card+1)^d≤2^w) (hfitAtom : S.card+1≤2^w)
    (P : Ring.Poly Nat) (hP : Good C P) (hdeg : Ring.Degree d P) (hcount : P.length≤2^w)
    (atoms : List (Ring.Poly Nat)) (hlen : atoms.length=C) (ha : ∀ Q∈atoms,Bounded S 1 Q)
    (left : Ring.Poly Nat) (hl : left.length≤2^w) :
    Step coldExecute (coldBudget C (commonReserve C w) P.length) heads
      (coldResident C (commonReserve C w) (left.map (maskNat C)) (P.map (maskNat C))
        (PacketVector.bank (commonReserve C w) (atomMasks C atoms)))
      heads (resident C (commonReserve C w) ((leftResult atoms P left).map (maskNat C))
        ((Normalized.structuralGF2Substitute (fun code=>atoms.getD code []) P).map (maskNat C))
        (PacketVector.bank (commonReserve C w) (atomMasks C atoms))) :=
  (allocate_run C (commonReserve C w) (left.map (maskNat C)) (P.map (maskNat C))
    (PacketVector.bank (commonReserve C w) (atomMasks C atoms))).seq
    (nat_run C w d S hS hw hfit hfitAtom P hP hdeg hcount atoms hlen ha left hl)

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionCall
