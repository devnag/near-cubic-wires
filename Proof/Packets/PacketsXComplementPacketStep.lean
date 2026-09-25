import Proof.Packets.PacketsXOrderedPacketRightLookup
import Proof.Packets.PhysicalOneCount

/-! Build the actual pair P, (1+P) for the majority selector. The addition
order is the frozen Boolean negation order. Resident coordinate bytes are
fetched from the source bank; both output packets are physically appended. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ComplementPacketStep
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport Theorem25Completion.CycleBounds

abbrev Poly:=Ring.Poly Nat

def H (out : List Bool) : Fin 38→Nat:=Fin.addCases (m:=37) (n:=1) (motive:=fun _=>Nat)
  (ArithmeticLookup.H 0) (fun _=>out.length)
def A (C R index : Nat) (right : Poly) (ps : List Poly) (out : List Bool) : Fin 38→List Bool:=
  Fin.addCases (m:=37) (n:=1) (motive:=fun _=>List Bool)
    (OrderedPacketStep.A C R index [[]] right ps) (fun _=>out)
def entry (C R : Nat) (P : Poly) :=PacketVector.entry R (P.map (maskNat C))
def slots : Fin 6→Fin 38:=![31,37,26,27,35,36]
noncomputable def fetch:=TapeEmbedding.machine 1 VectorChildLookup.machine
noncomputable def store:=RecoveryFocus.machine slots PacketBank.storeZero
noncomputable def negate:=TapeEmbedding.machine 1 OrderedPacketStep.add
noncomputable def machine:=Composition.machine fetch
  (Composition.machine store (Composition.machine negate store))
def budget (C w index : Nat):=ArithmeticLookup.budget (commonReserve C w) index+
  1+(PacketBank.storeBudget (commonReserve C w)+4)+1+
  ReusableArithmetic.boundedBudget C w+1+(PacketBank.storeBudget (commonReserve C w)+4)

theorem fetch_run (C w : Nat) (ps : List Poly) (i : Fin ps.length) (old : Poly) (out : List Bool)
    (ho : old.length≤2^w) (hps : ∀P∈ps,P.length≤2^w) :
    Step fetch (ArithmeticLookup.budget (commonReserve C w) i.val)
      (H out) (A C (commonReserve C w) i.val old ps out)
      (H out) (A C (commonReserve C w) i.val ps[i.val] ps out) := by
  exact (OrderedPacketStep.fetch_right C w ps i [[]] old ho hps).embed
    (fun _ : Fin 1=>out.length) (fun _ : Fin 1=>out)

theorem store_run (C R index : Nat) (P : Poly) (ps : List Poly) (out : List Bool)
    (hp : PacketVector.Fits R (P.map (maskNat C))) :
    Step store (PacketBank.storeBudget R+4)
      (H out) (A C R index P ps out)
      (H (out++entry C R P)) (A C R index P ps (out++entry C R P)) := by
  have h:=(PacketBank.store_zero_run R index out
    (PacketVector.payload R (P.map (maskNat C))) (PacketVector.count R (P.map (maskNat C)))
    (PacketVector.payload_length hp) (PacketVector.count_length hp)).pad (![0,0,0,0,R,R] : Fin 6→Nat)
  apply PhysicalFocusBoundary.focus h slots (by decide) (H out) (H (out++entry C R P)) _ _
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>simp [slots,A,OrderedPacketStep.A,ArithmeticLookup.A,PacketBank.A,
      Fin.addCases,ReusableArithmetic.state,ReusableArithmetic.bank,ReusableArithmetic.padded,
      ReusableArithmetic.data,NormalizedMultiply.data,NormalizedMultiply.extras,
      PacketVector.payload,PacketVector.count,ZeroPadding.pad_zero]
    simp [ZeroPadding.pad]
  · intro i;fin_cases i <;>simp [slots,H,PacketBank.H,ArithmeticLookup.H,Fin.addCases,entry,PacketVector.entry,List.append_assoc]
  · intro i;fin_cases i <;>simp [slots,A,OrderedPacketStep.A,ArithmeticLookup.A,PacketBank.A,
      Fin.addCases,ReusableArithmetic.state,ReusableArithmetic.bank,ReusableArithmetic.padded,
      ReusableArithmetic.data,NormalizedMultiply.data,NormalizedMultiply.extras,
      PacketVector.payload,PacketVector.count,ZeroPadding.pad_zero,entry,PacketVector.entry,List.append_assoc]
    simp [ZeroPadding.pad]
  · intro i away
    have hi : i≠37:=by intro he;subst i;exact away 1 rfl
    fin_cases i <;>simp_all [H,A,Fin.addCases]

theorem negate_run (C w index : Nat) (P : Poly) (ps : List Poly) (out : List Bool)
    (hP : Fits C P) (hn : Ring.Normal P) (hc : P.length≤2^w) (hw : 1≤w) :
    Step negate (ReusableArithmetic.boundedBudget C w)
      (H out) (A C (commonReserve C w) index P ps out)
      (H out) (A C (commonReserve C w) index (Ring.add [[]] P) ps out) := by
  have oneFit : Fits C ([[]] : Poly):=by simp [Fits]
  have oneNormal : Ring.Normal ([[]] : Poly):=by simp [Ring.Normal]
  have oneCount : ([[]] : Poly).length≤2^w:=by simpa using Nat.one_le_pow w 2 (by decide)
  exact (OrderedPacketStep.add_run C w index [[]] P ps oneFit hP oneNormal hn oneCount hc hw).embed
    (fun _ : Fin 1=>out.length) (fun _ : Fin 1=>out)

theorem run (C w : Nat) (S : Finset Nat) (d : Nat) (ps : List Poly) (i : Fin ps.length)
    (old : Poly) (out : List Bool) (hS : ∀j∈S,j<C)
    (hps : ∀P∈ps,NormalizedIntermediate.Bounded S d P)
    (hfit : (S.card+1)^d≤2^w) (ho : old.length≤2^w) (hw : 1≤w) :
    Step machine (budget C w i.val)
      (H out) (A C (commonReserve C w) i.val old ps out)
      (H (out++entry C (commonReserve C w) ps[i.val]++entry C (commonReserve C w) (Ring.add [[]] ps[i.val])))
      (A C (commonReserve C w) i.val (Ring.add [[]] ps[i.val]) ps
        (out++entry C (commonReserve C w) ps[i.val]++entry C (commonReserve C w) (Ring.add [[]] ps[i.val]))) := by
  have hp:=hps ps[i.val] (List.getElem_mem i.isLt)
  have hn:=NormalizedIntermediate.add (NormalizedIntermediate.one S d) hp
  have h1:=fetch_run C w ps i old out ho
    (fun P hP=>(NormalizedIntermediate.census (hps P hP)).trans hfit)
  have h2:=store_run C (commonReserve C w) i.val ps[i.val] ps out
    (SubstitutionCensus.bounded_packet C w d S ps[i.val] hp hfit).1
  have h3:=negate_run C w i.val ps[i.val] ps (out++entry C (commonReserve C w) ps[i.val])
    (SubstitutionCensus.fits_of_bounded C S hS hp) hp.1.1
    ((NormalizedIntermediate.census hp).trans hfit) hw
  have h4:=store_run C (commonReserve C w) i.val (Ring.add [[]] ps[i.val]) ps
    (out++entry C (commonReserve C w) ps[i.val])
    (SubstitutionCensus.bounded_packet C w d S _ hn hfit).1
  have h:=h1.seq (h2.seq (h3.seq h4))
  have cost : ArithmeticLookup.budget (commonReserve C w) i.val+1+
      (PacketBank.storeBudget (commonReserve C w)+4+1+
      (ReusableArithmetic.boundedBudget C w+1+(PacketBank.storeBudget (commonReserve C w)+4)))=
        budget C w i.val := by unfold budget;omega
  rw [cost] at h
  exact h

end PCJ9eff70d512234a4c_Fixed.Materializer.ComplementPacketStep
