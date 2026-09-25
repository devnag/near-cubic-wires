import Proof.Packets.PacketsXMajorityCodeUpdate
import Proof.Packets.PacketsXMajorityPredicateMeaning
import Proof.Packets.PacketsXMajorityTermRun

/-! Complete fixed-machine enumeration of majority truth-table terms. Every
code emits one packet, including rejected codes, in the original code order. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.CanonicalRecoveryLanguage NearCubicWires.P1Closure
open NormalizedFiniteTransport Theorem25Completion.CycleBounds PairedPacketMeaning

attribute [local irreducible] MajorityTermArena.machine

def assignments (ps : List Poly) := LiveEnumeration.binary ps.length
def terms (ps : List Poly) : List Poly :=
  (assignments ps).map (fun b=>MajorityTermArena.term ps (List.ofFn b))
def emit (C R : Nat) (ps : List Poly) (b : BitInput ps.length) :=
  OrderedPacketStore.entry C R (MajorityTermArena.term ps (List.ofFn b))
def enumerationSlots : Fin 2→Fin 46 := ![44,45]
def enumerationH (out : List Bool) : Fin 47→Nat :=
  Fin.addCases (m:=46) (n:=1) (motive:=fun _=>Nat) (MajorityTermArena.H out) (fun _=>1)
def enumerationA (C R : Nat) (ps : List Poly) (code : Nat) (out : List Bool) : Fin 47→List Bool :=
  Fin.addCases (m:=46) (n:=1) (motive:=fun _=>List Bool)
    (MajorityTermArena.A C R ps [] [] [] 0 false out (frame (SignedSortKey.binary ps.length code)))
    (fun _=>CompareMachine.word (2^ps.length-1))
noncomputable def enumeration := BinaryEnumerator.machine MajorityTermArena.machine enumerationSlots
def enumerationBudget (C w N : Nat) := BinaryEnumerator.budget N (majorityTermBudget C w N)

theorem enumeration_heads (out : List Bool) :
    BinaryEnumerator.heads enumerationSlots MajorityTermArena.H out=MajorityTermArena.H out := by
  unfold BinaryEnumerator.heads
  funext i
  by_cases h : ∃ j,enumerationSlots j=i
  · obtain ⟨j,rfl⟩:=h
    rw [dockH_slot enumerationSlots (by decide)]
    fin_cases j <;>rfl
  · rw [dockH_other enumerationSlots _ _ i (by simpa only [not_exists] using h)]

theorem enumeration_bank (C R : Nat) (ps : List Poly) (j : Nat) (out : List Bool) :
    BinaryEnumerator.bank enumerationSlots
      (fun out=>MajorityTermArena.A C R ps [] [] [] 0 false out []) ps.length R j out=
      MajorityTermArena.A C R ps [] [] [] 0 false out
        (frame (SignedSortKey.binary ps.length j)) := by
  apply HierarchyAllocation.install_eq enumerationSlots (by decide)
  · intro i;fin_cases i <;>rfl
  · intro i away
    have h44 : i≠44 := by intro h;subst i;exact away 0 rfl
    exact (MajorityTermArena.binary_other C R ps [] [] [] 0 false out []
      (frame (SignedSortKey.binary ps.length j)) i h44).symm

theorem enumeration_word (C R : Nat) (ps : List Poly) :
    (assignments ps).flatMap (emit C R ps)=OrderedPacketStep.bank C R (terms ps) := by
  simp only [OrderedPacketStep.bank,terms,List.map_map,PacketVector.bank,List.flatMap_map,
    emit,OrderedPacketStore.entry,Function.comp_def]
  rfl

theorem enumerate_run (C w : Nat) (S : Finset Nat) (d : Nat) (ps : List Poly)
    (out : List Bool) (hS : ∀j∈S,j<C)
    (hps : ∀P∈ps,NormalizedIntermediate.Bounded S d P)
    (hfit : (S.card+1)^(d*ps.length)≤2^w) (hAtom : (S.card+1)^d≤2^w)
    (hN : ps.length≤2^w) (hw : 1≤w) :
    Step enumeration (enumerationBudget C w ps.length)
      (enumerationH out) (enumerationA C (commonReserve C w) ps 0 out)
      (enumerationH (out++OrderedPacketStep.bank C (commonReserve C w) (terms ps)))
      (enumerationA C (commonReserve C w) ps (2^ps.length-1)
        (out++OrderedPacketStep.bank C (commonReserve C w) (terms ps))) := by
  have room := MajorityTermArena.count_room C w ps.length hN
  have call : ∀j,j<2^ps.length→∀pre,
      Step MajorityTermArena.machine (majorityTermBudget C w ps.length)
        (BinaryEnumerator.heads enumerationSlots MajorityTermArena.H pre)
        (BinaryEnumerator.bank enumerationSlots
          (fun out=>MajorityTermArena.A C (commonReserve C w) ps [] [] [] 0 false out [])
          ps.length (commonReserve C w) j pre)
        (BinaryEnumerator.heads enumerationSlots MajorityTermArena.H
          (pre++emit C (commonReserve C w) ps (bitInputOfCode ps.length j)))
        (BinaryEnumerator.bank enumerationSlots
          (fun out=>MajorityTermArena.A C (commonReserve C w) ps [] [] [] 0 false out [])
          ps.length (commonReserve C w) j
          (pre++emit C (commonReserve C w) ps (bitInputOfCode ps.length j))) := by
    intro j _ pre
    rw [enumeration_heads,enumeration_heads,enumeration_bank,enumeration_bank]
    have h:=MajorityTermArena.run C w S d ps (List.ofFn (bitInputOfCode ps.length j)) pre
      (by simp) hS hps hfit hAtom hN hw
    have framed : frame (List.ofFn (bitInputOfCode ps.length j))=
        frame (SignedSortKey.binary ps.length j) := congrArg frame (fixedBits_binary ps.length j)
    rw [framed] at h
    exact h
  have h:=BinaryEnumerator.enumerate_step MajorityTermArena.machine enumerationSlots (by decide)
    MajorityTermArena.H
    (fun out=>MajorityTermArena.A C (commonReserve C w) ps [] [] [] 0 false out [])
    ps.length (commonReserve C w) (majorityTermBudget C w ps.length)
    (emit C (commonReserve C w) ps) out (by omega) call
  rw [enumeration_heads,enumeration_heads,enumeration_bank,enumeration_bank] at h
  change Step enumeration (enumerationBudget C w ps.length)
    (enumerationH out) (enumerationA C (commonReserve C w) ps 0 out)
    (enumerationH (out++(assignments ps).flatMap (emit C (commonReserve C w) ps)))
    (enumerationA C (commonReserve C w) ps (2^ps.length-1)
      (out++(assignments ps).flatMap (emit C (commonReserve C w) ps))) at h
  rw [enumeration_word] at h
  exact h

end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete
