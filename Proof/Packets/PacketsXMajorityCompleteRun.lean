import Proof.Rows.SourceDockCore
import Proof.Packets.PacketsXMajorityCompleteBounds

/-! The complete physical majority constructor: produce positive/negative
factors, return their cursor, enumerate all truth terms, return the term
cursor, and execute the exact descending normalized parity fold. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NormalizedFiniteTransport Theorem25Completion.CycleBounds PairedPacketMeaning
open Completion.SourceDock
noncomputable section

def complement := TapeEmbedding.machine 86 ComplementPacketBank.machine
def returnPairs := PhysicalRewindInto.machine (124 : Fin 125) 37
def enumerate := RecoveryFocus.machine enumSlots enumeration
def returnTerms := PhysicalRewindInto.machine (124 : Fin 125) 82
def fold := RecoveryFocus.machine foldSlots OrderedPacketFold.addMachine
def machine := Composition.machine complement
  (Composition.machine returnPairs (Composition.machine enumerate (Composition.machine returnTerms fold)))
def budget (C w N : Nat) := ComplementPacketBank.budget C w N+1+
  (2*(commonReserve C w)^2+2+1+(enumerationBudget C w N+1+
    (2*(commonReserve C w)^2+2+1+OrderedPacketFold.budget C w (2^N))))

theorem complement_run (C w : Nat) (S : Finset Nat) (d : Nat) (ps : List Poly)
    (hS : ∀j∈S,j<C) (hps : ∀P∈ps,NormalizedIntermediate.Bounded S d P)
    (hAtom : (S.card+1)^d≤2^w) (hN : ps.length≤2^w) (hw : 1≤w) :
    Step complement (ComplementPacketBank.budget C w ps.length)
      inputH (input C (commonReserve C w) ps)
      (producedH C (commonReserve C w) ps) (produced C (commonReserve C w) ps) := by
  have h:=ComplementPacketBank.run C w S d ps [] [] hS hps hAtom hN (by simp) hw
  exact h.embed
    (Fin.addCases (m:=47) (n:=39) (motive:=fun _=>Nat) (enumerationH [])
      (Fin.addCases (m:=38) (n:=1) (motive:=fun _=>Nat) OrderedPacketFold.H (fun _=>1)))
    (Fin.addCases (m:=47) (n:=39) (motive:=fun _=>List Bool) (enumCold C (commonReserve C w) ps)
      (Fin.addCases (m:=38) (n:=1) (motive:=fun _=>List Bool)
        (foldCold C (commonReserve C w) (2^ps.length)) (fun _=>UnaryTemplate.tape ((commonReserve C w)^2))))

theorem pairs_return_run (C w : Nat) (S : Finset Nat) (d : Nat) (ps : List Poly)
    (hps : ∀P∈ps,NormalizedIntermediate.Bounded S d P)
    (hAtom : (S.card+1)^d≤2^w) (hN : ps.length≤2^w) :
    Step returnPairs (2*(commonReserve C w)^2+2)
      (producedH C (commonReserve C w) ps) (produced C (commonReserve C w) ps)
      (pairedReadyH C (commonReserve C w) ps) (produced C (commonReserve C w) ps) := by
  exact PhysicalRewindInto.run ((commonReserve C w)^2) (124 : Fin 125) 37 (by decide)
    _ _ rfl rfl (paired_capacity C w S d ps hps hAtom hN)

theorem enumeration_stage_run (C w : Nat) (S : Finset Nat) (d : Nat) (ps : List Poly)
    (hS : ∀j∈S,j<C) (hps : ∀P∈ps,NormalizedIntermediate.Bounded S d P)
    (hfit : (S.card+1)^(d*ps.length)≤2^w) (hAtom : (S.card+1)^d≤2^w)
    (hN : ps.length≤2^w) (hw : 1≤w) :
    Step enumerate (enumerationBudget C w ps.length)
      (pairedReadyH C (commonReserve C w) ps) (produced C (commonReserve C w) ps)
      (enumeratedH C (commonReserve C w) ps) (enumerated C (commonReserve C w) ps) := by
  have h:=enumerate_run C w S d ps [] hS hps hfit hAtom hN hw
  simpa only [List.nil_append,enumerate,enumeratedH,enumerated,termBank] using
    Completion.SourceDock.dock h enumSlots enum_injective
    (pairedReadyH C (commonReserve C w) ps) (produced C (commonReserve C w) ps)
    (enum_entry_heads C (commonReserve C w) ps) (enum_entry_tapes C (commonReserve C w) ps)

theorem terms_return_run (C w : Nat) (S : Finset Nat) (d : Nat) (ps : List Poly)
    (hps : ∀P∈ps,NormalizedIntermediate.Bounded S d P)
    (hfit : (S.card+1)^(d*ps.length)≤2^w) (hCodes : 2^ps.length≤2^w) :
    Step returnTerms (2*(commonReserve C w)^2+2)
      (enumeratedH C (commonReserve C w) ps) (enumerated C (commonReserve C w) ps)
      (foldReadyH C (commonReserve C w) ps) (enumerated C (commonReserve C w) ps) := by
  have away : ∀j,enumSlots j≠124 := by
    intro j he
    have hj:=enum_below j
    have hv:=congrArg Fin.val he
    omega
  have wh : enumeratedH C (commonReserve C w) ps 124=1 := by
    rw [enumeratedH,dockH_other enumSlots _ _ _ away]
    rfl
  have wa : enumerated C (commonReserve C w) ps 124=UnaryTemplate.tape ((commonReserve C w)^2) := by
    rw [enumerated,install_other enumSlots _ _ _ away]
    rfl
  have pos : enumeratedH C (commonReserve C w) ps 82=(termBank C (commonReserve C w) ps).length := by
    change dockH enumSlots _ _ (enumSlots 43)=_
    rw [dockH_slot enumSlots enum_injective]
    rfl
  exact PhysicalRewindInto.run ((commonReserve C w)^2) (124 : Fin 125) 82 (by decide)
    _ _ wh wa (pos.le.trans (terms_capacity C w S d ps hps hfit hCodes))

theorem parity_stage_run (C w : Nat) (S : Finset Nat) (d : Nat) (ps : List Poly)
    (hS : ∀j∈S,j<C) (hps : ∀P∈ps,NormalizedIntermediate.Bounded S d P)
    (hfit : (S.card+1)^(d*ps.length)≤2^w) (hCodes : 2^ps.length≤2^w) (hw : 1≤w) :
    Step fold (OrderedPacketFold.budget C w (2^ps.length))
      (foldReadyH C (commonReserve C w) ps) (enumerated C (commonReserve C w) ps)
      (finalH C (commonReserve C w) ps) (final C (commonReserve C w) ps) := by
  have h:=OrderedPacketFold.parity_run C w S (d*ps.length) (terms ps) [] hS
    (terms_bounded S d ps hps) hfit (by simpa only [terms_length] using hCodes) (by simp) hw
  rw [terms_length,parity_exact] at h
  exact Completion.SourceDock.dock h foldSlots fold_injective (foldReadyH C (commonReserve C w) ps)
    (enumerated C (commonReserve C w) ps)
    (fold_entry_heads C (commonReserve C w) ps) (fold_entry_tapes C (commonReserve C w) ps)

theorem run (C w : Nat) (S : Finset Nat) (d : Nat) (ps : List Poly)
    (hS : ∀j∈S,j<C) (hps : ∀P∈ps,NormalizedIntermediate.Bounded S d P)
    (hfit : (S.card+1)^(d*ps.length)≤2^w) (hAtom : (S.card+1)^d≤2^w)
    (hN : ps.length≤2^w) (hCodes : 2^ps.length≤2^w) (hw : 1≤w) :
    Step machine (budget C w ps.length) inputH (input C (commonReserve C w) ps)
      (finalH C (commonReserve C w) ps) (final C (commonReserve C w) ps) := by
  exact (complement_run C w S d ps hS hps hAtom hN hw).seq
    ((pairs_return_run C w S d ps hps hAtom hN).seq
      ((enumeration_stage_run C w S d ps hS hps hfit hAtom hN hw).seq
        ((terms_return_run C w S d ps hps hfit hCodes).seq
          (parity_stage_run C w S d ps hS hps hfit hCodes hw))))

theorem output_payload (C R : Nat) (ps : List Poly) :
    final C R ps 112=PacketVector.payload R ((majority ps).map (maskNat C)) := by
  change install foldSlots (enumerated C R ps) _ (foldSlots 26)=_
  rw [install_slot foldSlots fold_injective]
  rfl
theorem output_count (C R : Nat) (ps : List Poly) :
    final C R ps 113=PacketVector.count R ((majority ps).map (maskNat C)) := by
  change install foldSlots (enumerated C R ps) _ (foldSlots 27)=_
  rw [install_slot foldSlots fold_injective]
  rfl

end
end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete
