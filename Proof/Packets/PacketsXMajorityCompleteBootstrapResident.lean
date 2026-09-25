import Proof.Packets.PacketsXMajorityCompleteBootstrapRun
import Proof.Packets.PacketsXMajorityCompleteBootstrapCompute

/-! Resident masters may carry already allocated zero tails. Fanout consumes
exactly their padded words and preserves the actual retained representations. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.Bootstrap
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NormalizedFiniteTransport Theorem25Completion Theorem25Completion.CycleBounds PairedPacketMeaning
noncomputable section

def readyWith (palette : Fin 10→List Bool) (C R S : Nat) (ps : List Poly) :=
  data palette S (OrderedPacketStep.bank C R ps) (readyWork C R S ps)
def finalWith (palette : Fin 10→List Bool) (C R S : Nat) (ps : List Poly) :=
  data palette S (OrderedPacketStep.bank C R ps) (finalWork C R S ps)
def Compatible (palette : Fin 10→List Bool) (C R N S : Nat) : Prop :=
  ∀i,ZeroPadding.pad S (palette i)=ZeroPadding.pad S (Palette.words C R N i)

theorem data_arena_palette (palette palette' : Fin 10→List Bool) (S : Nat)
    (source : List Bool) (work : Fin 123→List Bool) (i : Fin 125) :
    data palette S source work (arenaSlots i)=data palette' S source work (arenaSlots i) := by
  by_cases hs : i=34
  · subst i
    rw [show arenaSlots 34=44 from rfl,source_data,source_data]
  by_cases hw : i=124
  · subst i
    rw [show arenaSlots 124=134 from rfl,width_data,width_data]
  obtain ⟨j,rfl⟩:=private_cover i hs hw
  rw [private_data,private_data]

theorem compatible_length (palette : Fin 10→List Bool) (C R N S : Nat)
    (hf : Palette.Fits C R N S) (hc : Compatible palette C R N S) :
    ∀i,(palette i).length≤S := by
  intro i
  have hl:=Palette.words_length C R N S hf i
  have he:=congrArg List.length (hc i)
  simp only [ZeroPadding.pad,List.length_append,List.length_replicate] at he
  omega

theorem fanout_output_with (palette : Fin 10→List Bool) (C R S : Nat) (ps : List Poly)
    (hR : R+3≤S) (hC : C≤S) (hc : Compatible palette C R ps.length S) :
    NativeFanout.output Palette.privateSelect palette S=pack palette S (readyWork C R S ps) := by
  have hw : (fun i=>ZeroPadding.pad S (NativeFanout.word Palette.privateSelect palette i))=
      readyWork C R S ps := by
    funext i
    have he : ZeroPadding.pad S (NativeFanout.word Palette.privateSelect palette i)=
        ZeroPadding.pad S (NativeFanout.word Palette.privateSelect (Palette.words C R ps.length) i) := by
      cases h : Palette.privateSelect i with
      | none=>simp only [NativeFanout.word,h,Option.elim_none]
      | some j=>simpa only [NativeFanout.word,h,Option.elim_some] using hc j
    exact he.trans (Palette.private_word C R S ps hR hC i)
  change Fin.append (Fin.append _ (Fin.append _ _)) _= _
  rw [hw]
  rfl

theorem boot_with (palette : Fin 10→List Bool) (C R S : Nat) (ps : List Poly)
    (hf : Palette.Fits C R ps.length S) (hc : Compatible palette C R ps.length S) :
    Step machine (2*S+6) baseH (cold palette S (OrderedPacketStep.bank C R ps))
      heads (readyWith palette C R S ps) := by
  have h:=Step.of_ready (NativeFanout.ready Palette.privateSelect palette S
    (compatible_length palette C R ps.length S hf hc))
  have hr:=h.focus fanoutSlots fanout_injective baseH (base S (OrderedPacketStep.bank C R ps))
  rw [dock_base_heads,fanout_output_with palette C R S ps hf.reserve
    (by have :=hf.arithmetic;omega) hc] at hr
  exact (hr.seq (raise_run (readyWith palette C R S ps))).enlarge (by omega)

theorem reload_with (palette : Fin 10→List Bool) (C R S : Nat) (ps : List Poly)
    (hf : Palette.Fits C R ps.length S) (hc : Compatible palette C R ps.length S) :
    Step fanout (2*S+4) baseH
      (data palette S (OrderedPacketStep.bank C R ps) (fun _=>List.replicate S false))
      baseH (readyWith palette C R S ps) := by
  have h:=NativeFanout.reusable Palette.privateSelect palette S
    (compatible_length palette C R ps.length S hf hc)
  have hr:=h.focus fanoutSlots fanout_injective baseH (base S (OrderedPacketStep.bank C R ps))
  rw [dock_base_heads,fanout_output_with palette C R S ps hf.reserve
    (by have :=hf.arithmetic;omega) hc] at hr
  exact hr

theorem reset_with (palette : Fin 10→List Bool) (C R S : Nat) (ps : List Poly)
    (work : Fin 123→List Bool) (hw : ∀i,(work i).length≤S)
    (hf : Palette.Fits C R ps.length S) (hc : Compatible palette C R ps.length S) :
    Step reset (4*S+13) heads (data palette S (OrderedPacketStep.bank C R ps) work)
      heads (readyWith palette C R S ps) := by
  exact ((lower_run _).seq ((erase_run palette S _ work hw).seq
    ((reload_with palette C R S ps hf hc).seq (raise_run _)))).enlarge (by omega)

theorem run_with (palette : Fin 10→List Bool) (C w : Nat) (S : Finset Nat) (d : Nat)
    (ps : List Poly) (hS : ∀j∈S,j<C) (hps : ∀P∈ps,NormalizedIntermediate.Bounded S d P)
    (hfit : (S.card+1)^(d*ps.length)≤2^w) (hAtom : (S.card+1)^d≤2^w)
    (hN : ps.length≤2^w) (hCodes : 2^ps.length≤2^w) (hw : 1≤w) :
    Step compute (budget C w ps.length) heads
      (readyWith palette C (commonReserve C w) ((commonReserve C w)^2) ps)
      heads (finalWith palette C (commonReserve C w) ((commonReserve C w)^2) ps) := by
  have h:=(MajorityComplete.run C w S d ps hS hps hfit hAtom hN hCodes hw).pad
    (caps ((commonReserve C w)^2))
  rw [final_heads] at h
  apply PhysicalFocusBoundary.focus h arenaSlots arena_injective
  · intro i;exact (arena_heads i).symm
  · intro i
    exact ((data_arena_palette palette (Palette.words C (commonReserve C w) ps.length)
      _ _ _ i).trans (ready_arena C (commonReserve C w) ps i)).symm
  · intro i;exact (arena_heads i).symm
  · intro i
    exact ((data_arena_palette palette (Palette.words C (commonReserve C w) ps.length)
      _ _ _ i).trans (final_arena C (commonReserve C w) ps i)).symm
  · intro i hi
    exact ⟨rfl,data_outside _ _ _ _ _ i hi⟩

theorem source_with (palette : Fin 10→List Bool) (C R S : Nat) (ps : List Poly) :
    finalWith palette C R S ps 44=OrderedPacketStep.bank C R ps := source_data _ _ _ _
theorem payload_with (palette : Fin 10→List Bool) (C R S : Nat) (ps : List Poly) :
    finalWith palette C R S ps 122=ZeroPadding.pad S
      (PacketVector.payload R ((majority ps).map (maskNat C))) := by
  exact (data_arena_palette palette (Palette.words C R ps.length) S _ _ (112 : Fin 125)).trans
    (payload_output C R S ps)
theorem count_with (palette : Fin 10→List Bool) (C R S : Nat) (ps : List Poly) :
    finalWith palette C R S ps 123=ZeroPadding.pad S
      (PacketVector.count R ((majority ps).map (maskNat C))) := by
  exact (data_arena_palette palette (Palette.words C R ps.length) S _ _ (113 : Fin 125)).trans
    (count_output C R S ps)
theorem width_with (palette : Fin 10→List Bool) (C R S : Nat) (ps : List Poly) :
    finalWith palette C R S ps 127=ZeroPadding.pad S (UnaryTemplate.tape R) := by
  exact (data_arena_palette palette (Palette.words C R ps.length) S _ _ (117 : Fin 125)).trans
    (width_output C R S ps)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.Bootstrap
