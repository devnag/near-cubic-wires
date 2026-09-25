import Proof.Packets.PacketsXWalkTranscriptColumnBounds
import Proof.Packets.PacketsXWalkTranscriptColumnReady
import Proof.Packets.WalkTranscriptColumnStoreFrame

/-! The actual shared-column majority computation followed by actual packet
append. Its resident postcondition supplies the unchanged column, the full
majority reset boundary, and the extended ordered result bank. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkTranscriptColumnArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open NormalizedFiniteTransport Completion.SourceDock Theorem25Completion.CycleBounds
noncomputable section

structure Computed (palette : Fin 10→List Bool) (C R F N T S index : Nat) (source : List Bool) (old : PacketVector.Packet)
    (target result : List Bool) (ps : List (Ring.Poly Nat)) (A : Fin 471→List Bool) : Prop where
  column : ∀j,A (columnSlots j)=TranscriptColumn.residentTapes R N T index S source
    (PacketVector.payload R old) (PacketVector.count R old) target j
  majority : ∀j,A (majoritySlots j)=MajorityComplete.Bootstrap.finalWith palette C R F ps j
  result : A 29=result

def compute := RecoveryFocus.machine majoritySlots MajorityComplete.Bootstrap.compute
def consume := Composition.machine compute storeResult
def consumeBudget (C w T : Nat) := MajorityComplete.budget C w T+1+
  WalkTranscriptColumnStore.budget (commonReserve C w)

theorem ReadyHeads.store (H : Fin 471→Nat) (old next : Nat) (h : ReadyHeads H old) :
    ReadyHeads (Function.update H 29 next) next := by
  constructor
  · intro j;rw [Function.update_of_ne (column_away_result j)];exact h.column j
  · intro j;rw [Function.update_of_ne (majority_away_result j)];exact h.majority j
  · exact Function.update_self ..

private theorem consume_store_heads (H : Fin 471→Nat) (length : Nat) (hh : ReadyHeads H length) :
    ∀j,H (storeSlots j)=PacketBank.H length 0 j := by
  intro j;fin_cases j
  · exact hh.majority 127
  · exact hh.result
  · exact hh.majority 122
  · exact hh.majority 123
  · exact hh.column 8
  · exact hh.column 5

private theorem consume_store_tapes (palette : Fin 10→List Bool) (C R F N T S index : Nat) (source target result : List Bool)
    (old : PacketVector.Packet) (ps : List (Ring.Poly Nat)) (A : Fin 471→List Bool)
    (ha : Ready palette C R F N T S index source old target result ps A) :
    ∀j,install majoritySlots A (MajorityComplete.Bootstrap.finalWith palette C R F ps) (storeSlots j)=
      WalkTranscriptColumnStore.paddedTapes R index F S result
        ((MajorityComplete.majority ps).map (maskNat C)) j := by
  intro j;fin_cases j
  · change install majoritySlots A _ (majoritySlots 127)=ZeroPadding.pad F (UnaryTemplate.tape R)
    rw [install_slot majoritySlots majority_injective,MajorityComplete.Bootstrap.width_with]
  · change install majoritySlots A _ 29=result
    rw [majority_install_result,ha.result]
  · change install majoritySlots A _ (majoritySlots 122)=ZeroPadding.pad F
      (PacketVector.payload R ((MajorityComplete.majority ps).map (maskNat C)))
    rw [install_slot majoritySlots majority_injective,MajorityComplete.Bootstrap.payload_with]
  · change install majoritySlots A _ (majoritySlots 123)=ZeroPadding.pad F
      (PacketVector.count R ((MajorityComplete.majority ps).map (maskNat C)))
    rw [install_slot majoritySlots majority_injective,MajorityComplete.Bootstrap.count_with]
  · change install majoritySlots A _ (columnSlots 8)=ZeroPadding.pad S (CompareMachine.word index)
    rw [majority_install_column_private _ _ 8 (by decide),ha.column 8]
    rfl
  · change install majoritySlots A _ (columnSlots 5)=List.replicate S false
    rw [majority_install_column_private _ _ 5 (by decide),ha.column 5]
    rfl

theorem consume_run (palette : Fin 10→List Bool) (C w N T S index : Nat) (support : Finset Nat) (d : Nat)
    (source target result : List Bool) (old : PacketVector.Packet) (ps : List (Ring.Poly Nat))
    (hS : ∀j∈support,j<C) (hps : ∀P∈ps,NormalizedIntermediate.Bounded support d P)
    (hfit : (support.card+1)^(d*ps.length)≤2^w) (hAtom : (support.card+1)^d≤2^w)
    (hN : ps.length≤2^w) (hCodes : 2^ps.length≤2^w) (hw : 1≤w)
    (H : Fin 471→Nat) (A : Fin 471→List Bool) (hh : ReadyHeads H result.length)
    (ha : Ready palette C (commonReserve C w) ((commonReserve C w)^2) N T S index
      source old target result ps A)
    (ht : target=OrderedPacketStep.bank C (commonReserve C w) ps) :
    let R:=commonReserve C w
    let packet:=(MajorityComplete.majority ps).map (maskNat C)
    let next:=result++PacketVector.entry R packet
    ∃B,Step consume (consumeBudget C w ps.length) H A (Function.update H 29 next.length) B ∧
      Computed palette C R (R^2) N T S index source old target next ps B ∧
      ReadyHeads (Function.update H 29 next.length) next.length := by
  dsimp only
  have localRun:=MajorityComplete.Bootstrap.run_with palette C w support d ps hS hps hfit hAtom hN hCodes hw
  have actual:=dock localRun majoritySlots majority_injective H A hh.majority (ha.majority_pin ht)
  rw [heads_existing majoritySlots H _ hh.majority] at actual
  have hp : PacketVector.Fits (commonReserve C w) ((MajorityComplete.majority ps).map (maskNat C)) :=
    VectorBottomUp.packet_fits _ _ (SubstitutionCensus.bounded_packet C w (d*ps.length) support _
      (MajorityComplete.majority_bounded support d ps hps) hfit).2
  have stored:=store_run_update (commonReserve C w) index ((commonReserve C w)^2) S result _ hp H _
    (consume_store_heads H result.length hh)
    (consume_store_tapes palette C (commonReserve C w) ((commonReserve C w)^2) N T S index
      source target result old ps A ha)
  have joined:=actual.seq stored
  refine ⟨_,joined,⟨?_,?_,?_⟩,ReadyHeads.store H _ _ hh⟩
  · intro j
    rw [Function.update_of_ne (column_away_result j)]
    rw [majority_keeps_column]
    · exact ha.column j
    · rw [MajorityComplete.Bootstrap.source_with,←ht,ha.column 6]
      rfl
  · intro j
    rw [Function.update_of_ne (majority_away_result j),install_slot majoritySlots majority_injective]
  · exact Function.update_self ..

end
end Theorem25Completion.WalkTranscriptColumnArena
