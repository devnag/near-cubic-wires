import Proof.Packets.PacketsXOrderedPacketStore
import Proof.Packets.PhysicalBitCallFalse

/-! Store one truth-table term. The actual acceptance flag controls a paid
zeroing of the resident accumulator before storage. Every code emits exactly
one packet, so rejected terms keep their frozen positions in the parity fold. -/
set_option autoImplicit false
set_option maxHeartbeats 850000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.FilteredPacketStore
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport Theorem25Completion.CycleBounds
abbrev Poly:=Ring.Poly Nat

def H (out : List Bool) : Fin 39→Nat:=Fin.addCases (m:=38) (n:=1) (motive:=fun _=>Nat)
  (OrderedPacketStore.H out) (fun _=>0)
def A (C R index : Nat) (left right : Poly) (ps : List Poly) (out : List Bool) (flag : Bool) : Fin 39→List Bool:=
  Fin.addCases (m:=38) (n:=1) (motive:=fun _=>List Bool)
    (OrderedPacketStore.A C R index left right ps out) (fun _=>[flag])
noncomputable def zero:=TapeEmbedding.machine 2 OrderedPacketReset.zeroMachine
noncomputable def filter:=PhysicalBitCall.falseMachine (38 : Fin 39) zero
noncomputable def store:=TapeEmbedding.machine 1 OrderedPacketStore.store
noncomputable def machine:=Composition.machine filter store

theorem zero_run (C w index : Nat) (left right : Poly) (ps : List Poly) (out : List Bool) (flag : Bool)
    (hr : right.length≤2^w) :
    Step zero (4*commonReserve C w+5) (H out) (A C (commonReserve C w) index left right ps out flag)
      (H out) (A C (commonReserve C w) index left [] ps out flag) := by
  have h:=(OrderedPacketReset.zero_run C w index left right ps hr).embed
    (![out.length,0] : Fin 2→Nat) (![out,[flag]] : Fin 2→List Bool)
  refine (h.congr_in ?_ ?_).congr ?_ ?_
  all_goals funext i;fin_cases i <;>rfl

theorem filter_run (C w index : Nat) (left right : Poly) (ps : List Poly) (out : List Bool) (flag : Bool)
    (hr : right.length≤2^w) :
    Step filter (4*commonReserve C w+8) (H out) (A C (commonReserve C w) index left right ps out flag)
      (H out) (A C (commonReserve C w) index left (if flag then right else []) ps out flag) := by
  cases flag
  · exact PhysicalBitCall.false_run (38 : Fin 39) (p:=zero) rfl (zero_run C w index left right ps out false hr)
  · exact (PhysicalBitCall.true_skip (p:=zero) (38 : Fin 39) (H out)
      (A C (commonReserve C w) index left right ps out true) rfl).enlarge (by omega)

theorem store_run (C w index : Nat) (left right : Poly) (ps : List Poly) (out : List Bool) (flag : Bool)
    (hr : right.length≤2^w) :
    Step store (PacketBank.storeBudget (commonReserve C w)+4)
      (H out) (A C (commonReserve C w) index left right ps out flag)
      (H (out++OrderedPacketStore.entry C (commonReserve C w) right))
      (A C (commonReserve C w) index left right ps
        (out++OrderedPacketStore.entry C (commonReserve C w) right) flag) := by
  have fit:=(SubstitutionCensus.packet_fits C w _ (SubstitutionCensus.mask_width C right)
    (by simpa only [List.length_map] using hr)).1
  exact (OrderedPacketStore.store_run C (commonReserve C w) index left right ps out fit).embed
    (fun _ : Fin 1=>0) (fun _=>[flag])

theorem run (C w index : Nat) (left right : Poly) (ps : List Poly) (out : List Bool) (flag : Bool)
    (hr : right.length≤2^w) :
    Step machine (12*commonReserve C w+28) (H out) (A C (commonReserve C w) index left right ps out flag)
      (H (out++OrderedPacketStore.entry C (commonReserve C w) (if flag then right else [])))
      (A C (commonReserve C w) index left (if flag then right else []) ps
        (out++OrderedPacketStore.entry C (commonReserve C w) (if flag then right else [])) flag) := by
  have h:=(filter_run C w index left right ps out flag hr).seq
    (store_run C w index left (if flag then right else []) ps out flag (by cases flag <;>simp_all))
  have cost : (4*commonReserve C w+8)+1+(PacketBank.storeBudget (commonReserve C w)+4)=
      12*commonReserve C w+28:=by unfold PacketBank.storeBudget;omega
  rw [cost] at h
  exact h

end PCJ9eff70d512234a4c_Fixed.Materializer.FilteredPacketStore
