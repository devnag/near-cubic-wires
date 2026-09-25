import Proof.Packets.PacketsXMajorityTermDefs

/-! Read the enumerator's actual framed assignment into reusable raw backing.
The source frame and its scratch are retained with all selected heads zero. -/
set_option autoImplicit false
set_option maxHeartbeats 750000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityTermArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport Theorem25Completion.CycleBounds PairedPacketMeaning

def readSlots : Fin 3→Fin 46:=![44,37,45]
noncomputable def read:=RecoveryFocus.machine readSlots Streaming.machine

theorem read_run (C R : Nat) (ps : List Poly) (left right : Poly) (bits : List Bool)
    (count : Nat) (flag : Bool) (out : List Bool) (hb : bits.length≤R) :
    Step read (4*bits.length+2) (H out) (A C R ps left right [] count flag out (frame bits))
      (H out) (A C R ps left right bits count flag out (frame bits)) := by
  obtain ⟨receipt,hr,ht,hh,_⟩:=UInputFields.unwrap_ready bits
  have h:=(Step.of_run hr (funext hh) ht).pad (![0,R,R] : Fin 3→Nat)
  have hz : ZeroPadding.pad R (List.replicate bits.length false)=List.replicate R false:=by
    simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add,Nat.add_sub_of_le hb]
  apply PhysicalFocusBoundary.focus h readSlots (by decide) (H out) (H out) _ _
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>simp [readSlots,A,extras,Fin.addCases,ZeroPadding.pad_zero,ZeroPadding.pad]
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>simp [readSlots,A,extras,Fin.addCases,ZeroPadding.pad_zero,hz]
  · intro i away
    have hi : i≠37:=by intro he;subst i;exact away 1 rfl
    fin_cases i <;>simp_all [H,A,extras,Fin.addCases]

end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityTermArena
