import Proof.Packets.PacketsXMajorityTermDefs
import Proof.Packets.PacketsXFilteredPacketStore

/-! Actual predicate-controlled packet append in the truth-enumerator arena. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityTermArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport Theorem25Completion.CycleBounds PairedPacketMeaning

def storeSlots (i : Fin 39) : Fin 46:=if h:i.val<37 then ⟨i.val,by omega⟩ else if i=37 then 43 else 41
noncomputable def store:=RecoveryFocus.machine storeSlots FilteredPacketStore.machine

theorem store_run (C w : Nat) (ps : List Poly) (left right : Poly) (bits : List Bool) (count : Nat)
    (flag : Bool) (out binary : List Bool) (hr : right.length≤2^w) :
    Step store (12*commonReserve C w+28) (H out) (A C (commonReserve C w) ps left right bits count flag out binary)
      (H (out++OrderedPacketStore.entry C (commonReserve C w) (if flag then right else [])))
      (A C (commonReserve C w) ps left (if flag then right else []) bits count flag
        (out++OrderedPacketStore.entry C (commonReserve C w) (if flag then right else [])) binary) := by
  have h:=(FilteredPacketStore.run C w 0 left right (ComplementPacketBank.pairs ps) out flag hr).pad
    (fun i : Fin 39=>if i=38 then commonReserve C w else 0)
  apply PhysicalFocusBoundary.focus h storeSlots (by decide) (H out)
    (H (out++OrderedPacketStore.entry C (commonReserve C w) (if flag then right else []))) _ _
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>simp [storeSlots,A,extras,FilteredPacketStore.A,OrderedPacketStore.A,
      Fin.addCases,ZeroPadding.pad_zero]
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>simp [storeSlots,A,extras,FilteredPacketStore.A,OrderedPacketStore.A,
      Fin.addCases,ZeroPadding.pad_zero]
  · intro i away
    have h26 : i≠26:=by intro he;subst i;exact away 26 rfl
    have h27 : i≠27:=by intro he;subst i;exact away 27 rfl
    have h43 : i≠43:=by intro he;subst i;exact away 37 rfl
    fin_cases i <;>simp_all [H,A,extras,Fin.addCases,OrderedPacketStep.A,ArithmeticLookup.A,
      ReusableArithmetic.state,ReusableArithmetic.bank,ReusableArithmetic.padded,ReusableArithmetic.data,
      NormalizedMultiply.data,NormalizedMultiply.extras]

end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityTermArena
