import Proof.Packets.NativeIndexedAtom
import Proof.Packets.PacketVectorReplace
import Proof.Packets.PhysicalZeroBank

/-! The dense atom bank is physically allocated from the measured support
width and the retained common reserve. Invalid sparse literal codes begin
as actual zero-polynomial entries. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DenseAtomInitialize
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NativeIndexedAtom (heads data)

def widthSlot : Fin 1→Fin 45 := ![24]
def allocateSlots : Fin 4→Fin 45 := ![33,42,43,24]
def raisedHeads (i : Fin 45) := if i=24 then 1 else heads 0 0 i
noncomputable def up := RecoveryFocus.machine widthSlot (Completion.PhysicalDriverMoves.machine 1 .right)
noncomputable def down := RecoveryFocus.machine widthSlot (Completion.PhysicalDriverMoves.machine 1 .left)
noncomputable def allocate := RecoveryFocus.machine allocateSlots PhysicalZeroBank.machine
noncomputable def machine := Composition.machine up (Composition.machine allocate down)
def budget (C R : Nat) := C*(12*R+24)+15

theorem moves (C R index : Nat) (pairs codes bank : List Bool) :
    Step up 1 (heads 0 0) (data C R pairs codes bank index) raisedHeads (data C R pairs codes bank index) ∧
    Step down 1 raisedHeads (data C R pairs codes bank index) (heads 0 0) (data C R pairs codes bank index) := by
  constructor
  · apply PhysicalFocusBoundary.focus
      (Completion.PhysicalDriverMoves.run .right (fun _ : Fin 1=>0)
        (fun _=>ZeroPadding.pad R (UnaryTemplate.tape C))) widthSlot (by decide)
      (heads 0 0) raisedHeads (data C R pairs codes bank index) (data C R pairs codes bank index)
    · intro i;fin_cases i;rfl
    · intro i;fin_cases i;rfl
    · intro i;fin_cases i;rfl
    · intro i;fin_cases i;rfl
    · intro i away
      have hi : i≠24 := by intro he;subst i;exact away 0 rfl
      exact ⟨by simp [raisedHeads,hi],rfl⟩
  · apply PhysicalFocusBoundary.focus
      (Completion.PhysicalDriverMoves.run .left (fun _ : Fin 1=>1)
        (fun _=>ZeroPadding.pad R (UnaryTemplate.tape C))) widthSlot (by decide)
      raisedHeads (heads 0 0) (data C R pairs codes bank index) (data C R pairs codes bank index)
    · intro i;fin_cases i;rfl
    · intro i;fin_cases i;rfl
    · intro i;fin_cases i;rfl
    · intro i;fin_cases i;rfl
    · intro i away
      have hi : i≠24 := by intro he;subst i;exact away 0 rfl
      exact ⟨by simp [raisedHeads,hi],rfl⟩

theorem run (C R index : Nat) (pairs codes : List Bool) (hC : C+2≤R) :
    Step machine (budget C R) (heads 0 0) (data C R pairs codes [] index)
      (heads 0 0) (data C R pairs codes (PacketVector.bank R (List.replicate C [])) index) := by
  have h:=(PhysicalZeroBank.run R C).pad (![0,0,R,R] : Fin 4→Nat)
  have hw:=VectorCounter.padded_template_word C R hC
  have alloc : Step allocate (C*(12*R+24)+11) raisedHeads (data C R pairs codes [] index)
      raisedHeads (data C R pairs codes (List.replicate (C*(2*R)) false) index) := by
    apply PhysicalFocusBoundary.focus h allocateSlots (by decide) raisedHeads raisedHeads
      (data C R pairs codes [] index) (data C R pairs codes (List.replicate (C*(2*R)) false) index)
    · intro i;fin_cases i <;>rfl
    · intro i;fin_cases i <;>simp [allocateSlots,PhysicalZeroBank.tapes,PhysicalZeroBank.A,data,NativeAtomStore.data,
        NativePairNormalize.result,NativePairNormalize.extras,ReusableNative.ready,
        ReusableNative.readyData,ReusableNative.bank,Fin.addCases,ZeroPadding.pad,hw]
      simpa [ZeroPadding.pad] using hw.symm
    · intro i;fin_cases i <;>rfl
    · intro i;fin_cases i <;>simp [allocateSlots,PhysicalZeroBank.tapes,PhysicalZeroBank.A,data,NativeAtomStore.data,
        NativePairNormalize.result,NativePairNormalize.extras,ReusableNative.ready,
        ReusableNative.readyData,ReusableNative.bank,Fin.addCases,ZeroPadding.pad,hw]
      simpa [ZeroPadding.pad] using hw.symm
    · intro i away
      fin_cases i <;>first | exact ⟨rfl,rfl⟩ | exact False.elim (away 1 rfl)
  have all:=(moves C R index pairs codes []).1 |>.seq
    (alloc.seq (moves C R index pairs codes (List.replicate (C*(2*R)) false)).2)
  rw [PacketVector.empty_bank R C (by omega)]
  have fuel : 1+1+(C*(12*R+24)+11+1+1)=budget C R := by unfold budget;omega
  simpa only [machine,fuel] using all

end PCJ9eff70d512234a4c_Fixed.Materializer.DenseAtomInitialize
