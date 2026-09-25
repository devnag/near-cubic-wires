import Proof.Packets.AddressedAtomPadded
import Proof.Packets.IdentityCodeCache

/-! The final occurrence-address atom bank is produced from its actual
native source cache and count. Identity code bytes are physically generated,
then consumed by the same checked normalized dense-table materializer. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.IdentityAtomMaterialize
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsRawPairSeek (Pair cacheWord)
open PacketVector (Packet)
open AddressedAtomMaterialize (H paddedA)
attribute [local irreducible] IdentityCodeCache.machine

theorem codes_eq (cs : List Pair) : AddressedAtomProgram.codes id cs=IdentityCodeLoop.stream cs.length := by
  simp [AddressedAtomProgram.codes,AddressedAtomProgram.codeList,AddressedAtomProgram.code,
    AddressedAtomProgram.index,IdentityCodeLoop.stream,List.flatMap_map]

def slots : Fin 6→Fin 46 := ![44,40,45,33,34,35]
def input (C R : Nat) (cs : List Pair) (initial : List Packet) (oldCodes : List Bool) : Fin 46→List Bool :=
  Function.update (paddedA C R id cs initial 0) 40 oldCodes
noncomputable def lower := PhysicalIndexReload.move (44 : Fin 46) .left
noncomputable def raise := PhysicalIndexReload.move (44 : Fin 46) .right
noncomputable def cache := RecoveryFocus.machine slots IdentityCodeCache.machine
noncomputable def prepare := Composition.machine lower (Composition.machine cache raise)
attribute [local irreducible] prepare

theorem prepare_run (C R : Nat) (cs : List Pair) (initial : List Packet) (oldCodes : List Bool)
    (hcap : cs.length+1≤R) (hold : oldCodes.length≤R)
    (hstream : (IdentityCodeLoop.stream cs.length).length≤R) :
    Step prepare (IdentityCodeCache.budget R cs.length+4) (H 0) (input C R cs initial oldCodes)
      (H 0) (paddedA C R id cs initial 0) := by
  have hz : ZeroPadding.pad R (CompareMachine.word 0)=IdentityCodeCache.zero R := by
    change ZeroPadding.pad R (List.replicate 1 false)=List.replicate R false
    rw [Rewind.Workspace.pad_zeros,Nat.max_eq_left (by omega)]
  let middleH:=Function.update (H 0) 44 0
  have first:=PhysicalIndexReload.move_run (44 : Fin 46) .left (H 0) (input C R cs initial oldCodes)
  have first' : Step lower 1 (H 0) (input C R cs initial oldCodes) middleH (input C R cs initial oldCodes) := first
  have mid : Step cache (IdentityCodeCache.budget R cs.length) middleH (input C R cs initial oldCodes)
      middleH (paddedA C R id cs initial 0) := by
    apply PhysicalFocusBoundary.focus
      (IdentityCodeCache.run R cs.length (IdentityCodeCache.zero R) oldCodes
        (by simp [IdentityCodeCache.zero]) hold hcap hstream)
      slots (by decide) middleH middleH (input C R cs initial oldCodes) (paddedA C R id cs initial 0)
    · intro i;fin_cases i <;>rfl
    · intro i;fin_cases i <;>simp [slots,input,AddressedAtomMaterialize.paddedA,
        AddressedAtomMaterialize.cacheCaps,AddressedAtomMaterialize.A,NativeIndexedAtom.data,
        NativeAtomStore.data,NativePairNormalize.result,NativePairNormalize.extras,
        ReusableNative.ready,ReusableNative.bank,Fin.addCases,ZeroPadding.pad_zero,hz,
        IdentityCodeCache.A]
    · intro i;fin_cases i <;>rfl
    · intro i;fin_cases i <;>simp [slots,AddressedAtomMaterialize.paddedA,
        AddressedAtomMaterialize.cacheCaps,AddressedAtomMaterialize.A,NativeIndexedAtom.data,
        NativeAtomStore.data,NativePairNormalize.result,NativePairNormalize.extras,
        ReusableNative.ready,ReusableNative.bank,Fin.addCases,ZeroPadding.pad_zero,hz,
        IdentityCodeCache.A,codes_eq]
    · intro i away
      have hi:i≠40:=by intro he;subst i;exact away 1 rfl
      exact ⟨rfl,by simp [input,Function.update_of_ne hi]⟩
  have last:=PhysicalIndexReload.move_run (44 : Fin 46) .right middleH (paddedA C R id cs initial 0)
  have last' : Step raise 1 middleH (paddedA C R id cs initial 0) (H 0) (paddedA C R id cs initial 0) :=
    last.congr (by funext i;fin_cases i <;>rfl) rfl
  have all:=first'.seq (mid.seq last')
  have hf : 1+1+(IdentityCodeCache.budget R cs.length+1+1)=IdentityCodeCache.budget R cs.length+4 := by omega
  simpa only [prepare,hf] using all


end PCJ9eff70d512234a4c_Fixed.Materializer.IdentityAtomMaterialize
