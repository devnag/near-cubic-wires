import Proof.Packets.NativePairNormalize
import Proof.Packets.NativeLiteralCode
import Proof.Packets.PacketBankWrite

/-! The sparse literal code is read from the actually generated singleton
record and selects the resident dense packet-bank entry. No decoded index
or normalized result is supplied to the machine. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NativeAtomStore
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

def heads (pairPos codePos indexPos : Nat) (i : Fin 44) : Nat :=
  Fin.addCases (m:=40) (n:=4) (motive:=fun _=>Nat) (NativePairNormalize.heads pairPos) (![codePos,indexPos,0,0] : Fin 4→Nat) i
def data (C R : Nat) (pairs codes bank : List Bool) (raw : List (List Bool)) (index : Nat) (i : Fin 44) : List Bool :=
  Fin.addCases (m:=40) (n:=4) (motive:=fun _=>List Bool) (NativePairNormalize.result C R pairs raw)
    (![codes,ZeroPadding.pad R (CompareMachine.word index),bank,List.replicate R false] : Fin 4→List Bool) i
def parseSlots : Fin 2→Fin 44 := ![40,41]
def storeSlots : Fin 6→Fin 44 := ![33,42,26,27,41,43]
noncomputable def parse := RecoveryFocus.machine parseSlots NativeLiteralCode.readyMachine
noncomputable def store := RecoveryFocus.machine storeSlots PacketBank.storeSelectedZero

theorem parse_run (C R pairPos code : Nat) (pairs pre post bank : List Bool)
    (raw : List (List Bool)) (hR : 1≤R) :
    Step parse (2*code+9) (heads pairPos pre.length 0)
      (data C R pairs (pre++NativeLiteralCode.word code++post) bank raw 0)
      (heads pairPos (pre.length+code+6) 1)
      (data C R pairs (pre++NativeLiteralCode.word code++post) bank raw code) := by
  have one : ZeroPadding.pad R (CompareMachine.word 0)=List.replicate R false := by
    change ZeroPadding.pad R (List.replicate 1 false)=_
    rw [Rewind.Workspace.pad_zeros,Nat.max_eq_left hR]
  apply PhysicalFocusBoundary.focus (NativeLiteralCode.padded_run R code pre post) parseSlots (by decide)
    (heads pairPos pre.length 0) (heads pairPos (pre.length+code+6) 1)
    (data C R pairs (pre++NativeLiteralCode.word code++post) bank raw 0)
    (data C R pairs (pre++NativeLiteralCode.word code++post) bank raw code)
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>simp [data,parseSlots,Fin.addCases,one]
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i away
    fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 0 rfl) | exact False.elim (away 1 rfl)

theorem store_run (C R pairPos codePos code : Nat) (pairs codes pre oldPayload oldCount post : List Bool)
    (raw : List (List Bool)) (hpre : pre.length=2*code*R)
    (hp : raw.flatten.length≤R) (hc : raw.length+1≤R)
    (hop : oldPayload.length=R) (hoc : oldCount.length=R) :
    Step store (PacketBank.lookupBudget R code+4) (heads pairPos codePos 1)
      (data C R pairs codes (pre++oldPayload++oldCount++post) raw code)
      (heads pairPos codePos 1)
      (data C R pairs codes (pre++ZeroPadding.pad R raw.flatten++
        ZeroPadding.pad R (CompareMachine.word raw.length)++post) raw code) := by
  have hpl : (ZeroPadding.pad R raw.flatten).length=R := by
    rw [ZeroPadding.pad_length,Nat.max_eq_left hp]
  have hcl : (ZeroPadding.pad R (CompareMachine.word raw.length)).length=R := by
    rw [ZeroPadding.pad_length,Nat.max_eq_left (by simpa [CompareMachine.word] using hc)]
  have h:=(PacketBank.store_selected_zero_run R code pre oldPayload oldCount post
    (ZeroPadding.pad R raw.flatten) (ZeroPadding.pad R (CompareMachine.word raw.length))
    hpre hpl hcl hop hoc).pad (![0,0,0,0,R,R] : Fin 6→Nat)
  apply PhysicalFocusBoundary.focus h storeSlots (by decide)
    (heads pairPos codePos 1) (heads pairPos codePos 1)
    (data C R pairs codes (pre++oldPayload++oldCount++post) raw code)
    (data C R pairs codes (pre++ZeroPadding.pad R raw.flatten++
      ZeroPadding.pad R (CompareMachine.word raw.length)++post) raw code)
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>simp [storeSlots,PacketBank.A,ZeroPadding.pad_zero,ZeroPadding.pad,
      data,NativePairNormalize.result,NativePairNormalize.extras,ReusableNative.ready,
      ReusableNative.bank,ReusableNative.readyData,Fin.addCases]
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>simp [storeSlots,PacketBank.A,ZeroPadding.pad_zero,ZeroPadding.pad,
      data,NativePairNormalize.result,NativePairNormalize.extras,ReusableNative.ready,
      ReusableNative.bank,ReusableNative.readyData,Fin.addCases]
  · intro i away
    fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 1 rfl)

end PCJ9eff70d512234a4c_Fixed.Materializer.NativeAtomStore
