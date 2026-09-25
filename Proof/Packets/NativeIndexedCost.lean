import Proof.Packets.NativeIndexedAtom

/-! A uniform concrete cost for each executed dense-bank atom transaction.
The input inequalities are the actual native/word reserve facts, not an
assumed execution budget for the whole transaction. -/
set_option autoImplicit false
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NativeIndexedAtom
open NearCubicWires.RepairOrdinary
open CloseoutRowsRawPairSeek (Pair cacheWord)

theorem budget_le (C R code : Nat) (pre : List Pair) (p : Pair)
    (hcopy : CloseoutRowsRawPairCopy.budget p≤R+3)
    (hNative : NativeNormalized.budget C (p.1++p.2)+3≤R)
    (hpre : (cacheWord pre).length≤R) (hindex : pre.length≤C) (hcode : code≤C) :
    budget C R code pre p≤128*(C+1)*(R+1) := by
  have hm:=Nat.mul_le_mul_right R hcode
  unfold budget NativePairSeekReady.budget CloseoutRowsRawPairSeek.budget
    NativeAtomStore.transactionBudget NativePairNormalize.budget NativePairCapture.budget
    ReusableNative.budget PacketBank.lookupBudget
  nlinarith

end PCJ9eff70d512234a4c_Fixed.Materializer.NativeIndexedAtom
