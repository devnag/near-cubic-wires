import Proof.Packets.NativeAtomTransaction
import Proof.Packets.NativePairSeekReady
import Proof.Packets.DescendingWindowCounters
import Proof.Packets.PhysicalBoundedLeftRewind

/-! Actual descending atom iteration over the unchanged ascending native
pair cache: seek by the physical occurrence counter, materialize/store the
atom at its parsed sparse code, rewind the cache, then decrement occurrence.
The dense-bank and cache words remain on their original tapes. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NativeIndexedAtom
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsRawPairSeek (Pair word cacheWord)

def heads (pairPos codePos : Nat) (i : Fin 45) : Nat :=
  Fin.addCases (m:=44) (n:=1) (motive:=fun _=>Nat) (NativeAtomStore.heads pairPos codePos 0) (fun _=>1) i
def data (C R : Nat) (pairs codes bank : List Bool) (index : Nat) (i : Fin 45) : List Bool :=
  Fin.addCases (m:=44) (n:=1) (motive:=fun _=>List Bool)
    (NativeAtomStore.data C R pairs codes bank [] 0)
    (fun _=>ZeroPadding.pad R (CompareMachine.word index)) i

def seekSlots : Fin 2→Fin 45 := ![44,36]
def backSlots : Fin 2→Fin 45 := ![33,36]
def indexSlot : Fin 1→Fin 45 := ![44]
noncomputable def seek := RecoveryFocus.machine seekSlots NativePairSeekReady.machine
noncomputable def back := RecoveryFocus.machine backSlots Completion.PhysicalBoundedLeftRewind.machine
noncomputable def decrement := RecoveryFocus.machine indexSlot VectorCounter.decrement
noncomputable def machine := Composition.machine seek
  (Composition.machine (TapeEmbedding.machine 1 NativeAtomStore.transaction)
    (Composition.machine back decrement))
def budget (C R code : Nat) (pre : List Pair) (p : Pair) := NativePairSeekReady.budget pre+1+
  (NativeAtomStore.transactionBudget C R code p+1+((2*R+2)+1+(2*pre.length+3)))

theorem seek_run (C R codePos : Nat) (pre : List Pair) (tail codes bank : List Bool)
    (hR : pre.length+2≤R) :
    Step seek (NativePairSeekReady.budget pre) (heads 0 codePos)
      (data C R (cacheWord pre++tail) codes bank pre.length)
      (heads (cacheWord pre).length codePos) (data C R (cacheWord pre++tail) codes bank pre.length) := by
  apply PhysicalFocusBoundary.focus (NativePairSeekReady.run R pre tail hR) seekSlots (by decide)
    (heads 0 codePos) (heads (cacheWord pre).length codePos)
    (data C R (cacheWord pre++tail) codes bank pre.length)
    (data C R (cacheWord pre++tail) codes bank pre.length)
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i away
    fin_cases i <;>first | exact ⟨rfl,rfl⟩ | exact False.elim (away 1 rfl)

theorem back_run (C R pos codePos index : Nat) (pairs codes bank : List Bool) (hp : pos≤R) :
    Step back (2*R+2) (heads pos codePos) (data C R pairs codes bank index)
      (heads 0 codePos) (data C R pairs codes bank index) := by
  obtain ⟨r,rr,rf,_⟩:=Completion.PhysicalBoundedLeftRewind.run R pos pairs hp
  have h:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  apply PhysicalFocusBoundary.focus h backSlots (by decide)
    (heads pos codePos) (heads 0 codePos) (data C R pairs codes bank index) (data C R pairs codes bank index)
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i away
    fin_cases i <;>first | exact ⟨rfl,rfl⟩ | exact False.elim (away 1 rfl)

theorem decrement_run (C R codePos index : Nat) (pairs codes bank : List Bool) (hi : index+1≤R) :
    Step decrement (2*index+3) (heads 0 codePos) (data C R pairs codes bank index)
      (heads 0 codePos) (data C R pairs codes bank (index-1)) := by
  apply PhysicalFocusBoundary.focus (DescendingWindowCounters.decrement_run index R hi) indexSlot (by decide)
    (heads 0 codePos) (heads 0 codePos) (data C R pairs codes bank index) (data C R pairs codes bank (index-1))
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;rfl
  · intro i away
    fin_cases i <;>first | exact ⟨rfl,rfl⟩ | exact False.elim (away 0 rfl)

theorem run (C R code : Nat) (pre : List Pair) (pairPost codePre codePost bankPre oldPayload oldCount bankPost : List Bool)
    (p : Pair) (hC : C≤R) (hR : pre.length+2≤R)
    (hcopy : CloseoutRowsRawPairCopy.budget p≤R+3)
    (hfits : ∀m∈p.1++p.2,∀i∈m,i<C)
    (hdata : ∀i,(NativeNormalized.A C (p.1++p.2) [] i).length≤R)
    (hfuel : NativeNormalized.budget C (p.1++p.2)+3≤R)
    (hpre : bankPre.length=2*code*R) (hop : oldPayload.length=R) (hoc : oldCount.length=R)
    (hp : (NativeAtomStore.answer C p).flatten.length≤R)
    (hc : (NativeAtomStore.answer C p).length+1≤R) (hi : code+1≤R)
    (hcache : (cacheWord pre).length+(word p).length≤R) :
    Step machine (budget C R code pre p) (heads 0 codePre.length)
      (data C R (cacheWord pre++word p++pairPost) (codePre++NativeLiteralCode.word code++codePost)
        (bankPre++oldPayload++oldCount++bankPost) pre.length)
      (heads 0 (codePre.length+code+6))
      (data C R (cacheWord pre++word p++pairPost) (codePre++NativeLiteralCode.word code++codePost)
        (NativeAtomStore.updatedBank C R p bankPre bankPost) (pre.length-1)) := by
  let pairs:=cacheWord pre++word p++pairPost
  let codes:=codePre++NativeLiteralCode.word code++codePost
  let before:=bankPre++oldPayload++oldCount++bankPost
  let after:=NativeAtomStore.updatedBank C R p bankPre bankPost
  have first:=seek_run C R codePre.length pre (word p++pairPost) codes before hR
  have second:=(NativeAtomStore.transaction_run C R code (cacheWord pre) pairPost codePre codePost
    bankPre oldPayload oldCount bankPost p hC (by omega) hcopy hfits hdata hfuel hpre hop hoc hp hc hi).embed
    (fun _ : Fin 1=>1) (fun _=>ZeroPadding.pad R (CompareMachine.word pre.length))
  have second' : Step (TapeEmbedding.machine 1 NativeAtomStore.transaction)
      (NativeAtomStore.transactionBudget C R code p)
      (heads (cacheWord pre).length codePre.length) (data C R pairs codes before pre.length)
      (heads ((cacheWord pre).length+(word p).length) (codePre.length+code+6))
      (data C R pairs codes after pre.length) := second
  have third:=back_run C R ((cacheWord pre).length+(word p).length) (codePre.length+code+6)
    pre.length pairs codes after hcache
  have last:=decrement_run C R (codePre.length+code+6) pre.length pairs codes after (by omega)
  have rest:=second'.seq (third.seq last)
  simp only [pairs,List.append_assoc] at rest
  simpa only [machine,budget,pairs,codes,before,after,List.append_assoc] using first.seq rest

end PCJ9eff70d512234a4c_Fixed.Materializer.NativeIndexedAtom
