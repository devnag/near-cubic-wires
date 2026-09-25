import Proof.Packets.DenseAtomLoop
import Proof.Packets.PhysicalCounterCopy
import Proof.Packets.ReflectedLiteralCache

/-! Reusable atom-table pass from the actual resident atom/code caches and
count master. It physically initializes the descending occurrence index,
executes every dense write, and returns both cache cursors to zero. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DenseAtomMaterialize
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsRawPairSeek (Pair cacheWord)
open PacketVector (Packet)
open DenseAtomProgram (table codes codePrefix)

def H (pos : Nat) (i : Fin 46) : Nat :=
  Fin.addCases (m:=45) (n:=1) (motive:=fun _=>Nat) (NativeIndexedAtom.heads 0 pos) (fun _=>1) i
def A (C R tag : Nat) (cs : List Pair) (ps : List Packet) (index : Nat) (i : Fin 46) : List Bool :=
  Fin.addCases (m:=45) (n:=1) (motive:=fun _=>List Bool)
    (NativeIndexedAtom.data C R (cacheWord cs) (codes tag cs) (PacketVector.bank R ps) index)
    (fun _=>ZeroPadding.pad R (CompareMachine.word cs.length)) i

def indexSlot : Fin 1→Fin 46 := ![44]
def backSlots : Fin 2→Fin 46 := ![33,40]
noncomputable def copy := PhysicalCounterCopy.machine (t:=46) 33 45 44
noncomputable def decrement := RecoveryFocus.machine indexSlot VectorCounter.decrement
noncomputable def back := RecoveryFocus.machine backSlots Completion.PhysicalBoundedLeftRewind.machine
noncomputable def machine := Composition.machine copy
  (Composition.machine decrement (Composition.machine DenseAtomProgram.machine back))
def budget (C R count : Nat) := 4*R+2*count+DenseAtomProgram.budget C R count+18

theorem codes_reflected (tag : Nat) (cs : List Pair) :
    codes tag cs=ReflectedLiteralCache.stream tag cs.length := by
  unfold codes DenseAtomProgram.codeList ReflectedLiteralCache.stream ReflectedLiteralCache.descending
  simp only [List.flatMap_map]
  apply List.flatMap_congr
  intro j _
  rw [NativeLiteralCode.word_native]
  rfl

theorem prefix_zero (tag : Nat) (cs : List Pair) : codePrefix tag cs 0=[] := by
  simp [codePrefix]
theorem prefix_final (tag : Nat) (cs : List Pair) : codePrefix tag cs cs.length=codes tag cs := by
  simp only [codePrefix,←DenseAtomProgram.codeList_length tag cs,List.take_length]
  rfl

theorem copy_run (C R tag : Nat) (cs : List Pair) (ps : List Packet) (hR : cs.length+1≤R) :
    Step copy (2*R+10) (H 0) (A C R tag cs ps 0) (H 0) (A C R tag cs ps cs.length) := by
  have h:=PhysicalCounterCopy.run R (33 : Fin 46) 45 44 (by decide) (by decide) (by decide)
    (H 0) (A C R tag cs ps 0) rfl rfl rfl rfl
    (by simp [A,Fin.addCases,ZeroPadding.pad_length,CompareMachine.word,hR])
    (by simp [A,NativeIndexedAtom.data,Fin.addCases,ZeroPadding.pad_length,CompareMachine.word];omega)
  apply h.congr rfl
  funext i
  fin_cases i <;>rfl

theorem decrement_run (C R tag : Nat) (cs : List Pair) (ps : List Packet) (hR : cs.length+1≤R) :
    Step decrement (2*cs.length+3) (H 0) (A C R tag cs ps cs.length)
      (H 0) (A C R tag cs ps (cs.length-1)) := by
  apply PhysicalFocusBoundary.focus (DescendingWindowCounters.decrement_run cs.length R hR) indexSlot (by decide)
    (H 0) (H 0) (A C R tag cs ps cs.length) (A C R tag cs ps (cs.length-1))
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;rfl
  · intro i away
    fin_cases i <;>first | exact ⟨rfl,rfl⟩ | exact False.elim (away 0 rfl)

theorem back_run (C R tag : Nat) (cs : List Pair) (ps : List Packet)
    (hcodes : (codes tag cs).length≤R) :
    Step back (2*R+2) (H (codes tag cs).length) (A C R tag cs ps 0)
      (H 0) (A C R tag cs ps 0) := by
  obtain ⟨r,rr,rf,_⟩:=Completion.PhysicalBoundedLeftRewind.run R (codes tag cs).length (codes tag cs) hcodes
  have h:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  apply PhysicalFocusBoundary.focus h backSlots (by decide)
    (H (codes tag cs).length) (H 0) (A C R tag cs ps 0) (A C R tag cs ps 0)
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i away
    fin_cases i <;>first | exact ⟨rfl,rfl⟩ | exact False.elim (away 1 rfl)

theorem run (C R tag : Nat) (cs : List Pair) (initial : List Packet)
    (hR : C+2≤R) (hcount : cs.length≤C) (hcodes : ∀i<cs.length,Nat.pair tag i<C)
    (hcache : (cacheWord cs).length≤R) (hcodeword : (codes tag cs).length≤R)
    (hinit : initial.length=C) (hinits : ∀P∈initial,PacketVector.Fits R P)
    (hcopy : ∀p∈cs,CloseoutRowsRawPairCopy.budget p≤R+3)
    (hfits : ∀p∈cs,∀m∈p.1++p.2,∀i∈m,i<C)
    (hdata : ∀p∈cs,∀i,(NativeNormalized.A C (p.1++p.2) [] i).length≤R)
    (hfuel : ∀p∈cs,NativeNormalized.budget C (p.1++p.2)+3≤R) :
    Step machine (budget C R cs.length) (H 0) (A C R tag cs initial 0)
      (H 0) (A C R tag cs (table C tag cs initial cs.length) 0) := by
  have loop:=(DenseAtomProgram.run C R tag cs initial hR hcount hcodes hcache hinit hinits
    hcopy hfits hdata hfuel).pad (fun i : Fin 46=>if i=45 then R else 0)
  have loop' : Step DenseAtomProgram.machine (DenseAtomProgram.budget C R cs.length)
      (H 0) (A C R tag cs initial (cs.length-1))
      (H (codes tag cs).length) (A C R tag cs (table C tag cs initial cs.length) 0) := by
    convert loop using 1 <;>
      (funext i;fin_cases i <;>simp [H,A,DenseAtomProgram.H,DenseAtomProgram.A,
        DenseAtomProgram.index,DenseAtomProgram.table,prefix_zero,prefix_final,Fin.addCases,ZeroPadding.pad_zero])
  have whole:=(copy_run C R tag cs initial (by omega)).seq
    ((decrement_run C R tag cs initial (by omega)).seq
      (loop'.seq (back_run C R tag cs (table C tag cs initial cs.length) hcodeword)))
  have fuel : (2*R+10)+1+((2*cs.length+3)+1+(DenseAtomProgram.budget C R cs.length+1+(2*R+2)))=
      budget C R cs.length := by unfold budget;omega
  simpa only [machine,fuel] using whole

end PCJ9eff70d512234a4c_Fixed.Materializer.DenseAtomMaterialize
