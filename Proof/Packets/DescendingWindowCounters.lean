import Proof.Packets.VectorCounterDecrement

/-! Actual descending inner-window coordinates: decrement the unary
elementary degree and increment its framed binary complement. Both counters
and the retained physical log return to head zero. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindowCounters
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairOrdinary.SignedSortKey

noncomputable def unary := Composition.machine
  (Composition.machine (Completion.PhysicalDriverMoves.machine 1 .right) VectorCounter.decrement)
  (Completion.PhysicalDriverMoves.machine 1 .left)

theorem decrement_zero : Step VectorCounter.decrement 3 (fun _=>1) (fun _=>CompareMachine.word 0)
    (fun _=>1) (fun _=>CompareMachine.word 0) := by
  have a : Timed VectorCounter.decrement 1
      (VectorCounter.dcfg 0 (CompareMachine.word 0) 1)
      (VectorCounter.dcfg 1 (CompareMachine.word 0) 0) := Timed.single (by rfl) (by rfl)
  have b : Timed VectorCounter.decrement 1
      (VectorCounter.dcfg 1 (CompareMachine.word 0) 0)
      (VectorCounter.dcfg 2 (CompareMachine.word 0) 0) := Timed.single (by rfl) (by rfl)
  have c : Timed VectorCounter.decrement 1
      (VectorCounter.dcfg 2 (CompareMachine.word 0) 0)
      (VectorCounter.dcfg 3 (CompareMachine.word 0) 1) := Timed.single (by rfl) (by rfl)
  obtain ⟨r,hr,hf,_⟩:=(a.trans (b.trans c)).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

theorem decrement_run (a C : Nat) (hC : a+1≤C) :
    Step VectorCounter.decrement (2*a+3) (fun _=>1)
      (fun _=>ZeroPadding.pad C (CompareMachine.word a))
      (fun _=>1) (fun _=>ZeroPadding.pad C (CompareMachine.word (a-1))) := by
  cases a with
  | zero=>exact decrement_zero.pad (fun _=>C)
  | succ n=>exact (VectorCounter.decrement_padded n C hC).enlarge (by omega)

theorem unary_run (a C : Nat) (hC : a+1≤C) :
    Step unary (2*a+7) (fun _=>0) (fun _=>ZeroPadding.pad C (CompareMachine.word a))
      (fun _=>0) (fun _=>ZeroPadding.pad C (CompareMachine.word (a-1))) := by
  have up := Completion.PhysicalDriverMoves.run .right (fun _ : Fin 1=>0)
    (fun _=>ZeroPadding.pad C (CompareMachine.word a))
  have mid := decrement_run a C hC
  have down := Completion.PhysicalDriverMoves.run .left (fun _ : Fin 1=>1)
    (fun _=>ZeroPadding.pad C (CompareMachine.word (a-1)))
  have whole:=(up.seq mid).seq down
  convert whole using 1 <;> first | rfl | omega

def data (u a b C : Nat) : Fin 3→List Bool :=
  ![ZeroPadding.pad C (CompareMachine.word a),ZeroPadding.pad C (frame (binary u b)),List.replicate (C+1) false]
def unarySlots : Fin 1→Fin 3 := ![0]
def binarySlots : Fin 2→Fin 3 := ![1,2]
noncomputable def unaryPart := RecoveryFocus.machine unarySlots unary
noncomputable def binaryPart := RecoveryFocus.machine binarySlots FramedIncrement.machine
noncomputable def machine := Composition.machine unaryPart binaryPart

theorem unaryPart_run (u a b C : Nat) (hC : a+1≤C) :
    Step unaryPart (2*a+7) (fun _=>0) (data u a b C)
      (fun _=>0) (data u (a-1) b C) := by
  apply PhysicalFocusBoundary.focus (unary_run a C hC) unarySlots (by decide)
    (fun _=>0) (fun _=>0) (data u a b C) (data u (a-1) b C)
  · intro i;rfl
  · intro i;fin_cases i;rfl
  · intro i;rfl
  · intro i;fin_cases i;rfl
  · intro i away
    fin_cases i
    · exact False.elim (away 0 rfl)
    · exact ⟨rfl,rfl⟩
    · exact ⟨rfl,rfl⟩

theorem binaryPart_run (u a b C : Nat) (hb : b+1<2^u) (hC : 2*u≤C) :
    Step binaryPart (4*u+2) (fun _=>0) (data u a b C)
      (fun _=>0) (data u a (b+1) C) := by
  obtain ⟨r,hr,h0,h1,hh,_,_⟩:=FramedIncrement.increment_run u b (C+1) hb (by omega)
  have hin : (Fin.addCases (m:=1) (n:=1) (motive:=fun _=>List Bool)
      (fun _=>frame (binary u b)) (fun _=>List.replicate (C+1) false))=
      (![frame (binary u b),List.replicate (C+1) false] : Fin 2→List Bool) := by
    funext i;fin_cases i <;> rfl
  rw [hin] at hr
  have raw : Step FramedIncrement.machine (4*u+2) (fun _=>0)
      ![frame (binary u b),List.replicate (C+1) false]
      (fun _=>0) ![frame (binary u (b+1)),List.replicate (C+1) false] := by
    apply Step.of_run hr (funext hh)
    funext i;fin_cases i
    · exact h0
    · exact h1
  have padded := raw.pad (![C,0] : Fin 2→Nat)
  apply PhysicalFocusBoundary.focus padded binarySlots (by decide)
    (fun _=>0) (fun _=>0) (data u a b C) (data u a (b+1) C)
  · intro i;rfl
  · intro i;fin_cases i
    · rfl
    · exact ZeroPadding.pad_zero _
  · intro i;rfl
  · intro i;fin_cases i
    · rfl
    · exact ZeroPadding.pad_zero _
  · intro i away
    fin_cases i
    · exact ⟨rfl,rfl⟩
    · exact False.elim (away 0 rfl)
    · exact False.elim (away 1 rfl)

theorem run (u a b C : Nat) (ha : a+1≤C) (hb : b+1<2^u) (hC : 2*u≤C) :
    Step machine (2*a+4*u+10) (fun _=>0) (data u a b C)
      (fun _=>0) (data u (a-1) (b+1) C) := by
  have h:=(unaryPart_run u a b C ha).seq (binaryPart_run u (a-1) b C hb hC)
  convert h using 1 <;> first | rfl | omega

end PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindowCounters
