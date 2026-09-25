import Proof.Packets.TranscriptColumnRewind

/-! Complete physical extraction of one transcript coordinate: seek with the
actual candidate driver, collect in time order, and rewind both transcript
and output cursors. All three resident unary drivers are restored. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.TranscriptColumn
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def heads (sourcePos targetPos : Nat) : Fin 9 → Nat :=
  Fin.addCases (m:=8) (n:=1) (motive:=fun _=>Nat)
    (Fin.addCases (m:=7) (n:=1) (motive:=fun _=>Nat) (H sourcePos targetPos) (fun _=>1)) (fun _=>1)
def tapes (R N T column : Nat) (source payload count target : List Bool) : Fin 9 → List Bool :=
  Fin.addCases (m:=8) (n:=1) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=7) (n:=1) (motive:=fun _=>List Bool)
      (A R N source payload count target) (fun _=>CompareMachine.word T))
    (fun _=>CompareMachine.word column)
def candidateSlots : Fin 6 → Fin 9 := ![0,1,2,3,8,5]
def outputSlots : Fin 6 → Fin 9 := ![0,6,2,3,7,5]
def seekCandidate := RecoveryFocus.machine candidateSlots PacketBank.seek
def backCandidate := RecoveryFocus.machine candidateSlots PacketBank.back
def backOutput := RecoveryFocus.machine outputSlots PacketBank.back

theorem candidate_focus {states fuel : Nat} (program : Machine 6 states)
    (R N T column sourcePos resultPos targetPos : Nat) (source payload count target : List Bool)
    (small : Step program fuel (PacketBank.H sourcePos 1) (PacketBank.A R column source payload count)
      (PacketBank.H resultPos 1) (PacketBank.A R column source payload count)) :
    Step (RecoveryFocus.machine candidateSlots program) fuel (heads sourcePos targetPos)
      (tapes R N T column source payload count target) (heads resultPos targetPos)
      (tapes R N T column source payload count target) := by
  apply PhysicalFocusBoundary.focus small candidateSlots (by decide)
    (heads sourcePos targetPos) (heads resultPos targetPos) _ _
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro i away;fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 1 rfl)

private theorem output_heads (sourcePos targetPos : Nat) :
    ∀i,PacketBank.H targetPos 1 i=heads sourcePos targetPos (outputSlots i) := by
  intro i;fin_cases i <;> rfl

private theorem output_tapes (R N T column : Nat) (source payload count target : List Bool) :
    ∀i,PacketBank.A R T target payload count i=
      tapes R N T column source payload count target (outputSlots i) := by
  intro i;fin_cases i <;> rfl

private theorem output_outside (sourcePos oldPos newPos R N T column : Nat)
    (source payload count target : List Bool) :
    ∀i,(∀j,outputSlots j≠i)→
      heads sourcePos oldPos i=heads sourcePos newPos i ∧
      tapes R N T column source payload count target i=tapes R N T column source payload count target i := by
  intro i away
  have hi : i≠6 := by intro he;subst i;exact away 1 rfl
  fin_cases i <;> simp_all [heads,H,Fin.addCases]

theorem output_focus {states fuel : Nat} (program : Machine 6 states)
    (R N T column sourcePos targetPos resultPos : Nat) (source payload count target : List Bool)
    (small : Step program fuel (PacketBank.H targetPos 1) (PacketBank.A R T target payload count)
      (PacketBank.H resultPos 1) (PacketBank.A R T target payload count)) :
    Step (RecoveryFocus.machine outputSlots program) fuel (heads sourcePos targetPos)
      (tapes R N T column source payload count target) (heads sourcePos resultPos)
      (tapes R N T column source payload count target) := by
  exact PhysicalFocusBoundary.focus small outputSlots (by decide)
    (heads sourcePos targetPos) (heads sourcePos resultPos)
    (tapes R N T column source payload count target) (tapes R N T column source payload count target)
    (output_heads sourcePos targetPos) (output_tapes R N T column source payload count target)
    (output_heads sourcePos resultPos) (output_tapes R N T column source payload count target)
    (output_outside sourcePos targetPos resultPos R N T column source payload count target)

theorem seek_candidate (R N T column sourcePos targetPos : Nat) (source payload count target : List Bool) :
    Step seekCandidate (column*(2*R+5)+3) (heads sourcePos targetPos)
      (tapes R N T column source payload count target) (heads (sourcePos+column*R) targetPos)
      (tapes R N T column source payload count target) :=
  candidate_focus PacketBank.seek R N T column sourcePos (sourcePos+column*R) targetPos
    source payload count target (PacketBank.seek_run R column sourcePos 1 source payload count)

theorem back_candidate (R N T column sourcePos targetPos : Nat) (source payload count target : List Bool) :
    Step backCandidate (column*(2*R+5)+3) (heads (sourcePos+column*R) targetPos)
      (tapes R N T column source payload count target) (heads sourcePos targetPos)
      (tapes R N T column source payload count target) :=
  candidate_focus PacketBank.back R N T column (sourcePos+column*R) sourcePos targetPos
    source payload count target (PacketBank.back_run R column sourcePos 1 source payload count)

theorem back_output (R N T column sourcePos targetPos : Nat) (source payload count target : List Bool) :
    Step backOutput (T*(2*R+5)+3) (heads sourcePos (targetPos+T*R))
      (tapes R N T column source payload count target) (heads sourcePos targetPos)
      (tapes R N T column source payload count target) :=
  output_focus PacketBank.back R N T column sourcePos (targetPos+T*R) targetPos
    source payload count target (PacketBank.back_run R T targetPos 1 target payload count)

def program := Composition.machine seekCandidate (Composition.machine seekCandidate
  (Composition.machine (TapeEmbedding.machine 1 loop)
    (Composition.machine backOutput (Composition.machine backOutput
      (Composition.machine (TapeEmbedding.machine 1 rewindRows)
        (Composition.machine backCandidate backCandidate))))))
def budget (R N T column : Nat) :=
  loopBudget R N T+rewindBudget R N T+4*column*(2*R+5)+2*T*(2*R+5)+25

theorem run (R N T : Nat) (rows : Nat → List PacketVector.Packet)
    (hlen : ∀i,(rows i).length=N) (column : Fin N) (target : List Bool)
    (old : PacketVector.Packet) (hfit : ∀i,∀P∈rows i,PacketVector.Fits R P)
    (hold : PacketVector.Fits R old) :
    Step program (budget R N T column.val) (heads 0 target.length)
      (tapes R N T column.val (PacketTranscript.prefixBank R rows T)
        (PacketVector.payload R old) (PacketVector.count R old) target)
      (heads 0 target.length)
      (tapes R N T column.val (PacketTranscript.prefixBank R rows T)
        (PacketVector.payload R (previous (rowPacket N rows hlen column) old T))
        (PacketVector.count R (previous (rowPacket N rows hlen column) old T))
        (target++PacketVector.bank R
          (List.ofFn (fun i : Fin T=>rowPacket N rows hlen column i.val)))) := by
  let source := PacketTranscript.prefixBank R rows T
  let P := previous (rowPacket N rows hlen column) old T
  let result := target++PacketVector.bank R (List.ofFn (fun i : Fin T=>rowPacket N rows hlen column i.val))
  have start := seek_candidate R N T column.val 0 target.length source
    (PacketVector.payload R old) (PacketVector.count R old) target
  have second := seek_candidate R N T column.val (column.val*R) target.length source
    (PacketVector.payload R old) (PacketVector.count R old) target
  have collect := (rows_run R N T rows hlen column target old hfit hold).embed
    (fun _ : Fin 1=>1) (fun _ : Fin 1=>CompareMachine.word column.val)
  have hlength : result.length=target.length+T*(2*R) := by
    dsimp only [result]
    rw [List.length_append,PacketVector.bank_length]
    · rw [List.length_ofFn];ring
    · intro Q hQ
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hQ
      exact rowPacket_fits R N rows hlen column hfit i.val
  have backOne := back_output R N T column.val (column.val*(2*R)+T*(N*(2*R)))
    (target.length+T*R) source (PacketVector.payload R P) (PacketVector.count R P) result
  have backTwo := back_output R N T column.val (column.val*(2*R)+T*(N*(2*R)))
    target.length source (PacketVector.payload R P) (PacketVector.count R P) result
  have restore := (rewind_rows R N T (column.val*(2*R)) target.length
    source (PacketVector.payload R P) (PacketVector.count R P) result).embed
    (fun _ : Fin 1=>1) (fun _ : Fin 1=>CompareMachine.word column.val)
  have finalOne := back_candidate R N T column.val (column.val*R) target.length source
    (PacketVector.payload R P) (PacketVector.count R P) result
  have finalTwo := back_candidate R N T column.val 0 target.length source
    (PacketVector.payload R P) (PacketVector.count R P) result
  have colPos : column.val*R+column.val*R=column.val*(2*R) := by ring
  have outPos : target.length+T*R+T*R=result.length := by rw [hlength];ring
  simp only [Nat.zero_add] at start finalTwo
  rw [colPos] at second finalOne
  rw [outPos] at backOne
  have collect' : Step (TapeEmbedding.machine 1 loop) (loopBudget R N T)
      (heads (column.val*(2*R)) target.length)
      (tapes R N T column.val source (PacketVector.payload R old) (PacketVector.count R old) target)
      (heads (column.val*(2*R)+T*(N*(2*R))) result.length)
      (tapes R N T column.val source (PacketVector.payload R P) (PacketVector.count R P) result) := collect
  have restore' : Step (TapeEmbedding.machine 1 rewindRows) (rewindBudget R N T)
      (heads (column.val*(2*R)+T*(N*(2*R))) target.length)
      (tapes R N T column.val source (PacketVector.payload R P) (PacketVector.count R P) result)
      (heads (column.val*(2*R)) target.length)
      (tapes R N T column.val source (PacketVector.payload R P) (PacketVector.count R P) result) := restore
  have whole := start.seq (second.seq (collect'.seq (backOne.seq (backTwo.seq
    (restore'.seq (finalOne.seq finalTwo))))))
  have fuel : (column.val*(2*R+5)+3)+1+((column.val*(2*R+5)+3)+1+
      (loopBudget R N T+1+((T*(2*R+5)+3)+1+((T*(2*R+5)+3)+1+
      (rewindBudget R N T+1+((column.val*(2*R+5)+3)+1+(column.val*(2*R+5)+3)))))))=
      budget R N T column.val := by unfold budget;ring
  simpa only [program,fuel,source,P,result] using whole

end
end PCJ9eff70d512234a4c_Fixed.Materializer.TranscriptColumn
