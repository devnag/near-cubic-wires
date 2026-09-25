import Proof.Packets.MaskAdditionReady
import Proof.Packets.MaskFrameEncoding
import Proof.Packets.NormalizerCold

/-! Fixed physical ports for raw-sum production followed by cold
ordered normalization. Operands, counts, and two width templates are the
only nonconstant entry data. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NormalizedAddition
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.ExtDecompositionBatch

def additionSlots : Fin 9→Fin 30 := ![24,25,26,0,3,27,28,13,29]
def extraHeads : Fin 6→Nat := ![1,0,0,1,1,0]
def extras (B : Nat) (left right : List (List Bool)) : Fin 6→List Bool :=
  ![UnaryTemplate.tape B,left.flatten,right.flatten,CompareMachine.word right.length,
    CompareMachine.word left.length,[]]
def heads (i : Fin 30) : Nat := Fin.addCases (m:=24) (n:=6) (motive:=fun _=>Nat) NormalizeCold.heads extraHeads i
def data (B : Nat) (left right raw : List (List Bool)) : Fin 30→List Bool :=
  fun i=>Fin.addCases (m:=24) (n:=6) (motive:=fun _=>List Bool) (NormalizeCold.data B raw) (extras B left right) i
noncomputable def additionMachine := RecoveryFocus.machine additionSlots MaskAddition.machine
noncomputable def normalizeMachine := TapeEmbedding.machine 6 NormalizeCold.machine
noncomputable def machine := Composition.machine additionMachine normalizeMachine
noncomputable def entry (B : Nat) (left right : List (List Bool)) :=
  Normalize.started machine heads (data B left right [])
def budget (B : Nat) (left right : List (List Bool)) :=
  MaskAddition.budget B left.length right.length+1+
    NormalizeCold.budget B (left.reverse++right)

theorem sum_width (B : Nat) (left right : List (List Bool))
    (hl : ∀ bits∈left,bits.length=B) (hr : ∀ bits∈right,bits.length=B) :
    ∀ bits∈left.reverse++right,bits.length=B := by
  intro bits hb
  rcases List.mem_append.mp hb with h|h
  · exact hl bits (List.mem_reverse.mp h)
  · exact hr bits h

theorem addition_step (B : Nat) (left right : List (List Bool))
    (hl : ∀ bits∈left,bits.length=B) (hr : ∀ bits∈right,bits.length=B) :
    Step additionMachine (MaskAddition.budget B left.length right.length)
      heads (data B left right []) heads (data B left right (left.reverse++right)) := by
  have h := MaskAddition.ready_run B left right [] [] [] [] [] hl hr
  have he : MaskAddition.records left right=
      SuffixScan.stream (Normalize.records (left.reverse++right)) := by
    rw [MaskAddition.records,←MaskFrame.records_append,MaskFrame.records_stream]
    rfl
  refine PhysicalFocusBoundary.focus h additionSlots (by decide) heads heads
    (data B left right []) (data B left right (left.reverse++right)) ?_ ?_ ?_ ?_ ?_
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> simp [data,additionSlots,extras,NormalizeCold.data,
      Normalize.records,SuffixScan.stream,Fin.addCases,MaskAddition.A,MaskProduct.readyA]
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> simp [data,additionSlots,extras,NormalizeCold.data,
      Fin.addCases,MaskProduct.readyA,MaskAddition.A,List.length_append,List.length_reverse,he]
  · intro i
    refine Fin.addCases (m:=24) (n:=6) (fun j=>?_) (fun j=>?_) i
    · intro hi
      by_cases h0 : j=0
      · subst j;exact False.elim (hi 3 rfl)
      by_cases h3 : j=3
      · subst j;exact False.elim (hi 4 rfl)
      exact ⟨rfl,by simp [data,Fin.addCases,NormalizeCold.data,h0,h3]⟩
    · intro _
      exact ⟨rfl,by simp only [data,Fin.addCases_right]⟩

end PCJ9eff70d512234a4c_Fixed.Materializer.NormalizedAddition
