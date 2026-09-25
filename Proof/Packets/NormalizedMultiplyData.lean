import Proof.Packets.MaskProductReady
import Proof.Packets.MaskProductEncoding
import Proof.Packets.NormalizerCold

/-! Fixed physical ports for support-product production followed by cold
ordered normalization. Operands, counts, and two width templates are the
only nonconstant entry data. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NormalizedMultiply
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.ExtDecompositionBatch

def productSlots : Fin 9→Fin 30 := ![24,25,26,0,3,27,28,13,29]
def extraHeads : Fin 6→Nat := ![1,0,0,1,1,0]
def extras (B : Nat) (left right : List (List Bool)) : Fin 6→List Bool :=
  ![UnaryTemplate.tape B,left.flatten,right.flatten,CompareMachine.word right.length,
    CompareMachine.word left.length,[]]
def heads (i : Fin 30) : Nat := Fin.addCases (m:=24) (n:=6) (motive:=fun _=>Nat) NormalizeCold.heads extraHeads i
def data (B : Nat) (left right raw : List (List Bool)) : Fin 30→List Bool :=
  fun i=>Fin.addCases (m:=24) (n:=6) (motive:=fun _=>List Bool) (NormalizeCold.data B raw) (extras B left right) i
noncomputable def productMachine := RecoveryFocus.machine productSlots MaskProduct.readyMachine
noncomputable def normalizeMachine := TapeEmbedding.machine 6 NormalizeCold.machine
noncomputable def machine := Composition.machine productMachine normalizeMachine
noncomputable def entry (B : Nat) (left right : List (List Bool)) :=
  Normalize.started machine heads (data B left right [])
def budget (B : Nat) (left right : List (List Bool)) :=
  MaskProduct.readyBudget B left.length right.length+1+
    NormalizeCold.budget B (MaskProduct.unions left right)

theorem unions_width (B : Nat) (left right : List (List Bool))
    (hl : ∀ bits∈left,bits.length=B) (hr : ∀ bits∈right,bits.length=B) :
    ∀ bits∈MaskProduct.unions left right,bits.length=B := by
  intro bits hb
  obtain ⟨m,hm,hb⟩ := List.mem_flatMap.mp hb
  obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hb
  simp [MaskProduct.values,PhysicalSupportUnion.values,hl m hm,hr n hn]

theorem product_step (B : Nat) (left right : List (List Bool))
    (hl : ∀ bits∈left,bits.length=B) (hr : ∀ bits∈right,bits.length=B) :
    Step productMachine (MaskProduct.readyBudget B left.length right.length)
      heads (data B left right []) heads (data B left right (MaskProduct.unions left right)) := by
  have h := MaskProduct.ready_run B left right [] [] [] [] [] hl hr
  have he : MaskProduct.products left right=
      SuffixScan.stream (Normalize.records (MaskProduct.unions left right)) := MaskProduct.products_stream left right
  refine PhysicalFocusBoundary.focus h productSlots (by decide) heads heads
    (data B left right []) (data B left right (MaskProduct.unions left right)) ?_ ?_ ?_ ?_ ?_
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> simp [data,productSlots,extras,NormalizeCold.data,
      Normalize.records,SuffixScan.stream,Fin.addCases,MaskProduct.readyA]
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> simp [data,productSlots,extras,NormalizeCold.data,
      Fin.addCases,MaskProduct.readyA,MaskProduct.unions_length,he]
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

end PCJ9eff70d512234a4c_Fixed.Materializer.NormalizedMultiply
