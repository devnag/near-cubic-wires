import Proof.Packets.PacketsXCycleNormalizeTyped

/-! Serialize an already computed flat monomial bank without normalizing it
again. The physical initializer writes the index mark and raises all three
unary cursors; the resulting literal monomial order is preserved. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace Theorem25Completion.CycleFlatSerialize
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed
noncomputable section

def boot : Machine 5 3 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==2
  rule := fun q _=>if q=0 then some ⟨1,fun _=>none,![.right,.stay,.right,.stay,.right]⟩
    else if q=1 then some ⟨2,![none,none,some true,none,none],fun _=>.stay⟩ else none
def heads (out : List Bool) : Fin 5→Nat := ![0,0,0,out.length,0]
def readyHeads (out : List Bool) : Fin 5→Nat := ![1,0,1,out.length,1]
def input (B R : Nat) (rows : List (List Bool)) (out : List Bool) : Fin 5→List Bool :=
  ![UnaryTemplate.tape B,rows.flatten,List.replicate R false,out,CompareMachine.word rows.length]
def readyInput (B R : Nat) (rows : List (List Bool)) (out : List Bool) : Fin 5→List Bool :=
  ![UnaryTemplate.tape B,rows.flatten,ZeroPadding.pad R (UnaryTemplate.tape 1),out,CompareMachine.word rows.length]

theorem write_index (R : Nat) (hR : 3≤R) :
    writeTapeBit (List.replicate R false) 1 true=ZeroPadding.pad R (UnaryTemplate.tape 1) := by
  have he : R-3+3=R := by omega
  simpa only [he] using CycleSerializerBoot.index_write (R-3)

theorem boot_run (B R : Nat) (rows : List (List Bool)) (out : List Bool) (hR : 3≤R) :
    Step boot 2 (heads out) (input B R rows out) (readyHeads out) (readyInput B R rows out) := by
  let first : Configuration 5 3 := ⟨0,heads out,input B R rows out⟩
  let middle : Configuration 5 3 := ⟨1,readyHeads out,input B R rows out⟩
  let last : Configuration 5 3 := ⟨2,readyHeads out,readyInput B R rows out⟩
  have h1 : step boot first=some middle := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;>rfl
    · rfl
  have h2 : step boot middle=some last := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;>rfl
    · funext i;fin_cases i <;>first | rfl | exact write_index R hR
  obtain ⟨r,hr,hf,_⟩ := ((Timed.single (by rfl) h1).trans (Timed.single (by rfl) h2)).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

def indexReserve (R : Nat) : Fin 5→Nat := ![0,0,R,0,0]
def word (rows : List (List Bool)) := ExtIncidence.stream (rows.map (PhysicalMaskIndices.selectedIndices 0))
def ending (B : Nat) (rows : List (List Bool)) (out : List Bool) :=
  PhysicalPolynomialSerialize.ending B rows.flatten rows.flatten.length (out++word rows) rows.length
def output (B R : Nat) (rows : List (List Bool)) (out : List Bool) :=
  fun i=>ZeroPadding.pad (indexReserve R i) ((ending B rows out).tapes i)
def machine := Composition.machine boot PhysicalPolynomialSerialize.machine
def budget (B : Nat) (rows : List (List Bool)) := rows.length*(B^2+8*B+9)+8

theorem pad_nested (C R : Nat) (bits : List Bool) (h : C≤R) :
    ZeroPadding.pad R (ZeroPadding.pad C bits)=ZeroPadding.pad R bits := by
  simp only [ZeroPadding.pad,List.length_append,List.length_replicate,List.append_assoc,←List.replicate_add]
  congr 1
  congr 1
  omega

theorem run (B R : Nat) (rows : List (List Bool)) (out : List Bool)
    (hR : B+3≤R) (hw : ∀ row∈rows,row.length=B) :
    Step machine (budget B rows) (heads out) (input B R rows out)
      (ending B rows out).heads (output B R rows out) := by
  have h := (PhysicalPolynomialSerialize.stream_step B [] rows [] out hw).pad (indexReserve R)
  simp only [List.nil_append,List.append_nil,List.length_nil,Nat.zero_add] at h
  have hi : (fun i=>ZeroPadding.pad (indexReserve R i)
      ((PhysicalPolynomialSerialize.input B rows.flatten 0 out rows.length).tapes i)) =
      readyInput B R rows out := by
    funext i
    fin_cases i <;>simp [indexReserve,PhysicalPolynomialSerialize.input,PhysicalPolynomialSerialize.cfg,
      PhysicalPolynomialSerialize.data,Composition.leftConfig,RepeatMachine.cfg,TapeEmbedding.config,
      controlConfig,Fin.addCases,readyInput,pad_nested (B+3) R _ hR]
  have hh : (PhysicalPolynomialSerialize.input B rows.flatten 0 out rows.length).heads=readyHeads out := by
    funext i
    fin_cases i <;>simp [PhysicalPolynomialSerialize.input,PhysicalPolynomialSerialize.cfg,
      PhysicalPolynomialSerialize.data,Composition.leftConfig,RepeatMachine.cfg,TapeEmbedding.config,
      controlConfig,Fin.addCases,readyHeads]
  have hs : Step PhysicalPolynomialSerialize.machine (rows.length*(B^2+8*B+9)+5)
      (readyHeads out) (readyInput B R rows out) (ending B rows out).heads (output B R rows out) :=
    h.congr_in hh hi
  have total := (boot_run B R rows out (by omega)).seq hs
  have ht : 2+1+(rows.length*(B^2+8*B+9)+5)=budget B rows := by unfold budget;omega
  rw [ht] at total
  exact total

theorem output_word (B R : Nat) (rows : List (List Bool)) (out : List Bool) :
    output B R rows out 3=out++word rows := by
  change ZeroPadding.pad 0 (out++word rows)=_
  exact ZeroPadding.pad_zero _

end
end Theorem25Completion.CycleFlatSerialize
