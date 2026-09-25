import Proof.Packets.PacketsXWalkLiteralMastersTemplates

/-! Paid palette master construction from raw numeric words and the actual mask.
Every derived scalar, template, padding cell and zero seed word is produced by execution. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralMasters
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open Completion
noncomputable section
structure Bounds (C R root rank depth M : Nat) (mask : List Bool) : Prop where
  arena : 2*C+5≤R
  code : C+11≤R
  root : root≤R
  rank : rank+2≤R
  depth : depth+2≤R
  population : M+2≤R
  mask : mask.length≤R

def source (C root rank depth M : Nat) (mask : List Bool) : Fin 10→List Bool :=
  ![UnaryTemplate.tape (2*C+3),UnaryTemplate.tape C,List.replicate root true,
    List.replicate rank true,UnaryTemplate.tape rank,mask,List.replicate (C+9) true,
    UnaryTemplate.tape depth,UnaryTemplate.tape (C+9),UnaryTemplate.tape M]
def select : Fin 13→Option (Fin 10) :=
  ![some 0,some 1,some 2,some 3,none,none,none,some 4,some 5,some 6,some 7,some 8,some 9]
def slots10 : Fin 25→Fin 55 := ![29,27,2,3,33,6,25,35,37,39,41,42,43,44,45,46,47,48,49,50,51,52,53,1,54]
def phase10 := RecoveryFocus.machine slots10 (NativeFanout.machine select)
def bank10 (C R root rank depth M : Nat) (mask : List Bool) := install slots10 (bank9 C R root rank depth M mask)
  (NativeFanout.output select (source C root rank depth M mask) R)
theorem bank10_slot (C R root rank depth M : Nat) (mask : List Bool) (i : Fin 25) :
    bank10 C R root rank depth M mask (slots10 i)=NativeFanout.output select (source C root rank depth M mask) R i :=
  install_slot slots10 (by decide) _ _ i
theorem bank10_other (C R root rank depth M : Nat) (mask : List Bool) (i : Fin 55) (hi : ∀j,slots10 j≠i) :
    bank10 C R root rank depth M mask i=bank9 C R root rank depth M mask i := install_other slots10 _ _ _ hi

theorem source_length (C R root rank depth M : Nat) (mask : List Bool) (h : Bounds C R root rank depth M mask) :
    ∀i,(source C root rank depth M mask i).length≤R := by
  rcases h with ⟨ha,hc,hr,hk,hd,hm,hmask⟩
  intro i;fin_cases i <;>simp [source,UnaryTemplate.tape] <;>omega

theorem join10 (C R root rank depth M : Nat) (mask : List Bool) : ∀i,bank9 C R root rank depth M mask (slots10 i)=
    NativeFanout.input (m:=13) (source C root rank depth M mask) R i := by
  intro i;fin_cases i
  · change bank9 C R root rank depth M mask 29=NativeFanout.input (m:=13) (source C root rank depth M mask) R 0
    rw [bank9_other C R root rank depth M mask 29 (by decide)]
    rw [bank8_other C R root rank depth M mask 29 (by decide)]
    rw [bank7_other C R root rank depth M mask 29 (by decide)]
    rw [bank6_other C R root rank depth M mask 29 (by decide)]
    rw [bank5_other C R root rank depth M mask 29 (by decide)]
    change bank4 C R root rank depth M mask (slots4 1)=_
    rw [bank4_slot]
    rfl
  · change bank9 C R root rank depth M mask 27=NativeFanout.input (m:=13) (source C root rank depth M mask) R 1
    rw [bank9_other C R root rank depth M mask 27 (by decide)]
    rw [bank8_other C R root rank depth M mask 27 (by decide)]
    rw [bank7_other C R root rank depth M mask 27 (by decide)]
    rw [bank6_other C R root rank depth M mask 27 (by decide)]
    rw [bank5_other C R root rank depth M mask 27 (by decide)]
    rw [bank4_other C R root rank depth M mask 27 (by decide)]
    change bank3 C R root rank depth M mask (slots3 1)=_
    rw [bank3_slot]
    rfl
  · change bank9 C R root rank depth M mask 2=NativeFanout.input (m:=13) (source C root rank depth M mask) R 2
    rw [bank9_other C R root rank depth M mask 2 (by decide)]
    rw [bank8_other C R root rank depth M mask 2 (by decide)]
    rw [bank7_other C R root rank depth M mask 2 (by decide)]
    rw [bank6_other C R root rank depth M mask 2 (by decide)]
    rw [bank5_other C R root rank depth M mask 2 (by decide)]
    rw [bank4_other C R root rank depth M mask 2 (by decide)]
    rw [bank3_other C R root rank depth M mask 2 (by decide)]
    rw [bank2_other C R root rank depth M mask 2 (by decide)]
    rw [bank1_other C R root rank depth M mask 2 (by decide)]
    rfl
  · change bank9 C R root rank depth M mask 3=NativeFanout.input (m:=13) (source C root rank depth M mask) R 3
    rw [bank9_other C R root rank depth M mask 3 (by decide)]
    rw [bank8_other C R root rank depth M mask 3 (by decide)]
    rw [bank7_other C R root rank depth M mask 3 (by decide)]
    change bank6 C R root rank depth M mask (slots6 0)=_
    rw [bank6_slot]
    rfl
  · change bank9 C R root rank depth M mask 33=NativeFanout.input (m:=13) (source C root rank depth M mask) R 4
    rw [bank9_other C R root rank depth M mask 33 (by decide)]
    rw [bank8_other C R root rank depth M mask 33 (by decide)]
    rw [bank7_other C R root rank depth M mask 33 (by decide)]
    change bank6 C R root rank depth M mask (slots6 1)=_
    rw [bank6_slot]
    rfl
  · change bank9 C R root rank depth M mask 6=NativeFanout.input (m:=13) (source C root rank depth M mask) R 5
    rw [bank9_other C R root rank depth M mask 6 (by decide)]
    rw [bank8_other C R root rank depth M mask 6 (by decide)]
    rw [bank7_other C R root rank depth M mask 6 (by decide)]
    rw [bank6_other C R root rank depth M mask 6 (by decide)]
    rw [bank5_other C R root rank depth M mask 6 (by decide)]
    rw [bank4_other C R root rank depth M mask 6 (by decide)]
    rw [bank3_other C R root rank depth M mask 6 (by decide)]
    rw [bank2_other C R root rank depth M mask 6 (by decide)]
    rw [bank1_other C R root rank depth M mask 6 (by decide)]
    rfl
  · change bank9 C R root rank depth M mask 25=NativeFanout.input (m:=13) (source C root rank depth M mask) R 6
    rw [bank9_other C R root rank depth M mask 25 (by decide)]
    change bank8 C R root rank depth M mask (slots8 0)=_
    rw [bank8_slot]
    rfl
  · change bank9 C R root rank depth M mask 35=NativeFanout.input (m:=13) (source C root rank depth M mask) R 7
    rw [bank9_other C R root rank depth M mask 35 (by decide)]
    rw [bank8_other C R root rank depth M mask 35 (by decide)]
    change bank7 C R root rank depth M mask (slots7 1)=_
    rw [bank7_slot]
    rfl
  · change bank9 C R root rank depth M mask 37=NativeFanout.input (m:=13) (source C root rank depth M mask) R 8
    rw [bank9_other C R root rank depth M mask 37 (by decide)]
    change bank8 C R root rank depth M mask (slots8 1)=_
    rw [bank8_slot]
    rfl
  · change bank9 C R root rank depth M mask 39=NativeFanout.input (m:=13) (source C root rank depth M mask) R 9
    change bank9 C R root rank depth M mask (slots9 1)=_
    rw [bank9_slot]
    rfl
  · change bank9 C R root rank depth M mask 41=NativeFanout.input (m:=13) (source C root rank depth M mask) R 10
    rw [bank9_other C R root rank depth M mask 41 (by decide)]
    rw [bank8_other C R root rank depth M mask 41 (by decide)]
    rw [bank7_other C R root rank depth M mask 41 (by decide)]
    rw [bank6_other C R root rank depth M mask 41 (by decide)]
    rw [bank5_other C R root rank depth M mask 41 (by decide)]
    rw [bank4_other C R root rank depth M mask 41 (by decide)]
    rw [bank3_other C R root rank depth M mask 41 (by decide)]
    rw [bank2_other C R root rank depth M mask 41 (by decide)]
    rw [bank1_other C R root rank depth M mask 41 (by decide)]
    rfl
  · change bank9 C R root rank depth M mask 42=NativeFanout.input (m:=13) (source C root rank depth M mask) R 11
    rw [bank9_other C R root rank depth M mask 42 (by decide)]
    rw [bank8_other C R root rank depth M mask 42 (by decide)]
    rw [bank7_other C R root rank depth M mask 42 (by decide)]
    rw [bank6_other C R root rank depth M mask 42 (by decide)]
    rw [bank5_other C R root rank depth M mask 42 (by decide)]
    rw [bank4_other C R root rank depth M mask 42 (by decide)]
    rw [bank3_other C R root rank depth M mask 42 (by decide)]
    rw [bank2_other C R root rank depth M mask 42 (by decide)]
    rw [bank1_other C R root rank depth M mask 42 (by decide)]
    rfl
  · change bank9 C R root rank depth M mask 43=NativeFanout.input (m:=13) (source C root rank depth M mask) R 12
    rw [bank9_other C R root rank depth M mask 43 (by decide)]
    rw [bank8_other C R root rank depth M mask 43 (by decide)]
    rw [bank7_other C R root rank depth M mask 43 (by decide)]
    rw [bank6_other C R root rank depth M mask 43 (by decide)]
    rw [bank5_other C R root rank depth M mask 43 (by decide)]
    rw [bank4_other C R root rank depth M mask 43 (by decide)]
    rw [bank3_other C R root rank depth M mask 43 (by decide)]
    rw [bank2_other C R root rank depth M mask 43 (by decide)]
    rw [bank1_other C R root rank depth M mask 43 (by decide)]
    rfl
  · change bank9 C R root rank depth M mask 44=NativeFanout.input (m:=13) (source C root rank depth M mask) R 13
    rw [bank9_other C R root rank depth M mask 44 (by decide)]
    rw [bank8_other C R root rank depth M mask 44 (by decide)]
    rw [bank7_other C R root rank depth M mask 44 (by decide)]
    rw [bank6_other C R root rank depth M mask 44 (by decide)]
    rw [bank5_other C R root rank depth M mask 44 (by decide)]
    rw [bank4_other C R root rank depth M mask 44 (by decide)]
    rw [bank3_other C R root rank depth M mask 44 (by decide)]
    rw [bank2_other C R root rank depth M mask 44 (by decide)]
    rw [bank1_other C R root rank depth M mask 44 (by decide)]
    rfl
  · change bank9 C R root rank depth M mask 45=NativeFanout.input (m:=13) (source C root rank depth M mask) R 14
    rw [bank9_other C R root rank depth M mask 45 (by decide)]
    rw [bank8_other C R root rank depth M mask 45 (by decide)]
    rw [bank7_other C R root rank depth M mask 45 (by decide)]
    rw [bank6_other C R root rank depth M mask 45 (by decide)]
    rw [bank5_other C R root rank depth M mask 45 (by decide)]
    rw [bank4_other C R root rank depth M mask 45 (by decide)]
    rw [bank3_other C R root rank depth M mask 45 (by decide)]
    rw [bank2_other C R root rank depth M mask 45 (by decide)]
    rw [bank1_other C R root rank depth M mask 45 (by decide)]
    rfl
  · change bank9 C R root rank depth M mask 46=NativeFanout.input (m:=13) (source C root rank depth M mask) R 15
    rw [bank9_other C R root rank depth M mask 46 (by decide)]
    rw [bank8_other C R root rank depth M mask 46 (by decide)]
    rw [bank7_other C R root rank depth M mask 46 (by decide)]
    rw [bank6_other C R root rank depth M mask 46 (by decide)]
    rw [bank5_other C R root rank depth M mask 46 (by decide)]
    rw [bank4_other C R root rank depth M mask 46 (by decide)]
    rw [bank3_other C R root rank depth M mask 46 (by decide)]
    rw [bank2_other C R root rank depth M mask 46 (by decide)]
    rw [bank1_other C R root rank depth M mask 46 (by decide)]
    rfl
  · change bank9 C R root rank depth M mask 47=NativeFanout.input (m:=13) (source C root rank depth M mask) R 16
    rw [bank9_other C R root rank depth M mask 47 (by decide)]
    rw [bank8_other C R root rank depth M mask 47 (by decide)]
    rw [bank7_other C R root rank depth M mask 47 (by decide)]
    rw [bank6_other C R root rank depth M mask 47 (by decide)]
    rw [bank5_other C R root rank depth M mask 47 (by decide)]
    rw [bank4_other C R root rank depth M mask 47 (by decide)]
    rw [bank3_other C R root rank depth M mask 47 (by decide)]
    rw [bank2_other C R root rank depth M mask 47 (by decide)]
    rw [bank1_other C R root rank depth M mask 47 (by decide)]
    rfl
  · change bank9 C R root rank depth M mask 48=NativeFanout.input (m:=13) (source C root rank depth M mask) R 17
    rw [bank9_other C R root rank depth M mask 48 (by decide)]
    rw [bank8_other C R root rank depth M mask 48 (by decide)]
    rw [bank7_other C R root rank depth M mask 48 (by decide)]
    rw [bank6_other C R root rank depth M mask 48 (by decide)]
    rw [bank5_other C R root rank depth M mask 48 (by decide)]
    rw [bank4_other C R root rank depth M mask 48 (by decide)]
    rw [bank3_other C R root rank depth M mask 48 (by decide)]
    rw [bank2_other C R root rank depth M mask 48 (by decide)]
    rw [bank1_other C R root rank depth M mask 48 (by decide)]
    rfl
  · change bank9 C R root rank depth M mask 49=NativeFanout.input (m:=13) (source C root rank depth M mask) R 18
    rw [bank9_other C R root rank depth M mask 49 (by decide)]
    rw [bank8_other C R root rank depth M mask 49 (by decide)]
    rw [bank7_other C R root rank depth M mask 49 (by decide)]
    rw [bank6_other C R root rank depth M mask 49 (by decide)]
    rw [bank5_other C R root rank depth M mask 49 (by decide)]
    rw [bank4_other C R root rank depth M mask 49 (by decide)]
    rw [bank3_other C R root rank depth M mask 49 (by decide)]
    rw [bank2_other C R root rank depth M mask 49 (by decide)]
    rw [bank1_other C R root rank depth M mask 49 (by decide)]
    rfl
  · change bank9 C R root rank depth M mask 50=NativeFanout.input (m:=13) (source C root rank depth M mask) R 19
    rw [bank9_other C R root rank depth M mask 50 (by decide)]
    rw [bank8_other C R root rank depth M mask 50 (by decide)]
    rw [bank7_other C R root rank depth M mask 50 (by decide)]
    rw [bank6_other C R root rank depth M mask 50 (by decide)]
    rw [bank5_other C R root rank depth M mask 50 (by decide)]
    rw [bank4_other C R root rank depth M mask 50 (by decide)]
    rw [bank3_other C R root rank depth M mask 50 (by decide)]
    rw [bank2_other C R root rank depth M mask 50 (by decide)]
    rw [bank1_other C R root rank depth M mask 50 (by decide)]
    rfl
  · change bank9 C R root rank depth M mask 51=NativeFanout.input (m:=13) (source C root rank depth M mask) R 20
    rw [bank9_other C R root rank depth M mask 51 (by decide)]
    rw [bank8_other C R root rank depth M mask 51 (by decide)]
    rw [bank7_other C R root rank depth M mask 51 (by decide)]
    rw [bank6_other C R root rank depth M mask 51 (by decide)]
    rw [bank5_other C R root rank depth M mask 51 (by decide)]
    rw [bank4_other C R root rank depth M mask 51 (by decide)]
    rw [bank3_other C R root rank depth M mask 51 (by decide)]
    rw [bank2_other C R root rank depth M mask 51 (by decide)]
    rw [bank1_other C R root rank depth M mask 51 (by decide)]
    rfl
  · change bank9 C R root rank depth M mask 52=NativeFanout.input (m:=13) (source C root rank depth M mask) R 21
    rw [bank9_other C R root rank depth M mask 52 (by decide)]
    rw [bank8_other C R root rank depth M mask 52 (by decide)]
    rw [bank7_other C R root rank depth M mask 52 (by decide)]
    rw [bank6_other C R root rank depth M mask 52 (by decide)]
    rw [bank5_other C R root rank depth M mask 52 (by decide)]
    rw [bank4_other C R root rank depth M mask 52 (by decide)]
    rw [bank3_other C R root rank depth M mask 52 (by decide)]
    rw [bank2_other C R root rank depth M mask 52 (by decide)]
    rw [bank1_other C R root rank depth M mask 52 (by decide)]
    rfl
  · change bank9 C R root rank depth M mask 53=NativeFanout.input (m:=13) (source C root rank depth M mask) R 22
    rw [bank9_other C R root rank depth M mask 53 (by decide)]
    rw [bank8_other C R root rank depth M mask 53 (by decide)]
    rw [bank7_other C R root rank depth M mask 53 (by decide)]
    rw [bank6_other C R root rank depth M mask 53 (by decide)]
    rw [bank5_other C R root rank depth M mask 53 (by decide)]
    rw [bank4_other C R root rank depth M mask 53 (by decide)]
    rw [bank3_other C R root rank depth M mask 53 (by decide)]
    rw [bank2_other C R root rank depth M mask 53 (by decide)]
    rw [bank1_other C R root rank depth M mask 53 (by decide)]
    rfl
  · change bank9 C R root rank depth M mask 1=NativeFanout.input (m:=13) (source C root rank depth M mask) R 23
    rw [bank9_other C R root rank depth M mask 1 (by decide)]
    rw [bank8_other C R root rank depth M mask 1 (by decide)]
    rw [bank7_other C R root rank depth M mask 1 (by decide)]
    rw [bank6_other C R root rank depth M mask 1 (by decide)]
    change bank5 C R root rank depth M mask (slots5 0)=_
    rw [bank5_slot]
    rfl
  · change bank9 C R root rank depth M mask 54=NativeFanout.input (m:=13) (source C root rank depth M mask) R 24
    rw [bank9_other C R root rank depth M mask 54 (by decide)]
    rw [bank8_other C R root rank depth M mask 54 (by decide)]
    rw [bank7_other C R root rank depth M mask 54 (by decide)]
    rw [bank6_other C R root rank depth M mask 54 (by decide)]
    rw [bank5_other C R root rank depth M mask 54 (by decide)]
    rw [bank4_other C R root rank depth M mask 54 (by decide)]
    rw [bank3_other C R root rank depth M mask 54 (by decide)]
    rw [bank2_other C R root rank depth M mask 54 (by decide)]
    rw [bank1_other C R root rank depth M mask 54 (by decide)]
    rfl

theorem step10 (C R root rank depth M : Nat) (mask : List Bool) (h : Bounds C R root rank depth M mask) :
    Step phase10 (2*R+4) (fun _=>0) (bank9 C R root rank depth M mask) (fun _=>0) (bank10 C R root rank depth M mask) := by
  have localStep:=Step.of_ready (NativeFanout.ready select (source C root rank depth M mask) R
    (source_length C R root rank depth M mask h))
  have focused:=localStep.focus slots10 (by decide) (fun _=>0) (bank9 C R root rank depth M mask)
  exact (focused.congr_in (zero_heads slots10)
    (install_existing _ _ _ (join10 C R root rank depth M mask))).congr (zero_heads slots10) rfl

def machine := Composition.machine joined9 phase10
def budget (C R root rank depth M : Nat) (mask : List Bool) := budget9 C R root rank depth M mask+1+(2*R+4)
theorem run (C R root rank depth M : Nat) (mask : List Bool) (h : Bounds C R root rank depth M mask) :
    Step machine (budget C R root rank depth M mask) (fun _=>0) (input C R root rank depth M mask) (fun _=>0) (bank10 C R root rank depth M mask) :=
  (run9 C R root rank depth M mask).seq (step10 C R root rank depth M mask h)

def paletteSlots : Fin 15→Fin 55 := ![41,42,31,1,43,44,45,46,47,48,49,50,51,52,53]
def palette (C R root rank depth M : Nat) (mask : List Bool) : Fin 15→List Bool :=
  ![ZeroPadding.pad R (UnaryTemplate.tape (2*C+3)),ZeroPadding.pad R (UnaryTemplate.tape C),
    UnaryTemplate.tape R,List.replicate R true,ZeroPadding.pad R (List.replicate root true),
    ZeroPadding.pad R (List.replicate rank true),List.replicate R false,List.replicate R false,
    List.replicate R false,ZeroPadding.pad R (CompareMachine.word rank),ZeroPadding.pad R mask,
    ZeroPadding.pad R (List.replicate (C+9) true),ZeroPadding.pad R (CompareMachine.word depth),
    ZeroPadding.pad R (CompareMachine.word (C+9)),ZeroPadding.pad R (CompareMachine.word M)]

theorem palette_output (C R root rank depth M : Nat) (mask : List Bool) (h : Bounds C R root rank depth M mask) :
    ∀i,bank10 C R root rank depth M mask (paletteSlots i)=palette C R root rank depth M mask i := by
  intro i;fin_cases i
  · change bank10 C R root rank depth M mask (slots10 10)=_
    rw [bank10_slot]
    rfl
  · change bank10 C R root rank depth M mask (slots10 11)=_
    rw [bank10_slot]
    rfl
  · change bank10 C R root rank depth M mask 31=_
    rw [bank10_other C R root rank depth M mask 31 (by decide)]
    rw [bank9_other C R root rank depth M mask 31 (by decide)]
    rw [bank8_other C R root rank depth M mask 31 (by decide)]
    rw [bank7_other C R root rank depth M mask 31 (by decide)]
    rw [bank6_other C R root rank depth M mask 31 (by decide)]
    change bank5 C R root rank depth M mask (slots5 1)=_
    rw [bank5_slot]
    rfl
  · change bank10 C R root rank depth M mask (slots10 23)=_
    rw [bank10_slot]
    rfl
  · change bank10 C R root rank depth M mask (slots10 12)=_
    rw [bank10_slot]
    rfl
  · change bank10 C R root rank depth M mask (slots10 13)=_
    rw [bank10_slot]
    rfl
  · change bank10 C R root rank depth M mask (slots10 14)=_
    rw [bank10_slot]
    simp [NativeFanout.output,NativeFanout.word,select,source,palette,ZeroPadding.pad,Fin.addCases]
  · change bank10 C R root rank depth M mask (slots10 15)=_
    rw [bank10_slot]
    simp [NativeFanout.output,NativeFanout.word,select,source,palette,ZeroPadding.pad,Fin.addCases]
  · change bank10 C R root rank depth M mask (slots10 16)=_
    rw [bank10_slot]
    simp [NativeFanout.output,NativeFanout.word,select,source,palette,ZeroPadding.pad,Fin.addCases]
  · change bank10 C R root rank depth M mask (slots10 17)=_
    rw [bank10_slot]
    change ZeroPadding.pad R (UnaryTemplate.tape (rank))=ZeroPadding.pad R (CompareMachine.word (rank))
    exact (CycleLiveSuccessor.pad_compare_template R (rank) (by have hb:=h.rank;omega)).symm
  · change bank10 C R root rank depth M mask (slots10 18)=_
    rw [bank10_slot]
    rfl
  · change bank10 C R root rank depth M mask (slots10 19)=_
    rw [bank10_slot]
    rfl
  · change bank10 C R root rank depth M mask (slots10 20)=_
    rw [bank10_slot]
    change ZeroPadding.pad R (UnaryTemplate.tape (depth))=ZeroPadding.pad R (CompareMachine.word (depth))
    exact (CycleLiveSuccessor.pad_compare_template R (depth) (by have hb:=h.depth;omega)).symm
  · change bank10 C R root rank depth M mask (slots10 21)=_
    rw [bank10_slot]
    change ZeroPadding.pad R (UnaryTemplate.tape (C+9))=ZeroPadding.pad R (CompareMachine.word (C+9))
    exact (CycleLiveSuccessor.pad_compare_template R (C+9) (by have hb:=h.code;omega)).symm
  · change bank10 C R root rank depth M mask (slots10 22)=_
    rw [bank10_slot]
    change ZeroPadding.pad R (UnaryTemplate.tape (M))=ZeroPadding.pad R (CompareMachine.word (M))
    exact (CycleLiveSuccessor.pad_compare_template R (M) (by have hb:=h.population;omega)).symm
end
end Theorem25Completion.WalkLiteralMasters
