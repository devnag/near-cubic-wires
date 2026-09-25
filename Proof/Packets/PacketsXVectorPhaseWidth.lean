import Proof.Packets.PacketsXVectorNumericArena
import Proof.Packets.WindowSeedPrimitives
import Proof.Packets.SourceDigitWidthBounds

/-! Recompute the provider's logarithmic subset width from its actual count.
The raw input is physically copied, the twelve-port binary/length worker runs,
its result overwrites185, and every private work tape is erased. -/
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open RecoveryRootRound
noncomputable section

def widthSlots (j : Fin 12) : Fin 299 := ⟨283+j.val,by omega⟩
def rawSlots : Fin 3→Fin 299 := ![184,283,33]
def widthEraseSlots : Fin 14→Fin 299 := Fin.addCases (m:=12) (n:=2) (motive:=fun _=>Fin 299)
  widthSlots (![32,33])
def widthRaw := RecoveryFocus.machine rawSlots WindowSeed.raw
def widthWorker := RecoveryFocus.machine widthSlots Completion.SourceDigitWidth.machine
def widthCopy := PhysicalCopyInto.machine (31 : Fin 299) 293 185
def widthErase := RecoveryFocus.machine widthEraseSlots (RecoveryScratchErase.resetMachine 12)
def regenerateWidth := Composition.machine widthRaw
  (Composition.machine widthWorker (Composition.machine widthCopy widthErase))

theorem width_inj : Function.Injective widthSlots := by
  intro i j h;apply Fin.ext;have hv:=congrArg Fin.val h;dsimp [widthSlots] at hv;omega

theorem raw_count_run (R M : Nat) (A : Fin 299→List Bool)
    (hm : A 184=ZeroPadding.pad R (CompareMachine.word M))
    (hout : A 283=List.replicate R false) (hlog : A 33=List.replicate (R+3) false)
    (hr : M≤R+1) :
    Step widthRaw (2*M+6) heads A heads
      (Function.update A 283 (ZeroPadding.pad R (List.replicate M true))) := by
  apply PhysicalFocusBoundary.focus (WindowSeed.raw_run R M hr) rawSlots (by decide) heads heads A _
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i
    · exact hm.symm
    · simpa [WindowSeed.rawData,rawSlots,ZeroPadding.pad] using hout.symm
    · exact hlog.symm
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i
    · simpa [WindowSeed.rawData,WindowSeed.source,rawSlots,Function.update] using hm.symm
    · rfl
    · simpa [WindowSeed.rawData,rawSlots,Function.update] using hlog.symm
  · intro i away
    have hi:i≠283 := by intro he;exact away 1 he.symm
    exact ⟨rfl,by simp only [Function.update_of_ne hi]⟩

theorem regenerate_width_run (R M : Nat) (A : Fin 299→List Bool)
    (hR : A 31=UnaryTemplate.tape R) (hraw : A 32=List.replicate R true)
    (hlog : A 33=List.replicate (R+3) false)
    (hM : A 184=ZeroPadding.pad R (CompareMachine.word M))
    (hw : ∀j,A (widthSlots j)=List.replicate R false)
    (h185 : (A 185).length=R) (hcap : Completion.SourceDigitWidth.capacity M≤R) :
    Step regenerateWidth (4*R+2*M+Completion.SourceDigitWidth.budget M+15) heads A heads
      (Function.update A 185 (ZeroPadding.pad R (CompareMachine.word (Completion.SourceDigitWidth.digitWidth M)))) := by
  have hm : M≤R+1 := by unfold Completion.SourceDigitWidth.capacity at hcap;nlinarith
  have first:=raw_count_run R M A hM (hw 0) hlog hm
  let A1:=Function.update A 283 (ZeroPadding.pad R (List.replicate M true))
  obtain ⟨B,hb,b10,_b1,_b3,_b5,bl⟩:=Completion.SourceDigitWidth.padded_run M R hcap
  have second:=hb.dock widthSlots width_inj heads A1
    (by intro j;simp only [widthSlots,heads,Fin.ext_iff];split <;>omega) (by
      intro j
      by_cases hj:j=0
      · subst j;rfl
      have hp:widthSlots j≠283 := by intro he;exact hj (width_inj (show widthSlots j=widthSlots 0 from he))
      simp only [A1,Function.update_of_ne hp,hw j,Completion.SourceDigitWidth.input,if_neg hj]
      simp [ZeroPadding.pad])
  rw [dockH_existing widthSlots heads (fun _=>0)
    (by intro j;simp only [widthSlots,heads,Fin.ext_iff];split <;>omega)] at second
  let A2:=install widthSlots A1 B
  have other (i : Fin 299) (hi:i.val<283) : A2 i=A1 i := by
    apply install_other
    intro j he
    have hv:=congrArg Fin.val he
    dsimp [widthSlots] at hv;omega
  have source : A2 293=ZeroPadding.pad R (CompareMachine.word (Completion.SourceDigitWidth.digitWidth M)) :=
    (install_slot widthSlots width_inj A1 B 10).trans b10
  have third:=PhysicalCopyInto.run R (31 : Fin 299) 293 185 (by decide) (by decide) (by decide)
    heads A2 rfl rfl rfl (by rw [other 31 (by decide)];simpa [A1,Function.update] using hR)
    (by rw [show A2 293=B 10 from install_slot widthSlots width_inj A1 B 10];exact bl 10)
    (by rw [other 185 (by decide)];simpa [A1,Function.update] using h185)
  let A3:=Function.update A2 185 (A2 293)
  let final:=Function.update A 185 (ZeroPadding.pad R (CompareMachine.word (Completion.SourceDigitWidth.digitWidth M)))
  have eraseReady:=Step.of_ready (RecoveryScratchErase.erase_ready R (R+3) B (fun j=>(bl j).le))
  have fourth : Step widthErase (2*R+4) heads A3 heads final := by
    apply PhysicalFocusBoundary.focus eraseReady widthEraseSlots (by decide) heads heads A3 final
    · intro j;fin_cases j <;>rfl
    · intro j
      refine Fin.addCases (m:=12) (n:=2) (fun i=>?_) (fun i=>?_) j
      · have hp:widthSlots i≠185 := by intro he;have hv:=congrArg Fin.val he;dsimp [widthSlots] at hv;omega
        have hx : Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool)
            (Fin.addCases (m:=12) (n:=1) (motive:=fun _=>List Bool) B (fun _=>List.replicate R true))
            (fun _=>List.replicate (R+3) false) (i.castAdd 2)=B i := by fin_cases i <;>rfl
        rw [hx]
        rw [show widthEraseSlots (i.castAdd 2)=widthSlots i from Fin.addCases_left i]
        simp only [A3,Function.update_of_ne hp]
        exact (install_slot widthSlots width_inj A1 B i).symm
      · fin_cases i
        · change List.replicate R true=A3 32
          simp only [A3,Function.update_of_ne (by decide : (32 : Fin 299)≠185)]
          rw [other 32 (by decide)];simpa [A1,Function.update] using hraw.symm
        · change List.replicate (R+3) false=A3 33
          simp only [A3,Function.update_of_ne (by decide : (33 : Fin 299)≠185)]
          rw [other 33 (by decide)];simpa [A1,Function.update] using hlog.symm
    · intro j;fin_cases j <;>rfl
    · intro j;fin_cases j
      · simpa [final,widthEraseSlots,widthSlots,Fin.addCases,Function.update] using (hw 0).symm
      · simpa [final,widthEraseSlots,widthSlots,Fin.addCases,Function.update] using (hw 1).symm
      · simpa [final,widthEraseSlots,widthSlots,Fin.addCases,Function.update] using (hw 2).symm
      · simpa [final,widthEraseSlots,widthSlots,Fin.addCases,Function.update] using (hw 3).symm
      · simpa [final,widthEraseSlots,widthSlots,Fin.addCases,Function.update] using (hw 4).symm
      · simpa [final,widthEraseSlots,widthSlots,Fin.addCases,Function.update] using (hw 5).symm
      · simpa [final,widthEraseSlots,widthSlots,Fin.addCases,Function.update] using (hw 6).symm
      · simpa [final,widthEraseSlots,widthSlots,Fin.addCases,Function.update] using (hw 7).symm
      · simpa [final,widthEraseSlots,widthSlots,Fin.addCases,Function.update] using (hw 8).symm
      · simpa [final,widthEraseSlots,widthSlots,Fin.addCases,Function.update] using (hw 9).symm
      · simpa [final,widthEraseSlots,widthSlots,Fin.addCases,Function.update] using (hw 10).symm
      · simpa [final,widthEraseSlots,widthSlots,Fin.addCases,Function.update] using (hw 11).symm
      · simpa [final,widthEraseSlots,Fin.addCases,Function.update] using hraw.symm
      · simpa [final,widthEraseSlots,Fin.addCases,Function.update,Nat.max_eq_left (by omega : R+1≤R+3)] using hlog.symm
    · intro i away
      refine ⟨rfl,?_⟩
      by_cases h185:i=185
      · subst i;simp only [A3,final,Function.update_self];exact source
      have outside : ∀j,widthSlots j≠i := by
        intro j hj;exact away (j.castAdd 2) ((Fin.addCases_left j).trans hj)
      have h283:i≠283 := by intro he;exact outside 0 he.symm
      simp only [A3,final,Function.update_of_ne h185,A2,install_other widthSlots A1 B i outside,
        A1,Function.update_of_ne h283]
  have whole:=first.seq (second.seq (third.seq fourth))
  have hf : (2*M+6)+1+(Completion.SourceDigitWidth.budget M+1+((2*R+2)+1+(2*R+4)))=
      4*R+2*M+Completion.SourceDigitWidth.budget M+15 := by omega
  rw [hf] at whole;exact whole

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
