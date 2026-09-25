import Proof.Packets.PacketsXWalkLiteralProducedPrepare

/-! Exact byte-and-head boundary for the produced palette and physical copies. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralProduced
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer Completion
noncomputable section

def coordinate (rank : Nat) (a : ZMod (2^toeplitzWalkSideBits rank)) :=
  frame (FinalWalkStep.coordEncode (toeplitzWalkSideBits rank) a)

theorem coordinate_length (rank : Nat) (a : ZMod (2^toeplitzWalkSideBits rank)) :
    (coordinate rank a).length=2*toeplitzWalkSideBits rank+1 := by
  simp [coordinate,frame_length,FinalWalkStep.coordEncode_length]

theorem prepared_small (masters : Fin 95→List Bool) (rank R S n : Nat) (x y code : List Bool) (i : Fin 95) :
    prepared masters rank R S n x y code (i.castAdd 338)=masters i := by
  have hn := i.isLt
  simp only [prepared,fanoutBank,templateBank,rawBank,Function.update_apply]
  split_ifs <;>try {rename_i he; have hv:=congrArg Fin.val he;dsimp at hv;omega}
  simp [bank0]

theorem cold_palette_slot (i : Fin 15) :
    coldSlots ⟨15+i.val,by omega⟩=(paletteSlots i).castAdd 338 := by
  have hi := i.isLt
  simp [coldSlots,show 15+i.val<30 by omega]

theorem entry_tail (rank R S n : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank))
    (code : List Bool) (palette : Fin 15→List Bool) (i : Fin 333) (hi : 30 ≤ i.val) :
    WalkLiteralCold.entry rank R S n v code palette i=
      if i=329 then List.replicate S true else if i=332 then CompareMachine.word n else [] := by
  by_cases h332 : i=332
  · subst i;rfl
  have hlt : i.val<332 := by
    have hb:=i.isLt
    have hne : i.val≠332:=by simpa [Fin.ext_iff] using h332
    omega
  by_cases h331 : i=331
  · subst i;rfl
  have hlt331 : i.val<331 := by
    have hne : i.val≠331:=by simpa [Fin.ext_iff] using h331
    omega
  by_cases h330 : i=330
  · subst i;rfl
  have hlt330 : i.val<330 := by
    have hne : i.val≠330:=by simpa [Fin.ext_iff] using h330
    omega
  by_cases h329 : i=329
  · subst i;rfl
  have hlt329 : i.val<329 := by
    have hne : i.val≠329:=by simpa [Fin.ext_iff] using h329
    omega
  simp [WalkLiteralCold.entry,NativeFanout.input,Fin.addCases,hlt,h332,h329,
    show ¬i.val<15 by omega,show i.val-15<316 by omega,show i.val-15<315 by omega,
    show ¬i.val-15<15 by omega,show i.val-15-15<299 by omega]

theorem prepared_tail (masters : Fin 95→List Bool) (rank R S n : Nat) (x y code : List Bool)
    (i : Fin 333) (hi : 30 ≤ i.val) :
    prepared masters rank R S n x y code (coldSlots i)=
      if i=329 then List.replicate S true else if i=332 then CompareMachine.word n else [] := by
  have hib:=i.isLt
  have hnot : ¬(15 ≤ i.val ∧ i.val<30) := by omega
  rw [coldSlots,dif_neg hnot]
  have lo : 125 ≤ 95+i.val := by omega
  have hi' : 95+i.val<428 := by omega
  have h432 : (⟨95+i.val,by omega⟩ : Fin 433)≠432 := by
    intro he
    have hv:=congrArg Fin.val he
    dsimp at hv
    omega
  have h96 : (⟨95+i.val,by omega⟩ : Fin 433)≠96 := by
    intro he
    have hv:=congrArg Fin.val he
    dsimp at hv
    omega
  have h95 : (⟨95+i.val,by omega⟩ : Fin 433)≠95 := by
    intro he
    have hv:=congrArg Fin.val he
    dsimp at hv
    omega
  have h105 : (⟨95+i.val,by omega⟩ : Fin 433)≠105 := by
    intro he
    have hv:=congrArg Fin.val he
    dsimp at hv
    omega
  have h431 : (⟨95+i.val,by omega⟩ : Fin 433)≠431 := by
    intro he
    have hv:=congrArg Fin.val he
    dsimp at hv
    omega
  have h100 : (⟨95+i.val,by omega⟩ : Fin 433)≠100 := by
    intro he
    have hv:=congrArg Fin.val he
    dsimp at hv
    omega
  have h430 : (⟨95+i.val,by omega⟩ : Fin 433)≠430 := by
    intro he
    have hv:=congrArg Fin.val he
    dsimp at hv
    omega
  have h99 : (⟨95+i.val,by omega⟩ : Fin 433)≠99 := by
    intro he
    have hv:=congrArg Fin.val he
    dsimp at hv
    omega
  simp only [prepared,fanoutBank,templateBank,rawBank,Function.update_of_ne h432,Function.update_of_ne h96,
    Function.update_of_ne h95,Function.update_of_ne h105,Function.update_of_ne h431,Function.update_of_ne h100,
    Function.update_of_ne h430,Function.update_of_ne h99]
  simp [bank0,extras,Fin.addCases,Fin.ext_iff,show ¬95+i.val<95 by omega,
    show (95+i.val-95)=i.val by omega,show i.val≠7 by omega,
    show i.val≠333 by omega,show i.val≠334 by omega]

theorem prepared_join (masters : Fin 95→List Bool) (rank R S n : Nat)
    (v : MargulisVertex (2^toeplitzWalkSideBits rank)) (code : List Bool) (palette : Fin 15→List Bool)
    (hp : ∀i,masters (paletteSlots i)=palette i) :
    ∀i,prepared masters rank R S n (coordinate rank v.1) (coordinate rank v.2) code (coldSlots i)=
      WalkLiteralCold.entry rank R S n v code palette i := by
  intro i
  by_cases hlo : i.val<15
  · obtain ⟨j,hj⟩ : ∃j : Fin 15,j.val=i.val := ⟨⟨i.val,hlo⟩,rfl⟩
    have he : i=j.castAdd 318 := by apply Fin.ext;exact hj.symm
    subst i
    fin_cases j <;>rfl
  by_cases hpal : i.val<30
  · let j : Fin 15:=⟨i.val-15,by omega⟩
    have he : i=(⟨15+j.val,by have hb:=j.isLt;omega⟩ : Fin 333) := by apply Fin.ext;dsimp [j];omega
    rw [he,cold_palette_slot,prepared_small,hp]
    have ent (k : Fin 15) : WalkLiteralCold.entry rank R S n v code palette ⟨15+k.val,by have hb:=k.isLt;omega⟩=palette k := by
      fin_cases k <;>rfl
    exact (ent j).symm
  · rw [prepared_tail _ _ _ _ _ _ _ _ _ (by omega),entry_tail _ _ _ _ _ _ _ _ (by omega)]

theorem prepared_heads_join : ∀i,preparedHeads (coldSlots i)=WalkLiteralCold.entryHeads i := by
  intro i
  by_cases hi : i=332
  · subst i;rfl
  have ne : coldSlots i≠427 := by
    intro he
    have he' : coldSlots i=coldSlots 332 := he
    exact hi (cold_slots_injective he')
  have hlt : i.val<332 := by
    have hb:=i.isLt
    have hn : i.val≠332:=by simpa [Fin.ext_iff] using hi
    omega
  simp [preparedHeads,ne,WalkLiteralCold.entryHeads,Fin.addCases,hlt]

theorem prepared_heads_dock :
    dockH coldSlots preparedHeads WalkLiteralCold.entryHeads=preparedHeads :=
  dockH_existing _ _ _ prepared_heads_join

end
end Theorem25Completion.WalkLiteralProduced
