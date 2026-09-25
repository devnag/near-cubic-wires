import Proof.Packets.PacketsXWindowModeAtoms
import Proof.Packets.WindowModeLevelDock
import Proof.Packets.PacketsXWindowProviderZeroRight

/-! A fixed, paid level provider. It clears the previous right operand,
derives the raw level from the retained successor tag, emits both mode-cache
halves, and constructs their literal cache and cumulative dense atom bank. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 10000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsModeCache
open Theorem25Completion.CycleBounds Theorem25Completion.CycleDenseAtomCost
noncomputable section

attribute [local irreducible] zeroRight makeModeLevel modeAtoms

def levelProvider := Composition.machine zeroRight (Composition.machine makeModeLevel modeAtoms)
def levelProviderInput (R level : Nat) (A : Fin 256 → List Bool) := modeLevelOutput R level (rightZero R A)
def levelProviderOutput (p : Parameters) (M C R : Nat)
    (initial : List PacketVector.Packet) (A : Fin 256 → List Bool) :=
  modeAtomsOutput p M C R initial (levelProviderInput R p.level A)
def levelProviderBudget (p : Parameters) (M C R : Nat) :=
  (4*R+5)+1+(ModeLevelRaw.budget R p.level+1+modeAtomsBudget p M C R)

theorem level_input_other (R level : Nat) (A : Fin 256 → List Bool) (i : Fin 256)
    (h26 : i≠26) (h27 : i≠27) (h159 : i≠159) (h176 : i≠176) :
    levelProviderInput R level A i=A i := by
  simp only [levelProviderInput,modeLevelOutput,Function.update_of_ne h159,
    Function.update_of_ne h176,zero_right_other R A i h26 h27]

theorem level_input_engine (C R level : Nat) (left right : PacketVector.Packet)
    (A : Fin 256 → List Bool) (hR : 1≤R)
    (hengine : ∀i : Fin 34,A (i.castAdd 222)=ReusableArithmetic.state C R left right i) :
    ∀i : Fin 34,levelProviderInput R level A (i.castAdd 222)=ReusableArithmetic.state C R left [] i := by
  intro i
  have hi:=i.isLt
  have h159 : (i.castAdd 222 : Fin 256)≠159 := by intro he;have h:=congrArg Fin.val he;dsimp at h;omega
  have h176 : (i.castAdd 222 : Fin 256)≠176 := by intro he;have h:=congrArg Fin.val he;dsimp at h;omega
  simp only [levelProviderInput,modeLevelOutput,Function.update_of_ne h159,Function.update_of_ne h176]
  exact zero_right_engine C R left right A hR hengine i

theorem level_provider_run (p : Parameters) (M C w : Nat)
    (out : List Bool) (priv : Fin 15 → List Bool) (initial : List PacketVector.Packet)
    (hl : p.level≤p.rank) (hC : p.rank+2≤p.C)
    (hb : CloseoutRowsModeHashLoop.budget p.rank p.rank+2≤p.C)
    (hi : M≤2^p.rank) (hlog : sourceBudget p M≤commonReserve C w+3)
    (hD : reuseCapacity p M≤commonReserve C w)
    (hpriv : ∀i,(priv i).length≤commonReserve C w)
    (hout : out.length≤commonReserve C w)
    (hword : (ModeCacheReady.word p M).length≤commonReserve C w)
    (hw : 1≤w) (htag : p.level+1≤C) (hcount : (modePairs p M).length≤C)
    (hcodes : ∀i<(modePairs p M).length,Nat.pair (p.level+1) i<C)
    (hshape : ∀pair∈modePairs p M,AtomShape C pair)
    (hinit : initial.length=C) (hinits : ∀P∈initial,PacketVector.Fits (commonReserve C w) P)
    (left right : PacketVector.Packet) (A : Fin 256 → List Bool)
    (hright : VectorAccumulator.Fits (commonReserve C w) right)
    (hengine : ∀i : Fin 34,A (i.castAdd 222)=ReusableArithmetic.state C (commonReserve C w) left right i)
    (hmode : ∀i,i≠12 → ModeCacheReady.A p M (commonReserve C w) out priv i=A (modePorts i))
    (atag : A 187=WindowSeed.source (commonReserve C w) (p.level+1))
    (acount : A 184=WindowSeed.source (commonReserve C w) (modePairs p M).length)
    (abank : A 140=PacketVector.bank (commonReserve C w) initial)
    (hprivate : ∀i,i≠59 → i≠60 → i≠62 → i≠64 → i≠65 → (A (literalPorts i)).length≤commonReserve C w)
    (hwork : ∀i,Workspace.selected i → (A i).length≤commonReserve C w)
    (h129 : (A 129).length≤commonReserve C w)
    (h159 : (A 159).length≤commonReserve C w) (h176 : (A 176).length≤commonReserve C w) :
    Step levelProvider (levelProviderBudget p M C (commonReserve C w)) heads A heads
      (levelProviderOutput p M C (commonReserve C w) initial A) := by
  let R:=commonReserve C w
  have reserve : C+2≤R := LiteralCacheReuse.reserve_width C w
  have first := (zero_right_provider C R left right A (by omega) hright hengine).1
  have second := make_mode_level_run R p.level heads (rightZero R A) (by decide)
    ((zero_right_other R A 187 (by decide) (by decide)).trans atag)
    ((zero_right_other R A 32 (by decide) (by decide)).trans (hengine 32))
    ((zero_right_other R A 33 (by decide) (by decide)).trans (hengine 33))
    (by rw [zero_right_other R A 159 (by decide) (by decide)];exact h159)
    (by rw [zero_right_other R A 176 (by decide) (by decide)];exact h176) (by omega)
  have mode : ∀i,ModeCacheReady.A p M R out priv i=levelProviderInput R p.level A (modePorts i) := by
    intro i
    by_cases he : i=12
    · subst i
      simp [ModeCacheReady.A,ModeCacheReady.caps,reuseData,Fin.addCases,modePorts,
        levelProviderInput,modeLevelOutput]
    · have away : ∀j : Fin 29,j≠12 → modePorts j≠26 ∧ modePorts j≠27 ∧ modePorts j≠159 ∧ modePorts j≠176 := by decide
      obtain ⟨h26,h27,ha,hb⟩:=away i he
      rw [level_input_other R p.level A _ h26 h27 ha hb]
      exact hmode i he
  have last := mode_atoms_run p M C w out priv initial hl hC hb hi hlog hD hpriv hout hword
    hw htag hcount hcodes hshape hinit hinits left (levelProviderInput R p.level A)
    (level_input_engine C R p.level left right A (by omega) hengine) mode
    ((level_input_other R p.level A 187 (by decide) (by decide) (by decide) (by decide)).trans atag)
    ((level_input_other R p.level A 184 (by decide) (by decide) (by decide) (by decide)).trans acount)
    ((level_input_other R p.level A 140 (by decide) (by decide) (by decide) (by decide)).trans abank)
    (by
      intro i h59 h60 h62 h64 h65
      have away : ∀j : Fin 68,j≠59 → j≠60 → j≠62 → j≠64 → j≠65 →
          literalPorts j≠26 ∧ literalPorts j≠27 ∧ literalPorts j≠159 ∧ literalPorts j≠176 := by decide
      obtain ⟨h26,h27,ha,hb⟩:=away i h59 h60 h62 h64 h65
      rw [level_input_other R p.level A _ h26 h27 ha hb]
      exact hprivate i h59 h60 h62 h64 h65)
    (by
      intro i hi
      have away : ∀j : Fin 256,Workspace.selected j → j≠26 ∧ j≠27 ∧ j≠159 ∧ j≠176 := by decide
      obtain ⟨h26,h27,ha,hb⟩:=away i hi
      rw [level_input_other R p.level A _ h26 h27 ha hb]
      exact hwork i hi)
    (by rw [level_input_other R p.level A 129 (by decide) (by decide) (by decide) (by decide)];exact h129)
  exact first.seq (second.seq last)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
