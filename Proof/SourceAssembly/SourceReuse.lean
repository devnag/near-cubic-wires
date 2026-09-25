import Proof.SourceAssembly.SourceBundle

/- Same ordinary source programs on retained backing.  No allocation or erasure
is inferred from these representation identities. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ6e421fabe2aa4155_SourceReuse
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound RepairOrdinary.RecoveryExecution RepairRepresentation
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
noncomputable section

theorem pad_pad (a b : Nat) (tape : List Bool) :
    ZeroPadding.pad a (ZeroPadding.pad b tape) = ZeroPadding.pad (max a b) tape := by
  simp only [ZeroPadding.pad, List.length_append, List.length_replicate,
    List.append_assoc, ← List.replicate_add]
  congr 1
  congr 1
  omega

theorem pad_install {t u : Nat} (slots : Fin t → Fin u)
    (R : Fin u → Nat) (ambient : Fin u → List Bool) (bank : Fin t → List Bool) :
    (fun i => ZeroPadding.pad (R i) (install slots ambient bank i)) =
    install slots (fun i => ZeroPadding.pad (R i) (ambient i))
      (fun j => ZeroPadding.pad (R (slots j)) (bank j)) := by
  funext i
  cases hp : RecoveryFocus.pick slots i with
  | none => simp [install, hp]
  | some j =>
    have he := RecoveryFocus.slot_of_pick slots hp
    simp only [install, hp]
    rw [he]

theorem ready_pad {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} {packet : PacketWriter selector a} {U : Nat}
    (c : MaskSeedCode mask packet U) (r : Request) (fuel : Nat)
    (H H' : Fin U → Nat) (A A' : Fin U → List Bool) (R : Fin U → Nat)
    (h : c.Ready r fuel H H' A A') :
    c.Ready r fuel H H' (fun i => ZeroPadding.pad (R i) (A i))
      (fun i => ZeroPadding.pad (R i) (A' i)) := by
  obtain ⟨mR,mH,mA,pR,pH,pA,leadFuel,suffixFuel,tailFuel,lead,suffix,tail,bound⟩ := h
  refine ⟨(fun j => max (R (c.maskSlots j)) (mR j)),mH,
    (fun i => ZeroPadding.pad (R i) (mA i)),
    (fun j => max (R (c.slots j)) (pR j)),pH,
    (fun i => ZeroPadding.pad (R i) (pA i)),leadFuel,suffixFuel,tailFuel,?_,?_,?_,bound⟩
  · simpa only [pad_install, pad_pad] using lead.pad R
  · intro B run out
    simpa only [pad_install, pad_pad] using (suffix B run out).pad R
  · intro B run out
    simpa only [pad_install, pad_pad] using (tail B run out).pad R

theorem dockH_existing {t u : Nat} (slot : Fin t → Fin u) (ambient : Fin u → Nat)
    (heads : Fin t → Nat) (h : ∀ j, ambient (slot j) = heads j) :
    dockH slot ambient heads = ambient := by
  funext i
  cases hp : RecoveryFocus.pick slot i with
  | none => simp [dockH, hp]
  | some j =>
    have he := RecoveryFocus.slot_of_pick slot hp
    simp only [dockH, hp]
    exact (h j).symm.trans (congrArg ambient he)

def haltMachine (T : Nat) : Machine T 1 where
  descriptionBits := 0
  start := 0
  halted := fun _ => true
  rule := fun _ _ => none

theorem halt_step {T : Nat} (H : Fin T → Nat) (A : Fin T → List Bool) :
    Step (haltMachine T) 0 H A H A :=
  ⟨{ final := ⟨(haltMachine T).start,H,A⟩, steps := 0,
      peakTapeCells := (⟨(haltMachine T).start,H,A⟩ : Configuration T 1).tapeCells },
    (by simp [runFrom, haltMachine]),rfl,rfl,le_rfl⟩

def identityTail {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} {packet : PacketWriter selector a} {U : Nat}
    (c : MaskSeedCode mask packet U) : MaskSeedCode mask packet U :=
  { c with tailStates := 1, tail := haltMachine U }

end
end PCJ6e421fabe2aa4155_SourceReuse
