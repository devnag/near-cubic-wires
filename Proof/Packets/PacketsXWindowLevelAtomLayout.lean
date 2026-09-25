import Proof.Packets.PacketsXWindowLevelAtoms

/-! Literal field preservation and private capacity after the closed
level-cache machine, for the repeated vector-level invariant. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsRawPairSeek (Pair)
open Theorem25Completion.CycleBounds

theorem level_atoms_cache (C R tag : Nat) (cs : List Pair) (initial : List PacketVector.Packet)
    (A : Fin 256→List Bool) : levelAtomsOutput C R tag cs initial A 186=
      ZeroPadding.pad R (ReflectedLiteralCache.stream tag cs.length) := by
  change cacheOutput R tag cs.length A 186=_
  exact produced_cache R tag cs.length A

theorem level_atoms_bank (C R tag : Nat) (cs : List Pair) (initial : List PacketVector.Packet)
    (A : Fin 256→List Bool) : levelAtomsOutput C R tag cs initial A 140=
      PacketVector.bank R (DenseAtomProgram.table C tag cs initial cs.length) := by
  simp only [levelAtomsOutput,Function.update_self]

theorem level_atoms_outside_work (C R tag : Nat) (cs : List Pair) (initial : List PacketVector.Packet)
    (A : Fin 256→List Bool) (i : Fin 256) (hi : ¬Workspace.selected i) (h129 : i≠129) (h140 : i≠140) :
    levelAtomsOutput C R tag cs initial A i=cacheOutput R tag cs.length A i := by
  simp only [levelAtomsOutput,denseReady,Function.update_of_ne h129,Function.update_of_ne h140,
    Workspace.cleared,if_neg hi]

theorem literal_private_outside_work (i : Fin 68) (h59 : i≠59) (h60 : i≠60)
    (h62 : i≠62) (h64 : i≠64) (h65 : i≠65) :
    ¬Workspace.selected (literalPorts i) ∧ literalPorts i≠129 ∧ literalPorts i≠140 := by
  fin_cases i <;>simp_all [literalPorts,Workspace.selected]

theorem level_atoms_private_lengths (C w tag : Nat) (cs : List Pair) (initial : List PacketVector.Packet)
    (ht : tag≤C) (hc : cs.length≤C) (hcodes : ∀i,i<cs.length→Nat.pair tag i≤C)
    (A : Fin 256→List Bool) :
    ∀i,i≠59→i≠60→i≠62→i≠64→i≠65→
      (levelAtomsOutput C (commonReserve C w) tag cs initial A (literalPorts i)).length=commonReserve C w := by
  intro i h59 h60 h62 h64 h65
  obtain ⟨hi,h129,h140⟩:=literal_private_outside_work i h59 h60 h62 h64 h65
  rw [level_atoms_outside_work C _ tag cs initial A _ hi h129 h140]
  exact cache_private_lengths C w tag cs.length ht hc hcodes A i h59 h60 h62 h64 h65

theorem level_atoms_core (C R tag : Nat) (cs : List Pair) (initial : List PacketVector.Packet)
    (left : PacketVector.Packet) (A : Fin 256→List Bool)
    (hengine : ∀i : Fin 34,A (i.castAdd 222)=ReusableArithmetic.state C R left [] i)
    (atag : A 187=ZeroPadding.pad R (CompareMachine.word tag))
    (acount : A 184=ZeroPadding.pad R (CompareMachine.word cs.length))
    (ht : tag+2≤R) (hc : cs.length+2≤R) :
    ∀i : Fin 34,levelAtomsOutput C R tag cs initial A (i.castAdd 222)=ReusableArithmetic.state C R left [] i := by
  intro i
  have hib : (i.castAdd 222 : Fin 256).val<34 := i.isLt
  have hi : ¬Workspace.selected (i.castAdd 222) := by unfold Workspace.selected;omega
  have hn (n : Nat) (hn : 34≤n) (hne : n<256) : i.castAdd 222≠(⟨n,hne⟩ : Fin 256) := by
    intro he
    have hh : i.val=n := congrArg (fun k : Fin 256=>k.val) he
    have hil:=i.isLt
    omega
  rw [level_atoms_outside_work C R tag cs initial A _ hi (hn 129 (by decide) (by decide))
    (hn 140 (by decide) (by decide))]
  exact (cache_retained R tag cs.length A (hengine 32) (hengine 33) (hengine 31)
    atag acount ht hc _ (by omega) (hn 186 (by decide) (by decide))).trans (hengine i)

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
