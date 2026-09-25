import Proof.Rows.SelectedPowerReady

/-! Extract one actual TOP circuit into the reusable coefficient cell. Only
payload94 is additionally padded; the growing coefficient stream is untouched. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_CircuitPowerInput
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal SignedSortKey
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_TopFrameReentry.machine
attribute [local irreducible] PCJ45bee56da9f34d5a_SelectedPowerReady.machine

def caps (U :Nat) (i :Fin 101):=if i=94 then U else 0
def bank (a B p w F U v key circuit :Nat) (source payload out :List Bool):Fin 103→List Bool:=
 Fin.addCases (m:=101) (n:=2) (motive:=fun _=>List Bool)
  (fun i=>ZeroPadding.pad (caps U i) (PCJ45bee56da9f34d5a_SelectedPowerPrepare.bank a B p w F U 0 0 v key payload out i))
  ![frame source,ZeroPadding.pad U (CompareMachine.word circuit)]
def heads (len :Nat):Fin 103→Nat:=Fin.addCases (m:=101) (n:=2) (motive:=fun _=>Nat)
 (PCJ45bee56da9f34d5a_SelectedPowerPrepare.heads len 0 0) ![0,1]
def slots:Fin 10→Fin 103:=![101,31,32,102,33,34,94,35,62,63]
def extract:=RecoveryFocus.machine slots PCJ45bee56da9f34d5a_TopFrameReentry.machine
def evaluate:=TapeEmbedding.machine 2 PCJ45bee56da9f34d5a_SelectedPowerReady.machine
def wipeSlots:Fin 3→Fin 103:=![94,62,63]
def wipe:=RecoveryFocus.machine wipeSlots (RecoveryScratchErase.resetMachine 1)
def machine:=Composition.machine (Composition.machine extract evaluate) wipe

theorem at62 (a B p w F U v key circuit :Nat) (source payload out :List Bool):
 bank a B p w F U v key circuit source payload out 62=List.replicate U true :=by
 change ZeroPadding.pad 0 (PCJ45bee56da9f34d5a_SelectedPowerPrepare.bank a B p w F U 0 0 v key payload out 62)=_
 rw [ZeroPadding.pad_zero,PCJ45bee56da9f34d5a_SelectedPowerPrepare.at62]
theorem at63 (a B p w F U v key circuit :Nat) (source payload out :List Bool):
 bank a B p w F U v key circuit source payload out 63=List.replicate (U+1) false :=by
 change ZeroPadding.pad 0 (PCJ45bee56da9f34d5a_SelectedPowerPrepare.bank a B p w F U 0 0 v key payload out 63)=_
 rw [ZeroPadding.pad_zero,PCJ45bee56da9f34d5a_SelectedPowerPrepare.at63]

theorem work (a B p w F U v key circuit :Nat) (source payload out :List Bool) (j :Fin 5):
 bank a B p w F U v key circuit source payload out ⟨31+j.val,by omega⟩=List.replicate U false :=by
 fin_cases j
 all_goals change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate U false)))=_
 all_goals rw [ZeroPadding.pad_zero,ZeroPadding.pad_zero,ZeroPadding.pad_zero]

theorem payload_away (a B p w F U v key circuit :Nat) (source payload payload' out :List Bool)
 (i :Fin 103) (hi : i≠94):
 bank a B p w F U v key circuit source payload out i=bank a B p w F U v key circuit source payload' out i :=by
 revert hi
 refine Fin.addCases (m:=101) (n:=2) (fun j hj=>?_) (fun _ _=>?_) i
 · simp only [bank,Fin.addCases_left]
   apply congrArg (ZeroPadding.pad (caps U j))
   revert hj
   refine Fin.addCases (m:=99) (n:=2) (fun k hk=>?_) (fun _ _=>?_) j
   · simp only [PCJ45bee56da9f34d5a_SelectedPowerPrepare.bank,Fin.addCases_left]
     revert hk
     refine Fin.addCases (m:=94) (n:=5) (fun _ _=>?_) (fun l hl=>?_) k
     · simp only [PCJ45bee56da9f34d5a_SelectedPowerBank.bank,Fin.addCases_left]
     · fin_cases l <;>first | exact False.elim (hl rfl) | rfl
   · simp only [PCJ45bee56da9f34d5a_SelectedPowerPrepare.bank,Fin.addCases_right]
 · simp only [bank,Fin.addCases_right]

theorem extract_run (words :List (List Bool)) (i :Fin words.length) (C a B p w F U v key :Nat) (out :List Bool)
 (hb : ∀x∈words,x.length≤C) (hu : PCJ45bee56da9f34d5a_TopFrameReentry.budget words i C+2≤U) :
 Step extract (PCJ45bee56da9f34d5a_TopFrameReentry.budget words i C+4*U+12)
  (heads out.length) (bank a B p w F U v key i.val (words.flatMap frame) [] out)
  (heads out.length) (bank a B p w F U v key i.val (words.flatMap frame) (words.get i) out) :=by
 have h:=(PCJ45bee56da9f34d5a_TopFrameReentry.run words i C U hb hu).dock slots (by decide)
  (heads out.length) (bank a B p w F U v key i.val (words.flatMap frame) [] out)
  (by intro j;fin_cases j <;>rfl)
  (by
   intro j;fin_cases j
   · rfl
   · exact work a B p w F U v key i.val _ [] out 0
   · exact work a B p w F U v key i.val _ [] out 1
   · rfl
   · exact work a B p w F U v key i.val _ [] out 2
   · exact work a B p w F U v key i.val _ [] out 3
   · rfl
   · exact work a B p w F U v key i.val _ [] out 4
   · exact at62 a B p w F U v key i.val _ [] out
   · exact at63 a B p w F U v key i.val _ [] out)
 apply h.congr
 · exact dockH_existing _ _ _ (by intro j;fin_cases j <;>rfl)
 · apply HierarchyAllocation.install_eq slots (by decide)
   · intro j;fin_cases j
     · rfl
     · exact work a B p w F U v key i.val _ _ out 0
     · exact work a B p w F U v key i.val _ _ out 1
     · rfl
     · exact work a B p w F U v key i.val _ _ out 2
     · exact work a B p w F U v key i.val _ _ out 3
     · rfl
     · exact work a B p w F U v key i.val _ _ out 4
     · exact at62 a B p w F U v key i.val _ _ out
     · exact at63 a B p w F U v key i.val _ _ out
   · intro j hj;exact (payload_away a B p w F U v key i.val _ [] _ out j (fun he=>hj 6 he.symm)).symm

theorem wipe_run (a B p w F U v key circuit :Nat) (source payload out :List Bool) (hp : payload.length≤U):
 Step wipe (2*U+4) (heads out.length) (bank a B p w F U v key circuit source payload out)
  (heads out.length) (bank a B p w F U v key circuit source [] out) :=by
 have h:=(Step.of_ready (RecoveryScratchErase.erase_ready U (U+1)
  (fun _ :Fin 1=>ZeroPadding.pad U payload)
  (by intro j;rw [ZeroPadding.pad_length];exact max_le (le_refl _) hp))).dock wipeSlots (by decide)
  (heads out.length) (bank a B p w F U v key circuit source payload out)
  (by intro j;fin_cases j <;>rfl)
  (by
   intro j;fin_cases j
   · rfl
   · exact at62 a B p w F U v key circuit source payload out
   · exact at63 a B p w F U v key circuit source payload out)
 apply h.congr
 · exact dockH_existing _ _ _ (by intro j;fin_cases j <;>rfl)
 · apply HierarchyAllocation.install_eq wipeSlots (by decide)
   · intro j;fin_cases j <;>simp only [Nat.max_self]
     · rfl
     · exact at62 a B p w F U v key circuit source [] out
     · exact at63 a B p w F U v key circuit source [] out
   · intro j hj;exact (payload_away a B p w F U v key circuit source payload [] out j (fun he=>hj 0 he.symm)).symm
end
end PCJ45bee56da9f34d5a_CircuitPowerInput
