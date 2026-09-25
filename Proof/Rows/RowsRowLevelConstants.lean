import Proof.Rows.RowsRowLevelFields
import Proof.Assembly.RowsConstantRun

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsRowLevel
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.P1Closure
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimator
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open CompetitorCrossScheduler (producer)
attribute [local irreducible] CompetitorCrossScheduler.producer P1TopDownPaidPayload.tapes
noncomputable section

/-! ## 1. The transducer docked at arbitrary ports -/

/-- Transducer slot map: four driver ports, eleven output ports, one counter port. -/
def constSlots {T : Nat} (src : Fin 4 → Fin T) (outp : Fin 11 → Fin T) (ctr : Fin T) :
    Fin 16 → Fin T :=
  fun i=>Fin.addCases (m:=15) (n:=1)
    (fun j=>Fin.addCases (m:=4) (n:=11) src outp j) (fun _ : Fin 1=>ctr) i

theorem constSlots_src {T : Nat} (src : Fin 4 → Fin T) (outp : Fin 11 → Fin T) (ctr : Fin T)
    (k : Fin 4) : constSlots src outp ctr ((k.castAdd 11).castAdd 1)=src k := by
  simp only [constSlots,Fin.addCases_left]

theorem constSlots_out {T : Nat} (src : Fin 4 → Fin T) (outp : Fin 11 → Fin T) (ctr : Fin T)
    (m : Fin 11) : constSlots src outp ctr ((m.natAdd 4).castAdd 1)=outp m := by
  simp only [constSlots,Fin.addCases_left,Fin.addCases_right]

theorem constSlots_ctr {T : Nat} (src : Fin 4 → Fin T) (outp : Fin 11 → Fin T) (ctr : Fin T)
    (j : Fin 1) : constSlots src outp ctr (j.natAdd 15)=ctr := by
  simp only [constSlots,Fin.addCases_right]

/-- The padding the docked run uses: driver reserves, `K` on the outputs, `S` on the counter. -/
def constCap (rs : Fin 4 → Nat) (K S : Nat) : Fin 16 → Nat :=
  fun i=>Fin.addCases (m:=15) (n:=1)
    (fun j=>Fin.addCases (m:=4) (n:=11) rs (fun _ : Fin 11=>K) j) (fun _ : Fin 1=>S) i

theorem pad_nil (K : Nat) : ZeroPadding.pad K []=List.replicate K false := by
  simp [ZeroPadding.pad]

/-- **The docked transducer.** From any ambient whose driver ports carry the four padded
driver words, whose eleven output ports are blank `0^K`, and whose counter port is blank
`0^S` with `S ≥ rawBudget`, all slot heads at `0`: one fixed machine writes
`pad K (fields p n Q C k)` on output `k` and restores every other port and every head. -/
theorem const_step {T : Nat} (src : Fin 4 → Fin T) (outp : Fin 11 → Fin T) (ctr : Fin T)
    (hinj : Function.Injective (constSlots src outp ctr)) (p n Q C : Nat)
    (rs : Fin 4 → Nat) (K S : Nat) (hS : PCJ45bee56da9f34d5a_Constants.rawBudget p n Q C ≤ S)
    (H : Fin T → Nat) (A : Fin T → List Bool)
    (hH : ∀ i,H (constSlots src outp ctr i)=0)
    (hsrc : ∀ k,A (src k)=ZeroPadding.pad (rs k) (PCJ45bee56da9f34d5a_Constants.source p n Q C k))
    (hout : ∀ k,A (outp k)=List.replicate K false)
    (hctr : A ctr=List.replicate S false) :
    Step (RecoveryFocus.machine (constSlots src outp ctr) PCJ45bee56da9f34d5a_Constants.machine)
      (2*PCJ45bee56da9f34d5a_Constants.rawBudget p n Q C+2) H A
      H (install outp A (fun k=>ZeroPadding.pad K (PCJ45bee56da9f34d5a_Constants.fields p n Q C k))) := by
  have base := (PCJ45bee56da9f34d5a_Constants.run p n Q C).pad (constCap rs K S)
  have hin : ∀ i,A (constSlots src outp ctr i)=
      ZeroPadding.pad (constCap rs K S i) (PCJ45bee56da9f34d5a_Constants.input p n Q C i) := by
    intro i
    refine Fin.addCases (m:=15) (n:=1) (fun j=>?_) (fun j=>?_) i
    · refine Fin.addCases (m:=4) (n:=11) (fun k=>?_) (fun k=>?_) j
      · simp only [constSlots,constCap,PCJ45bee56da9f34d5a_Constants.input,Fin.addCases_left]
        rw [hsrc]
        rfl
      · simp only [constSlots,constCap,PCJ45bee56da9f34d5a_Constants.input,Fin.addCases_left,
          Fin.addCases_right]
        rw [hout,pad_nil]
    · simp only [constSlots,constCap,PCJ45bee56da9f34d5a_Constants.input,Fin.addCases_right]
      rw [hctr,pad_nil]
  have docked := base.dock (constSlots src outp ctr) hinj H A hH hin
  refine docked.congr (dockH_existing _ _ _ hH) ?_
  funext x
  classical
  by_cases hx : ∃ i,constSlots src outp ctr i=x
  · obtain ⟨i,rfl⟩ := hx
    rw [install_slot _ hinj]
    refine Fin.addCases (m:=15) (n:=1) (fun j=>?_) (fun j=>?_) i
    · refine Fin.addCases (m:=4) (n:=11) (fun k=>?_) (fun k=>?_) j
      · have hk : ∀ m,outp m≠constSlots src outp ctr ((k.castAdd 11).castAdd 1) := by
          intro m he
          rw [←constSlots_out src outp ctr m] at he
          have hv := congrArg Fin.val (hinj he)
          simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
          have := k.isLt
          omega
        rw [install_other _ _ _ _ hk]
        simp only [constSlots,constCap,PCJ45bee56da9f34d5a_Constants.output,Fin.addCases_left]
        rw [hsrc]
      · have he := constSlots_out src outp ctr k
        have hi : Function.Injective outp := by
          intro a b hab
          rw [←constSlots_out src outp ctr a,←constSlots_out src outp ctr b] at hab
          have hv := congrArg Fin.val (hinj hab)
          simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
          exact Fin.ext (by omega)
        rw [he,install_slot _ hi]
        simp only [constCap,PCJ45bee56da9f34d5a_Constants.output,Fin.addCases_left,Fin.addCases_right]
    · have hk : ∀ m,outp m≠constSlots src outp ctr (j.natAdd 15) := by
        intro m he
        rw [←constSlots_out src outp ctr m] at he
        have hv := congrArg Fin.val (hinj he)
        simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
        have := m.isLt
        omega
      rw [install_other _ _ _ _ hk]
      simp only [constSlots,constCap,PCJ45bee56da9f34d5a_Constants.output,Fin.addCases_right]
      rw [hctr,pad_replicate_false _ _ hS]
  · have hn : ∀ i,constSlots src outp ctr i≠x := fun i he=>hx ⟨i,he⟩
    rw [install_other _ _ _ _ hn,install_other _ _ _ _ (fun m he=>hn ((m.natAdd 4).castAdd 1)
      ((constSlots_out src outp ctr m).trans he))]

/-! ## 2. The eleven transducer outputs are eleven datum fields, framed -/

/-- Which of the thirteen fields transducer output `k` is. -/
def constIdx : Fin 11 → Fin 13 := ![0,1,3,4,5,6,7,9,10,11,12]

theorem constIdx_injective : Function.Injective constIdx := by decide

/-- **Transducer output = framed datum field.** For a datum whose Prepare/warm constants are the
transducer's parameters (`d.row.d=⌈n/2⌉`, `d.row.odd=(n odd)`, `d.row.p=p`, `d.Q=Q`, `d.C=C`). -/
theorem const_fields (d : P1TopDownPaidReusable.Datum) (p n Q C : Nat)
    (hd : d.row.d=(n+1)/2) (hodd : d.row.odd=decide (n%2=1)) (hp : d.row.p=p)
    (hQ : d.Q=Q) (hC : d.C=C) (k : Fin 11) :
    PCJ45bee56da9f34d5a_Constants.fields p n Q C k=frame (fieldWord d (constIdx k)) := by
  have hb : CompetitorSelectedCount.scalarWidth (EquationRow.request d.row) Q=
      Q+2*((n+1)/2)+2*p+6 := by
    rw [CompetitorSelectedCount.scalarWidth,CompetitorSelectedCount.extraWidth_eq]
    change Q+(2*d.row.d+2*(d.row.p+1)+4)=_
    rw [hd,hp]
    omega
  fin_cases k <;>
    simp only [PCJ45bee56da9f34d5a_Constants.fields,fieldWord,constIdx,WarmFields.words,hb,
      CompetitorRationalDecision.width,P1TopDownPaidPayload.estimate,hd,hodd,hp,hQ,hC] <;> rfl

/-! ## 3. The docked transducer at the thirteen field slots -/

/-- **C2 at the row bank.** Outputs on the eleven transducer field slots; the drivers and the
counter are wherever the caller keeps them (`src`, `ctr`). Exit: exactly those eleven slots
changed, each to `pad K (frame (fieldWord d ·))`. -/
theorem const_row_step (printer : WilliamsAlgorithm) (t : Nat)
    (src : Fin 4 → Fin (PCJ38fbfed565f64139_Ready.tapes printer t))
    (ctr : Fin (PCJ38fbfed565f64139_Ready.tapes printer t))
    (hinj : Function.Injective (constSlots src (fieldSlot printer t ∘ constIdx) ctr))
    (d : P1TopDownPaidReusable.Datum) (p n Q C : Nat)
    (hd : d.row.d=(n+1)/2) (hodd : d.row.odd=decide (n%2=1)) (hp : d.row.p=p)
    (hQ : d.Q=Q) (hC : d.C=C)
    (rs : Fin 4 → Nat) (K S : Nat) (hS : PCJ45bee56da9f34d5a_Constants.rawBudget p n Q C ≤ S)
    (H : Fin (PCJ38fbfed565f64139_Ready.tapes printer t) → Nat)
    (A : Fin (PCJ38fbfed565f64139_Ready.tapes printer t) → List Bool)
    (hH : ∀ i,H (constSlots src (fieldSlot printer t ∘ constIdx) ctr i)=0)
    (hsrc : ∀ k,A (src k)=ZeroPadding.pad (rs k) (PCJ45bee56da9f34d5a_Constants.source p n Q C k))
    (hout : ∀ k,A (fieldSlot printer t (constIdx k))=List.replicate K false)
    (hctr : A ctr=List.replicate S false) :
    Step (RecoveryFocus.machine (constSlots src (fieldSlot printer t ∘ constIdx) ctr)
        PCJ45bee56da9f34d5a_Constants.machine)
      (2*PCJ45bee56da9f34d5a_Constants.rawBudget p n Q C+2) H A
      H (install (fieldSlot printer t ∘ constIdx) A
        (fun k=>ZeroPadding.pad K (frame (fieldWord d (constIdx k))))) := by
  have h := const_step src (fieldSlot printer t ∘ constIdx) ctr hinj p n Q C rs K S hS H A hH hsrc
    hout hctr
  have hf : (fun k=>ZeroPadding.pad K (PCJ45bee56da9f34d5a_Constants.fields p n Q C k))=
      (fun k=>ZeroPadding.pad K (frame (fieldWord d (constIdx k)))) := by
    funext k
    rw [const_fields d p n Q C hd hodd hp hQ hC]
  rw [hf] at h
  exact h


end
end RowsRowLevel
