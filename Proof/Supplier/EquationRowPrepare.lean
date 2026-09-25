import Proof.Supplier.EquationRowAllocate

/-! From the original framed row alone, prepare the exact reusable cut-loop
workspace and physically advance its three sentinel-count heads. -/
namespace NearCubicWires.RepairOrdinary.EquationRowPrepare
open LocalBitMultitape RecoveryExecution RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 126) : Prop := i=34 ∨ i=38 ∨ i=40
instance (i : Fin 126) : Decidable (selected i) := inferInstanceAs (Decidable (i=34 ∨ i=38 ∨ i=40))
def boot : Machine 126 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun _ _ => some ⟨1,fun _ => none,fun i => if selected i then .right else .stay⟩
def afterHeads (h : Fin 126 → ℕ) (i : Fin 126) := if selected i then h i+1 else h i

theorem boot_run (h : Fin 126 → ℕ) (a : Fin 126 → List Bool) :
    ∃ actual,runFrom boot 1 ⟨0,h,a⟩=some actual ∧
      actual.final.heads=afterHeads h ∧ actual.final.tapes=a ∧ actual.steps=1 := by
  let final : Configuration 126 2 := ⟨1,afterHeads h,a⟩
  have hs : step boot ⟨0,h,a⟩=some final := by
    simp only [step,boot]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i
      simp only [applyAction,afterHeads,final]
      split_ifs <;> rfl
    · rfl
  obtain ⟨actual,ha,hf,ht⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨actual,ha,congrArg Configuration.heads hf,congrArg Configuration.tapes hf,ht⟩

noncomputable def first := TapeEmbedding.machine 15 EquationHeaderCold.machine
noncomputable def allocated := Composition.machine first EquationRowAllocate.machine
noncomputable def machine := Composition.machine allocated boot
def input (d p g : ℕ) (odd : Bool) (suffix : List Bool) : Fin 126 → List Bool :=
  fun i => if i=0 then frame (EquationHeaderRead.word d p g (odd::suffix)) else []
def capacity (d p : ℕ) := 128*(2*d+1)*(p+1)
def bank (j : Fin 32) : Fin 126 := (EquationHeaderCold.bank j).castAdd 15
def bankHead (j : Fin 32) := if selected (bank j) then 1 else 0
def budget (d p g : ℕ) (odd : Bool) (suffix : List Bool) :=
  EquationHeaderCold.budget d p g odd suffix+2*capacity d p+7

theorem prepare_run (d p g : ℕ) (odd : Bool) (suffix : List Bool) : ∃ actual,
    run machine (budget d p g odd suffix) (input d p g odd suffix)=some actual ∧
    actual.final.tapes 0=frame (EquationHeaderRead.word d p g (odd::suffix)) ∧ actual.final.heads 0=0 ∧
    actual.final.tapes 1=EquationHeaderRead.word d p g (odd::suffix) ∧
      actual.final.heads 1=(EquationHeaderRead.header d p g).length+1 ∧
    actual.final.tapes 110=EquationHeaderRead.header d (p+1) (2*g) ∧
      actual.final.heads 110=(EquationHeaderRead.header d (p+1) (2*g)).length ∧
    (∀ j,j≠12 → j≠14 → j≠20 →
      actual.final.tapes (bank j)=EquationCountCapacity.data8 d p g odd j ∧ actual.final.heads (bank j)=bankHead j) ∧
    (∀ i : Fin 15,actual.final.tapes (i.natAdd 111)=EquationRowAllocate.extra (capacity d p) i ∧
      actual.final.heads (i.natAdd 111)=0) ∧ actual.steps ≤ budget d p g odd suffix := by
  obtain ⟨base,hb,bt0,bh0,bt1,bh1,btOut,bhOut,fields,bs⟩ := EquationHeaderCold.cold_run d p g odd suffix
  let prepared := TapeEmbedding.receipt (fun _ : Fin 15 => 0) (fun _ : Fin 15 => []) base
  have he := TapeEmbedding.run_embed EquationHeaderCold.machine (fun _ : Fin 15 => 0)
    (fun _ : Fin 15 => []) _ _ base hb
  obtain ⟨alloc,ha,old,fresh,ast⟩ := EquationRowAllocate.allocate_run base.final (capacity d p)
    (by
      have h := (fields 30 (by decide) (by decide) (by decide)).1
      change base.final.tapes 60=List.replicate ((2*d+1)*(p+1)*128) true at h
      simpa only [capacity,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using h)
    (fields 30 (by decide) (by decide) (by decide)).2
  have ha' : runFrom EquationRowAllocate.machine (2*capacity d p+4)
      (Composition.restart prepared.final EquationRowAllocate.machine.start)=some alloc := ha
  have hj := Composition.run_join first EquationRowAllocate.machine _ _ _ prepared alloc he ha'
  obtain ⟨last,hl,lh,lt,ls⟩ := boot_run alloc.final.heads alloc.final.tapes
  have hw := Composition.run_join allocated boot _ _ _ (Composition.joinedReceipt prepared alloc) last hj hl
  have hin : Composition.leftConfig _ (Composition.leftConfig _
      (TapeEmbedding.config (fun _ : Fin 15 => 0) (fun _ : Fin 15 => [])
        (initialConfiguration EquationHeaderCold.machine (EquationHeaderCold.input d p g odd suffix))))=
      initialConfiguration machine (input d p g odd suffix) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at hw
  have keepT (i : Fin 111) : last.final.tapes (i.castAdd 15)=base.final.tapes i := by
    rw [lt]
    exact (old i).1
  have keepH (i : Fin 111) : last.final.heads (i.castAdd 15)=
      if selected (i.castAdd 15) then base.final.heads i+1 else base.final.heads i := by
    rw [lh]
    simp only [afterHeads,(old i).2]
  refine ⟨Composition.joinedReceipt (Composition.joinedReceipt prepared alloc) last,?_,
    (keepT 0).trans bt0,?_,(keepT 1).trans bt1,?_,(keepT 110).trans btOut,?_,?_,?_,?_⟩
  · have hn : (EquationHeaderCold.budget d p g odd suffix+1+(2*capacity d p+4))+1+1=
        budget d p g odd suffix := by unfold budget; omega
    simpa only [run,machine,hn] using hw
  · change last.final.heads (Fin.castAdd 15 (0 : Fin 111))=0
    rw [keepH]
    exact bh0
  · change last.final.heads (Fin.castAdd 15 (1 : Fin 111))=_
    rw [keepH]
    exact bh1
  · change last.final.heads (Fin.castAdd 15 (110 : Fin 111))=_
    rw [keepH]
    exact bhOut
  · intro j h12 h14 h20
    constructor
    · exact (keepT (EquationHeaderCold.bank j)).trans (fields j h12 h14 h20).1
    · change last.final.heads ((EquationHeaderCold.bank j).castAdd 15)=_
      rw [keepH,(fields j h12 h14 h20).2]
      rfl
  · intro i
    constructor
    · change last.final.tapes (i.natAdd 111)=_
      rw [lt]
      exact (fresh i).1
    · change last.final.heads (i.natAdd 111)=0
      rw [lh]
      have hn : ¬selected (i.natAdd 111) := by
        intro h
        rcases h with h|h|h <;> have hv := congrArg Fin.val h <;> simp only [Fin.val_natAdd] at hv <;> norm_num at hv <;> omega
      simp only [afterHeads,hn,ite_false,(fresh i).2]
  · change (base.steps+1+alloc.steps)+1+last.steps ≤ _
    rw [ast,ls]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.EquationRowPrepare
