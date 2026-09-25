import Proof.Packets.PacketsMetaMaps
import Proof.Rows.RowsInitHeaderWords

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace RowsInit
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.PacketsGlue.RequestMeta
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent
noncomputable section

theorem liveCounter_run (n : Nat) : ∃ out,
    Step NearCubicWires.RepairSource.ProjectionNormalization.Counter.machine
      (NearCubicWires.RepairSource.ProjectionNormalization.Counter.budget n) (fun _ => 0)
      (NearCubicWires.RepairSource.ProjectionNormalization.Counter.input n) (fun _ => 0) out ∧
      out 0 = List.replicate n true ∧ out 2 = NearCubicWires.RepairSource.VerifierDecoding.CompareMachine.word n := by
  obtain ⟨out, h, h0, h2⟩ := NearCubicWires.RepairSource.ProjectionNormalization.DriverAtoms.counter_run n
  exact ⟨out, NearCubicWires.RepairSource.CloseoutFinal.C10CompareDockLit.step_of_clock h, h0, h2⟩

/-! ## 1. `CountFalse`: one `true` per payload `false` of a frame -/

namespace CountFalse

/-- Tapes: 0 source (a frame), 1 unary output. States: 0 marker, 1 payload, 2 halt. -/
def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q bits =>
    if q.val = 0 then some (if bits 0 then ⟨1, fun _ => none, ![.right, .stay]⟩
      else ⟨2, fun _ => none, fun _ => .stay⟩)
    else if q.val = 1 then some (if bits 0 then ⟨0, fun _ => none, ![.right, .stay]⟩
      else ⟨0, ![none, some true], ![.right, .right]⟩)
    else none

def cfg (q : Fin 3) (src : List Bool) (sh c : ℕ) : Configuration 2 3 :=
  ⟨q, ![sh, c], ![src, List.replicate c true]⟩

theorem mark_step (src : List Bool) (sh c : ℕ) (h : readTapeBit src sh = true) :
    step machine (cfg 0 src sh c) = some (cfg 1 src (sh+1) c) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem one_step (src : List Bool) (sh c : ℕ) (h : readTapeBit src sh = true) :
    step machine (cfg 1 src sh c) = some (cfg 0 src (sh+1) c) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem zero_step (src : List Bool) (sh c : ℕ) (h : readTapeBit src sh = false) :
    step machine (cfg 1 src sh c) = some (cfg 0 src (sh+1) (c+1)) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, write_end_replicate]

theorem end_step (src : List Bool) (sh c : ℕ) (h : readTapeBit src sh = false) :
    step machine (cfg 0 src sh c) = some (cfg 2 src sh c) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem scan_timed (pre w rest : List Bool) (c : ℕ) :
    Timed machine (2 * w.length) (cfg 0 (pre ++ frame w ++ rest) pre.length c)
      (cfg 0 (pre ++ frame w ++ rest) (pre.length + 2 * w.length) (c + w.count false)) := by
  induction w generalizing pre c with
  | nil => simpa using Timed.refl machine (cfg 0 (pre ++ frame [] ++ rest) pre.length c)
  | cons b w ih =>
    have hw : pre ++ frame (b :: w) ++ rest = (pre ++ [true, b]) ++ frame w ++ rest := by
      simp [frame_cons, List.append_assoc]
    have hm : readTapeBit (pre ++ frame (b :: w) ++ rest) pre.length = true := by
      rw [read_start pre _ rest (frame_pos _)]; rfl
    have hb : readTapeBit (pre ++ frame (b :: w) ++ rest) (pre.length+1) = b := by
      have h := read_shift pre (frame (b :: w)) rest 1 (by simp [frame_cons])
      rw [h]; rfl
    have s1 := Timed.single (p := machine) (by rfl) (mark_step _ _ c hm)
    have hl : (pre ++ [true, b]).length = pre.length + 1 + 1 := by simp
    cases b with
    | true =>
      have s2 := Timed.single (p := machine) (by rfl) (one_step _ (pre.length+1) c hb)
      have s3 := ih (pre ++ [true, true]) c
      rw [← hw, hl] at s3
      have h := (s1.trans s2).trans s3
      have e1 : 1 + 1 + 2 * w.length = 2 * (true :: w).length := by simp; omega
      have e2 : pre.length + 1 + 1 + 2 * w.length = pre.length + 2 * (true :: w).length := by simp; omega
      have e3 : c + w.count false = c + (true :: w).count false := by simp
      rw [e1, e2, e3] at h
      exact h
    | false =>
      have s2 := Timed.single (p := machine) (by rfl) (zero_step _ (pre.length+1) c hb)
      have s3 := ih (pre ++ [true, false]) (c+1)
      rw [← hw, hl] at s3
      have h := (s1.trans s2).trans s3
      have e1 : 1 + 1 + 2 * w.length = 2 * (false :: w).length := by simp; omega
      have e2 : pre.length + 1 + 1 + 2 * w.length = pre.length + 2 * (false :: w).length := by simp; omega
      have e3 : c + 1 + w.count false = c + (false :: w).count false := by simp; omega
      rw [e1, e2, e3] at h
      exact h

/-- **The count.** Exactly `(frame w).length` steps; output `replicate (w.count false) true`. -/
theorem run (pre w rest : List Bool) :
    ∃ r : ExecutionReceipt 2 3,
      runFrom machine (frame w).length (cfg 0 (pre ++ frame w ++ rest) pre.length 0) = some r ∧
      r.final = cfg 2 (pre ++ frame w ++ rest) (pre.length + 2 * w.length) (w.count false) ∧
      r.steps = (frame w).length := by
  have hs := scan_timed pre w rest 0
  have he : readTapeBit (pre ++ frame w ++ rest) (pre.length + 2 * w.length) = false := by
    rw [read_shift pre (frame w) rest (2 * w.length) (by simp), NearCubicWires.PacketsGlue.frame_eq_dbl]
    have h := read_suffix (NearCubicWires.PacketsGlue.dbl w) [false] 0
    rw [NearCubicWires.PacketsGlue.dbl_length, Nat.add_zero] at h
    rw [h]
    rfl
  have s := hs.trans (Timed.single (p := machine) (by rfl) (end_step _ _ _ he))
  rw [Nat.zero_add] at s
  obtain ⟨r, hr, hf, hsteps⟩ := s.run rfl
  have e : 2 * w.length + 1 = (frame w).length := by simp
  rw [e] at hr hsteps
  exact ⟨r, hr, hf, hsteps⟩

end CountFalse

theorem countFalse_step (w : List Bool) :
    Step CountFalse.machine (frame w).length ![0, 0] ![frame w, []]
      ![2 * w.length, w.count false] ![frame w, List.replicate (w.count false) true] := by
  have h := CountFalse.run [] w []
  simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at h
  obtain ⟨r, hr, hf, _⟩ := h
  exact Step.of_run (hin := ![0, 0]) (tin := ![frame w, []]) hr
    (by rw [hf]; rfl) (by rw [hf]; rfl)

/-! ## 2. The complement count `n = (live F)ᶜ.card` as a `RequestMeta.UnaryStage` -/

/-- `n`: the number of non-live coordinates (the pool arity, `Packets.Geometry.arity`). -/
def complCount (a : DecompositionAlgorithm) (r : Request) : ℕ := (live a r)ᶜ.card

theorem count_ofFn_compl {q : ℕ} (S : Finset (Fin q)) :
    (List.ofFn (fun x : Fin q => decide (x ∈ S))).count false = Sᶜ.card := by
  have h1 := count_ofFn_mem S
  have h2 := List.count_true_add_count_false (List.ofFn (fun x : Fin q => decide (x ∈ S)))
  rw [List.length_ofFn] at h2
  rw [Finset.card_compl, Fintype.card_fin]
  omega

/-- `n` is the number of `false`s of the mask field. -/
theorem count_mask_false (a : DecompositionAlgorithm) (r : Request) :
    (fields a r 2).count false = complCount a r := by
  change (CyclicChoice.mask (r.family a).occurrences r.liveScale).count false = _
  unfold CyclicChoice.mask
  rw [count_ofFn_compl]
  rfl

/-- **`complCount` (n) stage** (PG's `liveStage` with `CountFalse`). -/
def complStage (a : DecompositionAlgorithm) : UnaryStage a (complCount a) where
  extra := 13
  states := _
  machine := fieldMachine CountFalse.machine 2
  cost := fun r => 6*(r.input a).length+17 + 1 + (2*(frame (fields a r 2)).length+2)
  coefficient := 28
  degree := 1
  cost_le := fun r => cost_bound a r 2
  run := by
    intro r
    obtain ⟨H', A', hs, h0, hh0, h1, hh1⟩ := field_run CountFalse.machine 2 a r
      ((fields a r 2).count false) _ _ (countFalse_step (fields a r 2))
    exact ⟨H', A', hs, h0, hh0, by rw [h1, count_mask_false], hh1⟩

/-! ## 3. Any `UnaryStage`, with every head returned to `0` -/

theorem zeros_addCases (m n : Nat) :
    Fin.addCases (m:=m) (n:=n) (motive:=fun _=>Nat) (fun _=>0) (fun _=>0)=fun _=>0 := by
  funext i
  refine Fin.addCases (m:=m) (n:=n) (fun j=>?_) (fun j=>?_) i
  · rw [Fin.addCases_left]
  · rw [Fin.addCases_right]

theorem zeros_masked {m : Nat} (H : Fin m → Nat) :
    Fin.addCases (m:=m) (n:=1) (motive:=fun _=>Nat) (fun i=>if (fun _ : Fin m=>true) i then 0 else H i)
      (fun _=>0)=fun _=>0 := by
  funext i
  refine Fin.addCases (m:=m) (n:=1) (fun j=>?_) (fun j=>?_) i
  · rw [Fin.addCases_left]
    rfl
  · rw [Fin.addCases_right]

/-- A stage under the all-heads masked reset: heads `0 → 0`, tape 0 kept, tape 1 = `1^v`. -/
theorem stage_masked {a : DecompositionAlgorithm} {v : Request → ℕ} (s : UnaryStage a v) (r : Request) :
    ∃ A : Fin (2+s.extra+1) → List Bool,
      Step (MaskedReset.machine s.machine (fun _=>true)) (2*s.cost r+2) (fun _=>0)
        (Fin.addCases (inBank (2+s.extra) (Request.input a r)) (fun _ : Fin 1=>[])) (fun _=>0) A ∧
      A ⟨0,by omega⟩=frame (Request.input a r) ∧ A ⟨1,by omega⟩=List.replicate (v r) true := by
  obtain ⟨H',A',h,a0,-,a1,-⟩ := s.run r
  obtain ⟨k,-,m⟩ := mask_empty h (fun _=>true) (fun _ _=>rfl)
  refine ⟨Fin.addCases (m:=2+s.extra) (n:=1) (motive:=fun _=>List Bool) A' (fun _=>List.replicate k false),
    (m.congr_in (zeros_addCases _ _) rfl).congr (zeros_masked H') rfl,?_,?_⟩
  · have e : (⟨0,by omega⟩ : Fin (2+s.extra+1))=Fin.castAdd 1 (⟨0,by omega⟩ : Fin (2+s.extra)) := rfl
    rw [e,Fin.addCases_left,a0]
  · have e : (⟨1,by omega⟩ : Fin (2+s.extra+1))=Fin.castAdd 1 (⟨1,by omega⟩ : Fin (2+s.extra)) := rfl
    rw [e,Fin.addCases_left,a1]

theorem inBank_blank (e : Nat) (w : List Bool) (j : Fin (2+e+1)) (hj : j.val≠0) :
    Fin.addCases (m:=2+e) (n:=1) (motive:=fun _=>List Bool) (inBank (2+e) w) (fun _=>[]) j=[] := by
  revert hj
  refine Fin.addCases (m:=2+e) (n:=1) (fun i=>?_) (fun i=>?_) j
  · intro hj
    rw [Fin.addCases_left]
    have : i.val≠0 := by simpa using hj
    simp [inBank,this]
  · intro _
    rw [Fin.addCases_right]

/-- Docking a heads-`0` run at an injective slot map of a heads-`0` bank. -/
theorem dock0 {t u s n : Nat} {p : Machine t s} {tin tout : Fin t → List Bool}
    (h : Step p n (fun _=>0) tin (fun _=>0) tout) (slots : Fin t → Fin u) (hi : Function.Injective slots)
    (A : Fin u → List Bool) (hA : ∀ j,A (slots j)=tin j) :
    Step (RecoveryFocus.machine slots p) n (fun _=>0) A (fun _=>0) (install slots A tout) :=
  (h.dock slots hi _ A (fun _=>rfl) hA).congr (dockH_existing _ _ _ (fun _=>rfl)) rfl

/-! ## 4. The 73-port live-word phase -/

/-- Local entry bank: the framed request on port 0, everything else blank. -/
def liveIn (w : List Bool) : Fin 73 → List Bool := fun i=>if i=0 then frame w else []

def ls1 : Fin (2+13+1) → Fin 73 := fun i=>⟨i.val,by omega⟩
def ls2 : Fin (2+13+1) → Fin 73 := fun i=>if i.val=0 then 0 else ⟨i.val+15,by omega⟩
def ls3 : Fin (2+29+1) → Fin 73 := fun i=>if i.val=0 then 0 else ⟨i.val+30,by omega⟩
def ld1 : Fin 3 → Fin 73 := ![1,62,63]
def lpl : Fin (2+1) → Fin 73 := ![1,64,65]
def ld2 : Fin 3 → Fin 73 := ![64,66,67]
def ld3 : Fin 3 → Fin 73 := ![16,68,69]
def lw : Fin 4 → Fin 73 := ![31,70,71,72]
def lb : Fin 1 → Fin 73 := ![71]

theorem ls1_inj : Function.Injective ls1 := by decide
theorem ls2_inj : Function.Injective ls2 := by decide
theorem ls3_inj : Function.Injective ls3 := by decide
theorem ld1_inj : Function.Injective ld1 := by decide
theorem lpl_inj : Function.Injective lpl := by decide
theorem ld2_inj : Function.Injective ld2 := by decide
theorem ld3_inj : Function.Injective ld3 := by decide
theorem lw_inj : Function.Injective lw := by decide
theorem lb_inj : Function.Injective lb := by decide

def liveChain (a : DecompositionAlgorithm) :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (RecoveryFocus.machine ls1 (MaskedReset.machine (complStage a).machine (fun _=>true)))
    (RecoveryFocus.machine ls2 (MaskedReset.machine (liveStage a).machine (fun _=>true))))
    (RecoveryFocus.machine ls3 (MaskedReset.machine (twoKStage a).machine (fun _=>true))))
    (RecoveryFocus.machine ld1 (RepairSource.ProjectionNormalization.DimensionTemplate.machine false)))
    (RecoveryFocus.machine lpl (MaskedReset.machine (NearCubicWires.PacketsGlue.RequestMeta.CopyPlus.machine 1)
      (fun _=>true))))
    (RecoveryFocus.machine ld2 (RepairSource.ProjectionNormalization.DimensionTemplate.machine true)))
    (RecoveryFocus.machine ld3 (RepairSource.ProjectionNormalization.DimensionTemplate.machine true)))
    (RecoveryFocus.machine lw RepairSource.ProjectionNormalization.Counter.machine))
    (RecoveryFocus.machine lb bump)

def liveCost (a : DecompositionAlgorithm) (r : Request) : Nat :=
  ((((((((2*(complStage a).cost r+2)+1+(2*(liveStage a).cost r+2))+1+(2*(twoKStage a).cost r+2))+1+
    (2*complCount a r+8))+1+(2*(complCount a r+1+1)+2))+1+(2*(complCount a r+1)+8))+1+
    (2*liveCount a r+8))+1+RepairSource.ProjectionNormalization.Counter.budget (twoK a r))+1+1

/-- The exit heads: all `0` except the family-size word's sentinel head `1` (port 71). -/
def liveH : Fin 73 → Nat := fun i=>if i=71 then 1 else 0

theorem stage_input (e : Nat) (w : List Bool) (sl : Fin (2+e+1) → Fin 73)
    (h0 : sl ⟨0,by omega⟩=0) (_hne : ∀ j,j.val≠0 → sl j≠0) (A : Fin 73 → List Bool)
    (a0 : A 0=frame w) (ab : ∀ j,j.val≠0 → A (sl j)=[]) :
    ∀ j,A (sl j)=Fin.addCases (m:=2+e) (n:=1) (motive:=fun _=>List Bool) (inBank (2+e) w) (fun _=>[]) j := by
  intro j
  by_cases hj : j.val=0
  · obtain ⟨jv,hjv⟩ := j
    simp only at hj
    subst hj
    rw [h0,a0]
    have e1 : (⟨0,by omega⟩ : Fin (2+e+1))=Fin.castAdd 1 (⟨0,by omega⟩ : Fin (2+e)) := rfl
    rw [e1,Fin.addCases_left]
    simp [inBank]
  · rw [ab j hj,inBank_blank e w j hj]

theorem vec2_zero : (![0,0] : Fin 2 → Nat)=fun _=>0 := by
  funext i
  fin_cases i <;> rfl

theorem live_chain (a : DecompositionAlgorithm) (r : Request) :
    ∃ A : Fin 73 → List Bool,Step (liveChain a) (liveCost a r) (fun _=>0) (liveIn (Request.input a r)) liveH A ∧
      A 0=frame (Request.input a r) ∧ A 62=UnaryTemplate.tape (complCount a r) ∧
      A 66=UnaryTemplate.tape (complCount a r+2) ∧ A 68=UnaryTemplate.tape (liveCount a r+1) ∧
      A 71=RepairSource.VerifierDecoding.CompareMachine.word (twoK a r) := by
  classical
  set w := Request.input a r with hw
  set A0 := liveIn w with hA0
  have blank0 : ∀ x : Fin 73,x≠0 → A0 x=[] := fun x hx=>by simp [hA0,liveIn,hx]
  -- stage 1: n
  obtain ⟨B1,r1,b10,b11⟩ := stage_masked (complStage a) r
  have d1 := dock0 r1 ls1 ls1_inj A0 (stage_input 13 w ls1 rfl (by decide) A0 (by simp [hA0,liveIn])
    (fun j hj=>blank0 _ (by
      intro he
      apply hj
      have := congrArg Fin.val he
      simpa [ls1] using this)))
  set A1 := install ls1 A0 B1 with hA1
  have o1 : ∀ x : Fin 73,16 ≤ x.val → A1 x=[] := by
    intro x hx
    have hs : ∀ j,ls1 j≠x := by
      intro j he
      have := congrArg Fin.val he
      simp [ls1] at this
      omega
    rw [hA1,install_other _ _ _ _ hs]
    exact blank0 x (fun he=>by rw [he] at hx; exact absurd hx (by decide))
  have a1_0 : A1 0=frame w := by
    show install ls1 A0 B1 (ls1 ⟨0,by omega⟩)=_
    rw [install_slot _ ls1_inj]
    exact b10
  have a1_1 : A1 1=List.replicate (complCount a r) true := by
    show install ls1 A0 B1 (ls1 ⟨1,by omega⟩)=_
    rw [install_slot _ ls1_inj]
    exact b11
  -- stage 2: K
  obtain ⟨B2,r2,b20,b21⟩ := stage_masked (liveStage a) r
  have d2 := dock0 r2 ls2 ls2_inj A1 (stage_input 13 w ls2 rfl (by decide) A1 a1_0
    (fun j hj=>o1 _ (by simp [ls2,hj]; omega)))
  set A2 := install ls2 A1 B2 with hA2
  have s2v : ∀ j,(ls2 j).val=0 ∨ (15 ≤ (ls2 j).val ∧ (ls2 j).val ≤ 30) := by decide
  have o2 : ∀ x : Fin 73,x≠0 → (x.val<16 ∨ 30<x.val) → A2 x=A1 x := by
    intro x hx0 hx
    refine install_other _ _ _ _ (fun j he=>?_)
    rcases s2v j with h|h
    · exact hx0 (by rw [←he]; exact Fin.ext h)
    · rw [he] at h
      have : 16 ≤ x.val := by
        by_contra hc
        have hj : j.val=0 := by
          have := congrArg Fin.val he
          simp only [ls2] at this
          split_ifs at this with hj0
          · exact hj0
          · simp at this; omega
        rw [show ls2 j=0 by simp [ls2,hj]] at he
        exact hx0 he.symm
      omega
  have a2_0 : A2 0=frame w := by
    show install ls2 A1 B2 (ls2 ⟨0,by omega⟩)=_
    rw [install_slot _ ls2_inj]
    exact b20
  have a2_16 : A2 16=List.replicate (liveCount a r) true := by
    show install ls2 A1 B2 (ls2 ⟨1,by omega⟩)=_
    rw [install_slot _ ls2_inj]
    exact b21
  have a2_1 : A2 1=List.replicate (complCount a r) true := by
    rw [o2 1 (by decide) (Or.inl (by decide)),a1_1]
  have o2b : ∀ x : Fin 73,31 ≤ x.val → A2 x=[] := by
    intro x hx
    rw [o2 x (fun he=>by rw [he] at hx; exact absurd hx (by decide)) (Or.inr (by omega))]
    exact o1 x (by omega)
  -- stage 3: 2^K
  obtain ⟨B3,r3,b30,b31⟩ := stage_masked (twoKStage a) r
  have d3 := dock0 r3 ls3 ls3_inj A2 (stage_input 29 w ls3 rfl (by decide) A2 a2_0
    (fun j hj=>o2b _ (by simp [ls3,hj]; omega)))
  set A3 := install ls3 A2 B3 with hA3
  have s3v : ∀ j,(ls3 j).val=0 ∨ (30 ≤ (ls3 j).val ∧ (ls3 j).val ≤ 61) := by decide
  have o3 : ∀ x : Fin 73,x≠0 → (x.val<31 ∨ 61<x.val) → A3 x=A2 x := by
    intro x hx0 hx
    refine install_other _ _ _ _ (fun j he=>?_)
    rcases s3v j with h|h
    · exact hx0 (by rw [←he]; exact Fin.ext h)
    · rw [he] at h
      have : 31 ≤ x.val := by
        by_contra hc
        have hj : j.val=0 := by
          have := congrArg Fin.val he
          simp only [ls3] at this
          split_ifs at this with hj0
          · exact hj0
          · simp at this; omega
        rw [show ls3 j=0 by simp [ls3,hj]] at he
        exact hx0 he.symm
      omega
  have a3_0 : A3 0=frame w := by
    show install ls3 A2 B3 (ls3 ⟨0,by omega⟩)=_
    rw [install_slot _ ls3_inj]
    exact b30
  have a3_31 : A3 31=List.replicate (twoK a r) true := by
    show install ls3 A2 B3 (ls3 ⟨1,by omega⟩)=_
    rw [install_slot _ ls3_inj]
    exact b31
  have a3_1 : A3 1=List.replicate (complCount a r) true := by
    rw [o3 1 (by decide) (Or.inl (by decide)),a2_1]
  have a3_16 : A3 16=List.replicate (liveCount a r) true := by
    rw [o3 16 (by decide) (Or.inl (by decide)),a2_16]
  have o3b : ∀ x : Fin 73,62 ≤ x.val → A3 x=[] := by
    intro x hx
    rw [o3 x (fun he=>by rw [he] at hx; exact absurd hx (by decide)) (Or.inr (by omega))]
    exact o2b x (by omega)
  -- stage D1: tape n
  have rD1 := RepairSource.CloseoutFinal.C10CompareDockLit.step_of_clock (RepairSource.ProjectionNormalization.DimensionTemplate.ready false (complCount a r))
  have dD1 := dock0 rD1 ld1 ld1_inj A3 (by
    intro j
    fin_cases j
    · exact a3_1
    · exact o3b 62 (by decide)
    · exact o3b 63 (by decide))
  set A4 := install ld1 A3 (RepairSource.ProjectionNormalization.DimensionTemplate.output false (complCount a r)) with hA4
  have o4 : ∀ x : Fin 73,x≠1 → x≠62 → x≠63 → A4 x=A3 x := by
    intro x h1 h2 h3
    refine install_other _ _ _ _ (fun j he=>?_)
    fin_cases j
    · exact h1 he.symm
    · exact h2 he.symm
    · exact h3 he.symm
  have a4_62 : A4 62=UnaryTemplate.tape (complCount a r) := by
    show install ld1 A3 _ (ld1 1)=_
    rw [install_slot _ ld1_inj]
    rfl
  have a4_1 : A4 1=List.replicate (complCount a r) true := by
    show install ld1 A3 _ (ld1 0)=_
    rw [install_slot _ ld1_inj]
    rfl
  -- stage P: 1^(n+1)
  obtain ⟨kP,-,mP⟩ := mask_empty (NearCubicWires.PacketsGlue.RequestMeta.CopyPlus.run 1 (complCount a r))
    (fun _=>true) (fun i _=>by fin_cases i <;> rfl)
  rw [vec2_zero] at mP
  have rP := (mP.congr_in (zeros_addCases _ _) rfl).congr (zeros_masked _) rfl
  have dP := dock0 rP lpl lpl_inj A4 (by
    intro j
    fin_cases j
    · exact a4_1
    · show A4 64=_
      rw [o4 64 (by decide) (by decide) (by decide),o3b 64 (by decide)]
      rfl
    · show A4 65=_
      rw [o4 65 (by decide) (by decide) (by decide),o3b 65 (by decide)]
      rfl)
  set A5 := install lpl A4 (Fin.addCases (m:=2) (n:=1) (motive:=fun _=>List Bool)
    ![List.replicate (complCount a r) true,List.replicate (complCount a r+1) true]
    (fun _=>List.replicate kP false)) with hA5
  have o5 : ∀ x : Fin 73,x≠1 → x≠64 → x≠65 → A5 x=A4 x := by
    intro x h1 h2 h3
    refine install_other _ _ _ _ (fun j he=>?_)
    fin_cases j
    · exact h1 he.symm
    · exact h2 he.symm
    · exact h3 he.symm
  have a5_64 : A5 64=List.replicate (complCount a r+1) true := by
    show install lpl A4 _ (lpl 1)=_
    rw [install_slot _ lpl_inj]
    rfl
  -- stage D2: tape (n+2)
  have rD2 := RepairSource.CloseoutFinal.C10CompareDockLit.step_of_clock (RepairSource.ProjectionNormalization.DimensionTemplate.ready true (complCount a r+1))
  have dD2 := dock0 rD2 ld2 ld2_inj A5 (by
    intro j
    fin_cases j
    · exact a5_64
    · show A5 66=_
      rw [o5 66 (by decide) (by decide) (by decide),o4 66 (by decide) (by decide) (by decide),o3b 66 (by decide)]
      rfl
    · show A5 67=_
      rw [o5 67 (by decide) (by decide) (by decide),o4 67 (by decide) (by decide) (by decide),o3b 67 (by decide)]
      rfl)
  set A6 := install ld2 A5 (RepairSource.ProjectionNormalization.DimensionTemplate.output true (complCount a r+1)) with hA6
  have o6 : ∀ x : Fin 73,x≠64 → x≠66 → x≠67 → A6 x=A5 x := by
    intro x h1 h2 h3
    refine install_other _ _ _ _ (fun j he=>?_)
    fin_cases j
    · exact h1 he.symm
    · exact h2 he.symm
    · exact h3 he.symm
  have a6_66 : A6 66=UnaryTemplate.tape (complCount a r+2) := by
    show install ld2 A5 _ (ld2 1)=_
    rw [install_slot _ ld2_inj]
    rfl
  -- stage D3: tape (K+1)
  have rD3 := RepairSource.CloseoutFinal.C10CompareDockLit.step_of_clock (RepairSource.ProjectionNormalization.DimensionTemplate.ready true (liveCount a r))
  have up16 : A6 16=List.replicate (liveCount a r) true := by
    rw [o6 16 (by decide) (by decide) (by decide),o5 16 (by decide) (by decide) (by decide),
      o4 16 (by decide) (by decide) (by decide),a3_16]
  have dD3 := dock0 rD3 ld3 ld3_inj A6 (by
    intro j
    fin_cases j
    · exact up16
    · show A6 68=_
      rw [o6 68 (by decide) (by decide) (by decide),o5 68 (by decide) (by decide) (by decide),
        o4 68 (by decide) (by decide) (by decide),o3b 68 (by decide)]
      rfl
    · show A6 69=_
      rw [o6 69 (by decide) (by decide) (by decide),o5 69 (by decide) (by decide) (by decide),
        o4 69 (by decide) (by decide) (by decide),o3b 69 (by decide)]
      rfl)
  set A7 := install ld3 A6 (RepairSource.ProjectionNormalization.DimensionTemplate.output true (liveCount a r)) with hA7
  have o7 : ∀ x : Fin 73,x≠16 → x≠68 → x≠69 → A7 x=A6 x := by
    intro x h1 h2 h3
    refine install_other _ _ _ _ (fun j he=>?_)
    fin_cases j
    · exact h1 he.symm
    · exact h2 he.symm
    · exact h3 he.symm
  have a7_68 : A7 68=UnaryTemplate.tape (liveCount a r+1) := by
    show install ld3 A6 _ (ld3 1)=_
    rw [install_slot _ ld3_inj]
    rfl
  -- stage W: word (2^K)
  obtain ⟨oW,rW,-,w2⟩ := liveCounter_run (twoK a r)
  have back : ∀ x : Fin 73,x≠1 → x≠16 → x≠62 → x≠63 → x≠64 → x≠65 → x≠66 → x≠67 → x≠68 → x≠69 →
      A7 x=A3 x := by
    intro x h1 h16 h62 h63 h64 h65 h66 h67 h68 h69
    rw [o7 x h16 h68 h69,o6 x h64 h66 h67,o5 x h1 h64 h65,o4 x h1 h62 h63]
  have dW := dock0 rW lw lw_inj A7 (by
    intro j
    fin_cases j
    · show A7 31=_
      rw [back 31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide),a3_31]
      rfl
    · show A7 70=_
      rw [back 70 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide),o3b 70 (by decide)]
      rfl
    · show A7 71=_
      rw [back 71 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide),o3b 71 (by decide)]
      rfl
    · show A7 72=_
      rw [back 72 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide),o3b 72 (by decide)]
      rfl)
  set A8 := install lw A7 oW with hA8
  have a8_71 : A8 71=RepairSource.VerifierDecoding.CompareMachine.word (twoK a r) := by
    show install lw A7 oW (lw 2)=_
    rw [install_slot _ lw_inj,w2]
  have o8 : ∀ x : Fin 73,x≠31 → x≠70 → x≠71 → x≠72 → A8 x=A7 x := by
    intro x h1 h2 h3 h4
    refine install_other _ _ _ _ (fun j he=>?_)
    fin_cases j
    · exact h1 he.symm
    · exact h2 he.symm
    · exact h3 he.symm
    · exact h4 he.symm
  -- stage B: the word's head to 1
  have dB := (bump_run 0 (RepairSource.VerifierDecoding.CompareMachine.word (twoK a r))).dock lb lb_inj
    (fun _=>0) A8 (fun _=>rfl) (fun j=>by fin_cases j; exact a8_71)
  have hB : dockH lb (fun _ : Fin 73=>(0:Nat)) (fun _=>0+1)=liveH := by
    funext x
    by_cases hx : x=71
    · subst hx
      exact dockH_slot _ lb_inj _ _ 0
    · rw [dockH_other _ _ _ _ (fun j he=>by fin_cases j; exact hx he.symm)]
      simp [liveH,hx]
  set A9 := install lb A8 (fun _=>RepairSource.VerifierDecoding.CompareMachine.word (twoK a r)) with hA9
  have o9 : ∀ x : Fin 73,x≠71 → A9 x=A8 x := by
    intro x hx
    exact install_other _ _ _ _ (fun j he=>by fin_cases j; exact hx he.symm)
  refine ⟨A9,((((((((d1.seq d2).seq d3).seq dD1).seq dP).seq dD2).seq dD3).seq dW).seq (dB.congr hB rfl)),
    ?_,?_,?_,?_,?_⟩
  · rw [o9 0 (by decide),o8 0 (by decide) (by decide) (by decide) (by decide),
      back 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide),a3_0]
  · rw [o9 62 (by decide),o8 62 (by decide) (by decide) (by decide) (by decide),
      o7 62 (by decide) (by decide) (by decide),o6 62 (by decide) (by decide) (by decide),
      o5 62 (by decide) (by decide) (by decide),a4_62]
  · rw [o9 66 (by decide),o8 66 (by decide) (by decide) (by decide) (by decide),
      o7 66 (by decide) (by decide) (by decide),a6_66]
  · rw [o9 68 (by decide),o8 68 (by decide) (by decide) (by decide) (by decide),a7_68]
  · show install lb A8 _ (lb 0)=_
    rw [install_slot _ lb_inj]

end
end RowsInit
