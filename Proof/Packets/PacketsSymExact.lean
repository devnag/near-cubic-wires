import Proof.Packets.PacketsMetaStream

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.PacketsSymBits
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.PacketsMeta
noncomputable section

theorem lr_src {t s W : ℕ} {P : Machine t s} {n : ℕ} {σ σ' τ : Fin t → TS} (h : LRuns W P n σ τ)
    (e : σ = σ') : LRuns W P n σ' τ := e ▸ h

theorem write_end (l : List Bool) (b : Bool) : writeTapeBit l l.length b = l ++ [b] := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [writeTapeBit, ih]

theorem sf_snoc (w : List Bool) (x : Bool) (j : ℕ) :
    sf (w ++ [x]) j = if j = w.length + 1 then x else sf w j := by
  cases j with
  | zero => simp [sf_zero]
  | succ j =>
    rw [sf_succ, sf_succ]
    by_cases h1 : j < w.length
    · rw [List.getD_append _ _ _ _ h1, if_neg (by omega)]
    · by_cases h2 : j = w.length
      · subst h2
        rw [if_pos rfl, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
        rfl
      · rw [if_neg (by omega), List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by omega)]

/-! ## The exact copy -/

namespace ExactCopy

/-- Tapes: 0 stream, 1 marks, 2 output. While the marks read `true`: output := stream bit, all heads right. -/
def machine : Machine 3 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q b => if q.val = 0 then
      (if b 1 then some ⟨0, ![none, none, some (b 0)], fun _ => .right⟩
       else some ⟨1, fun _ => none, fun _ => .stay⟩)
    else none

def cfg (q : Fin 2) (h ho : ℕ) (S M O : List Bool) : Configuration 3 2 := ⟨q, ![h, h, ho], ![S, M, O]⟩

theorem sT (S M O : List Bool) (h ho : ℕ) (hm : readTapeBit M h = true) :
    LocalBitMultitape.step machine (cfg 0 h ho S M O) =
      some (cfg 0 (h + 1) (ho + 1) S M (writeTapeBit O ho (readTapeBit S h))) := by
  simp [LocalBitMultitape.step, machine, cfg, Configuration.scanned, hm]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem sF (S M O : List Bool) (h ho : ℕ) (hm : readTapeBit M h = false) :
    LocalBitMultitape.step machine (cfg 0 h ho S M O) = some (cfg 1 h ho S M O) := by
  simp [LocalBitMultitape.step, machine, cfg, Configuration.scanned, hm]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem loop (S M o w : List Bool) (hS : ∀ j, readTapeBit S j = sf w j)
    (hM : ∀ j, readTapeBit M j = sf (List.replicate w.length true) j) :
    ∀ i, i ≤ w.length →
      Timed machine i (cfg 0 1 o.length S M o) (cfg 0 (1 + i) (o.length + i) S M (o ++ w.take i)) := by
  intro i
  induction i with
  | zero =>
    intro _
    simpa using Timed.refl machine (cfg 0 1 o.length S M o)
  | succ i ih =>
    intro hi
    have t := ih (by omega)
    have hm : readTapeBit M (1 + i) = true := by
      rw [hM]; exact sf_marks_true _ _ (by omega) (by omega)
    have hs : readTapeBit S (1 + i) = w[i]'(by omega) := by
      rw [hS, show 1 + i = i + 1 by omega, sf_succ, List.getD_eq_getElem]
    have a := Timed.single (by rfl) (sT S M (o ++ w.take i) (1 + i) (o.length + i) hm)
    have hl : (o ++ w.take i).length = o.length + i := by simp; omega
    have e : writeTapeBit (o ++ w.take i) (o.length + i) (readTapeBit S (1 + i)) = o ++ w.take (i + 1) := by
      rw [← hl, write_end, hs, List.take_succ_eq_append_getElem (by omega), List.append_assoc]
    rw [e] at a
    have tt := t.trans a
    rwa [show 1 + i + 1 = 1 + (i + 1) by omega, show o.length + i + 1 = o.length + (i + 1) by omega] at tt

/-- **The exact copy.** -/
theorem run (S M o w : List Bool) (hS : ∀ j, readTapeBit S j = sf w j)
    (hM : ∀ j, readTapeBit M j = sf (List.replicate w.length true) j) :
    Step machine (w.length + 1) ![1, 1, o.length] ![S, M, o]
      ![1 + w.length, 1 + w.length, o.length + w.length] ![S, M, o ++ w] := by
  have t := loop S M o w hS hM w.length le_rfl
  rw [List.take_length] at t
  have hend : readTapeBit M (1 + w.length) = false := by
    rw [hM, show 1 + w.length = w.length + 1 by omega]; exact sf_marks_end _
  have a := Timed.single (by rfl) (sF S M (o ++ w) (1 + w.length) (o.length + w.length) hend)
  have tt := t.trans a
  obtain ⟨r, hr, hf, _⟩ := tt.run (by rfl)
  exact Step.of_run (hin := ![1, 1, o.length]) (tin := ![S, M, o])
    (hout := ![1 + w.length, 1 + w.length, o.length + w.length]) (tout := ![S, M, o ++ w]) hr
    (by rw [hf]; rfl) (by rw [hf]; rfl)

end ExactCopy

/-! ## A unary word into a stream -/

namespace UCopy

/-- Tapes: 0 the unary source `1^j`, 1 the new stream. Write the blank cell `0`, copy the source's marks from cell
`1` on, add one more mark, then walk back to cursor `1`. -/
def machine : Machine 2 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 3
  rule := fun q b =>
    if q.val = 0 then some ⟨1, ![none, some false], ![.stay, .right]⟩
    else if q.val = 1 then
      (if b 0 then some ⟨1, ![none, some true], ![.right, .right]⟩
       else some ⟨2, ![none, some true], ![.stay, .stay]⟩)
    else if q.val = 2 then
      (if b 1 then some ⟨2, fun _ => none, ![.stay, .left]⟩
       else some ⟨3, fun _ => none, ![.stay, .right]⟩)
    else none

def cfg (q : Fin 4) (hx hy : ℕ) (X Y : List Bool) : Configuration 2 4 := ⟨q, ![hx, hy], ![X, Y]⟩

theorem s0 (X Y : List Bool) :
    LocalBitMultitape.step machine (cfg 0 0 0 X Y) = some (cfg 1 0 1 X (writeTapeBit Y 0 false)) := by
  simp [LocalBitMultitape.step, machine, cfg, Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem s1t (X Y : List Bool) (hx hy : ℕ) (h : readTapeBit X hx = true) :
    LocalBitMultitape.step machine (cfg 1 hx hy X Y) =
      some (cfg 1 (hx + 1) (hy + 1) X (writeTapeBit Y hy true)) := by
  simp [LocalBitMultitape.step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem s1f (X Y : List Bool) (hx hy : ℕ) (h : readTapeBit X hx = false) :
    LocalBitMultitape.step machine (cfg 1 hx hy X Y) = some (cfg 2 hx hy X (writeTapeBit Y hy true)) := by
  simp [LocalBitMultitape.step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem s2t (X Y : List Bool) (hx hy : ℕ) (h : readTapeBit Y hy = true) :
    LocalBitMultitape.step machine (cfg 2 hx hy X Y) = some (cfg 2 hx (hy - 1) X Y) := by
  simp [LocalBitMultitape.step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem s2f (X Y : List Bool) (hx hy : ℕ) (h : readTapeBit Y hy = false) :
    LocalBitMultitape.step machine (cfg 2 hx hy X Y) = some (cfg 3 hx (hy + 1) X Y) := by
  simp [LocalBitMultitape.step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem copyLoop (j : ℕ) : ∀ i, i ≤ j →
    Timed machine i (cfg 1 0 1 (List.replicate j true) [false])
      (cfg 1 i (1 + i) (List.replicate j true) (false :: List.replicate i true)) := by
  intro i
  induction i with
  | zero => intro _; simpa using Timed.refl machine (cfg 1 0 1 (List.replicate j true) [false])
  | succ i ih =>
    intro hi
    have t := ih (by omega)
    have hx : readTapeBit (List.replicate j true) i = true := by
      simp [readTapeBit, List.getD_eq_getElem, List.getElem_replicate, show i < j by omega]
    have a := Timed.single (by rfl) (s1t (List.replicate j true) (false :: List.replicate i true) i (1 + i) hx)
    have e : writeTapeBit (false :: List.replicate i true) (1 + i) true = false :: List.replicate (i + 1) true := by
      have hl : (false :: List.replicate i true).length = 1 + i := by simp; omega
      rw [← hl, write_end, List.replicate_succ']
      rfl
    rw [e] at a
    have tt := t.trans a
    rwa [show 1 + i + 1 = 1 + (i + 1) by omega] at tt

theorem backLoop (X : List Bool) (hx n : ℕ) : ∀ m, m ≤ n + 1 →
    Timed machine m (cfg 2 hx (n + 1) X (false :: List.replicate (n + 1) true))
      (cfg 2 hx (n + 1 - m) X (false :: List.replicate (n + 1) true)) := by
  intro m
  induction m with
  | zero => intro _; simpa using Timed.refl machine (cfg 2 hx (n + 1) X (false :: List.replicate (n + 1) true))
  | succ m ih =>
    intro hm
    have t := ih (by omega)
    have hy : readTapeBit (false :: List.replicate (n + 1) true) (n + 1 - m) = true := by
      rw [show n + 1 - m = (n - m) + 1 by omega]
      simp [readTapeBit, List.getD_eq_getElem, List.getElem_replicate, show n - m < n + 1 by omega]
    have a := Timed.single (by rfl) (s2t X (false :: List.replicate (n + 1) true) hx (n + 1 - m) hy)
    have tt := t.trans a
    rwa [show n + 1 - m - 1 = n + 1 - (m + 1) by omega] at tt

/-- **The unary copy.** -/
theorem run (j : ℕ) :
    Step machine (2 * j + 4) ![0, 0] ![List.replicate j true, []]
      ![j, 1] ![List.replicate j true, false :: List.replicate (j + 1) true] := by
  have a0 := Timed.single (by rfl) (s0 (List.replicate j true) [])
  have e0 : writeTapeBit ([] : List Bool) 0 false = [false] := rfl
  rw [e0] at a0
  have t1 := copyLoop j j le_rfl
  have hx : readTapeBit (List.replicate j true) j = false := by simp [readTapeBit]
  have a1 := Timed.single (by rfl) (s1f (List.replicate j true) (false :: List.replicate j true) j (1 + j) hx)
  have e1 : writeTapeBit (false :: List.replicate j true) (1 + j) true = false :: List.replicate (j + 1) true := by
    have hl : (false :: List.replicate j true).length = 1 + j := by simp; omega
    rw [← hl, write_end, List.replicate_succ']
    rfl
  rw [e1] at a1
  rw [show 1 + j = j + 1 by omega] at t1 a1
  have t2 := backLoop (List.replicate j true) j j (j + 1) le_rfl
  rw [Nat.sub_self] at t2
  have hy : readTapeBit (false :: List.replicate (j + 1) true) 0 = false := rfl
  have a2 := Timed.single (by rfl) (s2f (List.replicate j true) (false :: List.replicate (j + 1) true) j 0 hy)
  have tt := (((a0.trans t1).trans a1).trans t2).trans a2
  obtain ⟨r, hr, hf, hs⟩ := tt.run (by rfl)
  have hs' : Step machine (1 + j + 1 + (j + 1) + 1) ![0, 0] ![List.replicate j true, []]
      ![j, 1] ![List.replicate j true, false :: List.replicate (j + 1) true] :=
    Step.of_run (hin := ![0, 0]) (tin := ![List.replicate j true, []]) hr (by rw [hf]; rfl) (by rw [hf]; rfl)
  exact hs'.enlarge (by omega)

end UCopy

/-! ## Streams with marks, cursor at the end -/

/-- A stream holding `w`, cursor just past it. -/
abbrev sS (w : List Bool) : TS := .cells (sf w) (w.length + 1)
/-- Its marks. -/
abbrev sM (w : List Bool) : TS := .cells (sf (List.replicate w.length true)) (w.length + 1)

/-- Append the bit `x` to a stream (tape 0) and its marks (tape 1). -/
def sapp (x : Bool) : Machine 2 2 :=
  oneStep 2 (fun _ => (![some x, some true], fun _ => .right))

theorem sapp_lruns (W : ℕ) (x : Bool) (w : List Bool) :
    LRuns W (sapp x) 1 ![sS w, sM w] ![sS (w ++ [x]), sM (w ++ [x])] := by
  intro H A hA
  have h0 : H 0 = w.length + 1 ∧ ∀ j, readTapeBit (A 0) j = sf w j := hA 0
  have h1 : H 1 = w.length + 1 ∧ ∀ j, readTapeBit (A 1) j = sf (List.replicate w.length true) j := hA 1
  refine ⟨_, _, oneStep_run 2 _ H A, ?_⟩
  intro i
  fin_cases i
  · refine ⟨by simp [HeadMove.apply, h0.1], fun j => ?_⟩
    simp only [acted]
    simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [read_write, h0.1, h0.2, sf_snoc]
  · refine ⟨by simp [HeadMove.apply, h1.1], fun j => ?_⟩
    simp only [acted]
    simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [read_write, h1.1, h1.2, List.length_append, List.length_singleton, List.replicate_succ', sf_snoc,
      List.length_replicate]

/-! ## `V` copies of a bit -/

namespace EmitBits

end EmitBits

/-! ## The branch at the Step level -/

section Branch
variable {t : ℕ}

/-- `Ite C P Q flag` when the flag reads `true` after `C`. -/
theorem iteT {a b c : ℕ} (C : Machine t a) (P : Machine t b) (Q : Machine t c) (flag : Fin t)
    {nc np : ℕ} (nq : ℕ) {H H1 H2 : Fin t → ℕ} {A A1 A2 : Fin t → List Bool}
    (hc : Step C nc H A H1 A1) (hf : readTapeBit (A1 flag) (H1 flag) = true) (hp : Step P np H1 A1 H2 A2) :
    Step (Ite C P Q flag) (nc + np + nq + 2) H A H2 A2 := by
  obtain ⟨r1, hr1, hh1, ht1, hs1⟩ := hc
  obtain ⟨r2, hr2, hh2, ht2, hs2⟩ := hp
  have hscan : r1.final.scanned flag = true := by
    unfold Configuration.scanned
    rw [hh1, ht1]
    exact hf
  obtain ⟨n1, hn1, t1⟩ := call_receipt (iteSizes a b c) (itePrograms C P Q) 0 (iteNext flag) 0 1 nc _ r1 hr1
    (iteNext_true flag _ _ hscan)
  have hr2' : runFrom (itePrograms C P Q 1) np
      (RecoveryCalls.restarted (itePrograms C P Q 1) r1.final.heads r1.final.tapes) = some r2 := by
    rw [hh1, ht1]; exact hr2
  obtain ⟨n2, hn2, t2⟩ := stop_receipt (iteSizes a b c) (itePrograms C P Q) 0 (iteNext flag) 1 np _ r2 hr2'
    (iteNext_one flag _ _)
  have tt := t1.trans t2
  have e : RecoveryCalls.stopped (iteSizes a b c) r2.final.heads r2.final.tapes =
      ⟨RecoveryCalls.controlCode (iteSizes a b c) none, H2, A2⟩ := by
    rw [hh2, ht2]; rfl
  rw [e] at tt
  exact step_of_timed tt rfl (by simp [Ite, RecoveryCalls.machine]) (by omega)

/-- `Ite C P Q flag` when the flag reads `false` after `C`. -/
theorem iteF {a b c : ℕ} (C : Machine t a) (P : Machine t b) (Q : Machine t c) (flag : Fin t)
    {nc nq : ℕ} (np : ℕ) {H H1 H2 : Fin t → ℕ} {A A1 A2 : Fin t → List Bool}
    (hc : Step C nc H A H1 A1) (hf : readTapeBit (A1 flag) (H1 flag) = false) (hq : Step Q nq H1 A1 H2 A2) :
    Step (Ite C P Q flag) (nc + np + nq + 2) H A H2 A2 := by
  obtain ⟨r1, hr1, hh1, ht1, hs1⟩ := hc
  obtain ⟨r2, hr2, hh2, ht2, hs2⟩ := hq
  have hscan : r1.final.scanned flag = false := by
    unfold Configuration.scanned
    rw [hh1, ht1]
    exact hf
  obtain ⟨n1, hn1, t1⟩ := call_receipt (iteSizes a b c) (itePrograms C P Q) 0 (iteNext flag) 0 2 nc _ r1 hr1
    (iteNext_false flag _ _ hscan)
  have hr2' : runFrom (itePrograms C P Q 2) nq
      (RecoveryCalls.restarted (itePrograms C P Q 2) r1.final.heads r1.final.tapes) = some r2 := by
    rw [hh1, ht1]; exact hr2
  obtain ⟨n2, hn2, t2⟩ := stop_receipt (iteSizes a b c) (itePrograms C P Q) 0 (iteNext flag) 2 nq _ r2 hr2'
    (iteNext_two flag _ _)
  have tt := t1.trans t2
  have e : RecoveryCalls.stopped (iteSizes a b c) r2.final.heads r2.final.tapes =
      ⟨RecoveryCalls.controlCode (iteSizes a b c) none, H2, A2⟩ := by
    rw [hh2, ht2]; rfl
  rw [e] at tt
  exact step_of_timed tt rfl (by simp [Ite, RecoveryCalls.machine]) (by omega)

end Branch

end
end NearCubicWires.PacketsSymBits

