import Proof.Packets.PacketsSymBitsTail

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.PacketsSymBits.Prog
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.RepairRepresentation
open NearCubicWires.PacketsMeta NearCubicWires.PacketsSymBits NearCubicWires.PacketsSymBits.Win
open NearCubicWires.PacketsKeys
noncomputable section

/-! ## The extra tapes -/

/-- The roles of the 20 extra tapes. -/
structure XS where
  o : List Bool
  T : ℕ → TS
  Tm : ℕ → TS
  off : ℕ → TS
  len : ℕ → TS
  f1 : Bool
  f2 : Bool

def xr (x : XS) : Fin 20 → TS := fun i =>
  if i.val = 0 then sS x.o else if i.val = 1 then sM x.o
  else if i.val < 6 then x.T (i.val - 2) else if i.val < 10 then x.Tm (i.val - 6)
  else if i.val < 14 then x.off (i.val - 10) else if i.val < 18 then x.len (i.val - 14)
  else if i.val = 18 then .flag x.f1 else .flag x.f2

/-- The whole role map. -/
def R (w : List Bool) (s : Native.NS) (x : XS) : Fin (26 + 20) → TS := Fin.addCases (Native.nv w s) (xr x)

/-- An extra tape. -/
def ex (k : ℕ) (hk : k < 20) : Fin (26 + 20) := Fin.natAdd 26 ⟨k, hk⟩

/-- The window tail's slots for circuit `c`. -/
def tailSlots (c : Fin 4) : Fin 9 → Fin (26 + 20) :=
  ![Fin.castAdd 20 (Native.sS c), ex (2 + c.val) (by omega), ex (6 + c.val) (by omega), ex (10 + c.val) (by omega),
    ex (14 + c.val) (by omega), ex 0 (by omega), ex 1 (by omega), ex 18 (by omega), ex 19 (by omega)]

theorem tailSlots_inj (c : Fin 4) : Function.Injective (tailSlots c) := by
  fin_cases c <;> decide

theorem R_ex (w : List Bool) (s : Native.NS) (x : XS) (k : ℕ) (hk : k < 20) : R w s x (ex k hk) = xr x ⟨k, hk⟩ := by
  unfold R ex; rw [Fin.addCases_right]

theorem R_castAdd (w : List Bool) (s : Native.NS) (x : XS) (i : Fin 26) :
    R w s x (Fin.castAdd 20 i) = Native.nv w s i := by
  simp only [R, Fin.addCases_left]

theorem R_S (w : List Bool) (s : Native.NS) (x : XS) (c : Fin 4) :
    R w s x (Fin.castAdd 20 (Native.sS c)) = s.ct (Native.cS c) := by
  simp only [R, Fin.addCases_left]; exact Native.nv_S w s c

/-- The extras after circuit `c`'s window tail. -/
def postX (x : XS) (c : ℕ) (top : List Bool) (off P : ℕ) : XS :=
  ⟨x.o ++ win top off P, Function.update x.T c (.cells (sf top) (1 + off + P)),
    Function.update x.Tm c (.cells (sf (List.replicate top.length true)) 1),
    Function.update x.off c (uw off off), Function.update x.len c (uw P P), false, lastBit top off x.f2 P⟩

/-- The docked window tail on the whole layout. -/
def tailD (c : Fin 4) := RecoveryFocus.machine (tailSlots c) tailL

theorem tailD_run (W : ℕ) (c : Fin 4) (w : List Bool) (s : Native.NS) (x : XS) (fx : ℕ → Bool) (h : ℕ)
    (top : List Bool) (off P : ℕ) (hs : s.ct (Native.cS c) = .cells fx h)
    (hT : x.T c.val = .cells PacketsMeta.blank 0) (hTm : x.Tm c.val = .cells PacketsMeta.blank 0)
    (hoff : x.off c.val = uw off 0) (hlen : x.len c.val = uw P 0)
    (hX : ∀ i, i < (frame top).length → fx (h + i) = (frame top).getD i false) :
    LRuns W (tailD c) (tailCost top.length off P) (R w s x)
      (R w { s with ct := Function.update s.ct (Native.cS c) (.cells fx (h + (frame top).length)) }
        (postX x c.val top off P)) := by
  have hc := c.isLt
  refine (Win.tail_run W fx h top off P x.o x.f1 x.f2 hX).focus (tailSlots c) (tailSlots_inj c) _ _ ?_ ?_ ?_
  · intro j
    fin_cases j
    · exact (R_S w s x c).trans hs
    · show R w s x (ex (2 + c.val) _) = _
      rw [R_ex]; simp only [xr]; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      rw [show 2 + c.val - 2 = c.val by omega, hT]; rfl
    · show R w s x (ex (6 + c.val) _) = _
      rw [R_ex]; simp only [xr]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      rw [show 6 + c.val - 6 = c.val by omega, hTm]; rfl
    · show R w s x (ex (10 + c.val) _) = _
      rw [R_ex]; simp only [xr]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      rw [show 10 + c.val - 10 = c.val by omega, hoff]; rfl
    · show R w s x (ex (14 + c.val) _) = _
      rw [R_ex]; simp only [xr]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega)]
      rw [show 14 + c.val - 14 = c.val by omega, hlen]; rfl
    · show R w s x (ex 0 _) = _
      rw [R_ex]; rfl
    · show R w s x (ex 1 _) = _
      rw [R_ex]; rfl
    · show R w s x (ex 18 _) = _
      rw [R_ex]; rfl
    · show R w s x (ex 19 _) = _
      rw [R_ex]; rfl
  · intro j
    fin_cases j
    · show R w _ _ (Fin.castAdd 20 (Native.sS c)) = _
      rw [R_S]; simp
    · show R w _ _ (ex (2 + c.val) _) = _
      rw [R_ex]; simp only [xr]; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      rw [show 2 + c.val - 2 = c.val by omega]; simp [postX]
    · show R w _ _ (ex (6 + c.val) _) = _
      rw [R_ex]; simp only [xr]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      rw [show 6 + c.val - 6 = c.val by omega]; simp [postX]
    · show R w _ _ (ex (10 + c.val) _) = _
      rw [R_ex]; simp only [xr]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      rw [show 10 + c.val - 10 = c.val by omega]; simp [postX]
    · show R w _ _ (ex (14 + c.val) _) = _
      rw [R_ex]; simp only [xr]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega)]
      rw [show 14 + c.val - 14 = c.val by omega]; simp [postX]
    · show R w _ _ (ex 0 _) = _
      rw [R_ex]; rfl
    · show R w _ _ (ex 1 _) = _
      rw [R_ex]; rfl
    · show R w _ _ (ex 18 _) = _
      rw [R_ex]; rfl
    · show R w _ _ (ex 19 _) = _
      rw [R_ex]; rfl
  · intro i hi
    refine Fin.addCases (motive := fun i => (∀ j, tailSlots c j ≠ i) → R w _ _ i = R w s x i) (fun i0 hi0 => ?_)
      (fun k hk => ?_) i hi
    · simp only [R, Fin.addCases_left]
      rw [← Native.up_S]
      refine Function.update_of_ne (fun e => hi0 0 ?_) _ _
      show Fin.castAdd 20 (Native.sS c) = Fin.castAdd 20 i0
      rw [e]
    · simp only [R, Fin.addCases_right]
      have hne : ∀ (t : Fin 9) (kk : ℕ) (hkk : kk < 20), tailSlots c t = ex kk hkk → kk ≠ k.val := by
        intro t kk hkk ht hkv
        apply hk t
        rw [ht]
        exact Fin.ext (by simp [ex, hkv])
      have n0 := hne 5 0 (by omega) rfl
      have n1 := hne 6 1 (by omega) rfl
      have n2 := hne 1 (2 + c.val) (by omega) rfl
      have n3 := hne 2 (6 + c.val) (by omega) rfl
      have n4 := hne 3 (10 + c.val) (by omega) rfl
      have n5 := hne 4 (14 + c.val) (by omega) rfl
      have n6 := hne 7 18 (by omega) rfl
      have n7 := hne 8 19 (by omega) rfl
      have hk20 := k.isLt
      simp only [xr, postX]
      split_ifs <;> first | omega | rfl | (rw [Function.update_of_ne (by omega)])

/-! ## One block -/

/-- A 26-tape machine on the whole layout. -/
abbrev liftW {s : ℕ} (P : Machine 26 s) := RecoveryFocus.machine (Fin.castAdd 20) P

/-- **Block `c`**: peek; if a circuit frame starts, PK's body then the window tail. -/
def blockW (c : Fin 4) :=
  Ite (liftW (RecoveryFocus.machine ![(2 : Fin 26), 6] peek))
    (Composition.machine (liftW (Native.body c)) (tailD c)) (nop (26 + 20)) (Fin.castAdd 20 (6 : Fin 26))

def blockWCost (W m B P : ℕ) : ℕ := 1 + (Native.bodyCost W m + 1 + Win.tailCost m B P) + 0 + 2

/-- The extras after `c` blocks: the output so far; circuits `< c` spent (`.any`), the others untouched. -/
def xc (o : List Bool) (c : ℕ) (offs : ℕ → ℕ) (P : ℕ) (f1 f2 : Bool) : XS :=
  ⟨o, fun d => if d < c then .any else .cells PacketsMeta.blank 0,
    fun d => if d < c then .any else .cells PacketsMeta.blank 0,
    fun d => if d < c then .any else uw (offs d) 0, fun d => if d < c then .any else uw P 0, f1, f2⟩

/-- Circuit `d`'s window (empty past the circuits). -/
def winAt {α : Type} (L : List α) (tp : α → List Bool) (offs : ℕ → ℕ) (P d : ℕ) : List Bool :=
  if h : d < L.length then win (tp L[d]) (offs d) P else []

/-- The output after `c` blocks. -/
def outAt {α : Type} (L : List α) (tp : α → List Bool) (offs : ℕ → ℕ) (P c : ℕ) : List Bool :=
  (List.range c).flatMap (winAt L tp offs P)

theorem outAt_succ {α : Type} (L : List α) (tp : α → List Bool) (offs : ℕ → ℕ) (P c : ℕ) :
    outAt L tp offs P (c + 1) = outAt L tp offs P c ++ winAt L tp offs P c := by
  simp [outAt, List.range_succ]

/-- Weakening the extras: same output and flags, every per-circuit role kept or dropped to `.any`. -/
theorem xr_weaken (W : ℕ) (x x' : XS) (ho : x'.o = x.o) (hT : ∀ d, x'.T d = .any ∨ x'.T d = x.T d)
    (hTm : ∀ d, x'.Tm d = .any ∨ x'.Tm d = x.Tm d) (hoff : ∀ d, x'.off d = .any ∨ x'.off d = x.off d)
    (hlen : ∀ d, x'.len d = .any ∨ x'.len d = x.len d) (h1 : x'.f1 = x.f1) (h2 : x'.f2 = x.f2) :
    ∀ i H A, TR W (xr x i) H A → TR W (xr x' i) H A := by
  intro i H A hi
  simp only [xr] at hi ⊢
  rw [ho, h1, h2]
  split_ifs at hi ⊢
  · exact hi
  · exact hi
  · rcases hT (i.val - 2) with e | e <;> rw [e] <;> first | trivial | exact hi
  · rcases hTm (i.val - 6) with e | e <;> rw [e] <;> first | trivial | exact hi
  · rcases hoff (i.val - 10) with e | e <;> rw [e] <;> first | trivial | exact hi
  · rcases hlen (i.val - 14) with e | e <;> rw [e] <;> first | trivial | exact hi
  · exact hi
  · exact hi

theorem R_weaken (W : ℕ) (w : List Bool) (s s' : Native.NS) (x x' : XS)
    (hs : ∀ i H A, TR W (Native.nv w s i) H A → TR W (Native.nv w s' i) H A)
    (hx : ∀ i H A, TR W (xr x i) H A → TR W (xr x' i) H A) :
    ∀ i H A, TR W (R w s x i) H A → TR W (R w s' x' i) H A := by
  intro i
  refine Fin.addCases (fun i0 => ?_) (fun k => ?_) i
  · simp only [R, Fin.addCases_left]; exact hs i0
  · simp only [R, Fin.addCases_right]; exact hx k

/-- The native state with circuit `c`'s stream role replaced. -/
def setS (s : Native.NS) (c : Fin 4) (t : TS) : Native.NS := { s with ct := Function.update s.ct (Native.cS c) t }

/-- **One block.** -/
theorem blockW_run {α : Type} {W : ℕ} (w pre : List Bool) (L : List α) (pay : α → List Bool) (num : α → ℕ)
    (tp rest : α → List Bool)
    (hw : w = pre ++ L.flatMap (fun a => frame (pay a)))
    (hpay : ∀ a, pay a = natWord (num a) ++ frame (tp a) ++ rest a)
    (hnb : ∀ a ∈ L, natBitLength (num a) ≤ W) (hW1 : 1 ≤ W)
    (hsumB : (L.map (fun a => num a + 1)).sum < 2 ^ W) (hprodB : (L.map (fun a => num a + 1)).prod < 2 ^ W)
    (S0 : Native.NS) (offs : ℕ → ℕ) (P B : ℕ) (hB : ∀ d, d < L.length → offs d ≤ B)
    (c : Fin 4) (bb pp : ℕ) (f1 f2 : Bool) :
    ∃ bb' pp' f1' f2', LRuns W (blockW c) (blockWCost W w.length B P)
      (R w (Native.chainSt S0 pre L (fun a => frame (pay a)) (fun a => num a + 1) c.val bb pp)
        (xc (outAt L tp offs P c.val) c.val offs P f1 f2))
      (R w (Native.chainSt S0 pre L (fun a => frame (pay a)) (fun a => num a + 1) (c.val + 1) bb' pp')
        (xc (outAt L tp offs P (c.val + 1)) (c.val + 1) offs P f1' f2')) := by
  set F : α → List Bool := fun a => frame (pay a) with hF
  set g : α → ℕ := fun a => num a + 1 with hg
  set s := Native.chainSt S0 pre L F g c.val bb pp with hsdef
  set x := xc (outAt L tp offs P c.val) c.val offs P f1 f2 with hxdef
  have hct : s.ct = Native.ctAfter c.val := rfl
  have e0 : LRuns W (liftW (RecoveryFocus.machine ![(2 : Fin 26), 6] peek)) 1 (R w s x)
      (R w { s with fl := sf w s.sp } x) := liftL (Native.peekS (W := W) w s) (xr x)
  have hxc : ∀ d, d ≠ c.val → ∀ (o : List Bool) (f1 f2 f1' f2' : Bool),
      ((xc o c.val offs P f1 f2).T d = .any ∨ (xc o c.val offs P f1 f2).T d = (xc o (c.val + 1) offs P f1' f2').T d) := by
    intro d hd o f1 f2 f1' f2'
    right; simp only [xc]
    split_ifs <;> first | rfl | omega
  by_cases hc : c.val < L.length
  · -- a circuit is present
    have hp := hpay L[c.val]
    have hsplit := Native.flatMap_split L F c.val hc
    have hpl : (pay L[c.val]).length ≤ w.length := by
      have h1 : (F L[c.val]).length ≤ w.length := by
        rw [hw, hsplit]; simp only [List.length_append]; omega
      have h2 : (F L[c.val]).length = 2 * (pay L[c.val]).length + 1 := RepairOrdinary.frame_length _
      omega
    have hX : ∀ i, i < (frame (pay L[c.val])).length →
        sf w (s.sp + i) = (frame (pay L[c.val])).getD i false := by
      intro i hi
      have e : w = (pre ++ (L.take c.val).flatMap F) ++ F L[c.val] ++ (L.drop (c.val + 1)).flatMap F := by
        rw [hw, hsplit]; simp only [List.append_assoc]
      have := Native.sf_mid (pre ++ (L.take c.val).flatMap F) (F L[c.val]) ((L.drop (c.val + 1)).flatMap F) i hi
      rw [e]
      convert this using 2
      simp only [hsdef, Native.chainSt, List.length_append]
      omega
    have hne : 0 < (frame (pay L[c.val])).length := by rw [RepairOrdinary.frame_length]; omega
    have hbit : sf w s.sp = true := by
      have := hX 0 hne
      rw [Nat.add_zero] at this
      rw [this, hp]
      have hl := ReadNat.natWord_length (num L[c.val])
      cases hn : natWord (num L[c.val]) with
      | nil => rw [hn] at hl; simp at hl
      | cons y ys => simp [RepairOrdinary.frame]
    have hsum1 := Native.sum_take_le L g (c.val + 1)
    have hprod1 := Native.prod_take_le L g (fun a _ => by simp [hg]) (c.val + 1)
    rw [Native.take_succ_of_lt L c.val hc, List.map_append, List.sum_append] at hsum1
    rw [Native.take_succ_of_lt L c.val hc, List.map_append, List.prod_append] at hprod1
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.prod_cons, List.prod_nil,
      Nat.add_zero, Nat.mul_one] at hsum1 hprod1
    have hx : num L[c.val] + 1 < 2 ^ W := by
      show g L[c.val] < 2 ^ W
      have := lt_of_le_of_lt hsum1 hsumB
      omega
    have e1 := liftL (Native.body_run (W := W) w { s with fl := sf w s.sp } c (pay L[c.val])
      (frame (tp L[c.val]) ++ rest L[c.val]) (num L[c.val]) (by rw [hp, List.append_assoc]) hX
      (by show s.ct (Native.cS c) = _; rw [hct]; exact Native.ctAfter_S c)
      (by show s.ct (Native.cM c) = _; rw [hct]; exact Native.ctAfter_M c) (hnb _ (List.getElem_mem hc)) hW1 hx
      (by show ((L.take c.val).map g).sum + g L[c.val] < 2 ^ W; exact lt_of_le_of_lt hsum1 hsumB)
      (by show ((L.take c.val).map g).prod * g L[c.val] < 2 ^ W; exact lt_of_le_of_lt hprod1 hprodB)) (xr x)
    set s1 := Native.bodyOut { s with fl := sf w s.sp } c (pay L[c.val]) (num L[c.val]) with hs1
    have hs1ct : s1.ct (Native.cS c) = .cells (sf (pay L[c.val])) (1 + (natWord (num L[c.val])).length) := by
      have hne' : Native.cS c ≠ Native.cM c := by
        fin_cases c <;> decide
      simp [hs1, Native.bodyOut, Native.rbS, Native.uf, Function.update_apply, hne']
    have hXt : ∀ i, i < (frame (tp L[c.val])).length →
        sf (pay L[c.val]) (1 + (natWord (num L[c.val])).length + i) = (frame (tp L[c.val])).getD i false := by
      intro i hi
      have := Native.sf_mid (natWord (num L[c.val])) (frame (tp L[c.val])) (rest L[c.val]) i hi
      rw [hp, show 1 + (natWord (num L[c.val])).length + i = (natWord (num L[c.val])).length + i + 1 by omega]
      exact this
    have e2 := tailD_run W c w s1 x (sf (pay L[c.val])) (1 + (natWord (num L[c.val])).length) (tp L[c.val])
      (offs c.val) P hs1ct (by simp [hxdef, xc]) (by simp [hxdef, xc]) (by simp [hxdef, xc]) (by simp [hxdef, xc]) hXt
    have htl : (tp L[c.val]).length ≤ w.length := by
      have h1 := congrArg List.length hp
      simp only [List.length_append, RepairOrdinary.frame_length] at h1
      omega
    have hcostT : Win.tailCost (tp L[c.val]).length (offs c.val) P ≤ Win.tailCost w.length B P := by
      have := hB c.val hc
      have h3 := Nat.mul_le_mul_right (1 + (1 + 1 + 1) + 2) (show offs c.val + 1 ≤ B + 1 by omega)
      unfold Win.tailCost; omega
    have hcostB : Native.bodyCost W (pay L[c.val]).length ≤ Native.bodyCost W w.length := by
      unfold Native.bodyCost; omega
    have hrun : LRuns W (blockW c) (blockWCost W w.length B P) (R w s x)
        (R w (setS s1 c (.cells (sf (pay L[c.val])) (1 + (natWord (num L[c.val])).length + (frame (tp L[c.val])).length)))
          (postX x c.val (tp L[c.val]) (offs c.val) P)) := by
      unfold blockW blockWCost
      exact Ite.runs (W := W) (np := Native.bodyCost W w.length + 1 + Win.tailCost w.length B P) (nq := 0) _ _ _
        (Fin.castAdd 20 (6 : Fin 26)) true e0 (by rw [R_castAdd]; simp [Native.nv, hbit])
        (fun _ => ((e1.seq e2).enlarge (by omega))) (fun h => by simp at h)
    have hstate : ({ s1 with ct := Native.ctAfter (c.val + 1) } : Native.NS) =
        Native.chainSt S0 pre L F g (c.val + 1) (num L[c.val] + 1) (((L.take c.val).map g).prod * (num L[c.val] + 1)) := by
      simp only [hs1, hsdef, Native.bodyOut, Native.rbS, Native.uf, Native.chainSt, Native.take_succ_of_lt L c.val hc,
        List.flatMap_append, List.map_append, List.sum_append, List.prod_append, List.length_append,
        List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.prod_cons, List.prod_nil, List.append_nil]
      simp only [hF, hg]
      congr 1 <;> ring
    refine ⟨num L[c.val] + 1, ((L.take c.val).map g).prod * (num L[c.val] + 1), false,
      lastBit (tp L[c.val]) (offs c.val) f2 P, ?_⟩
    rw [← hstate]
    refine hrun.weaken (R_weaken W w _ _ _ _ ?_ ?_)
    · refine Native.weaken_ct w _ _ ?_
      intro j H A h
      simp only [setS, hs1, Native.bodyOut, Native.rbS, Native.uf] at h
      rw [hct] at h
      fin_cases c <;> fin_cases j <;> first | trivial | exact h
    · refine xr_weaken W _ _ ?_ ?_ ?_ ?_ ?_ rfl rfl
      · simp only [xc, postX, hxdef]
        rw [outAt_succ]; simp [winAt, hc]
      · intro d; simp only [xc, postX, hxdef, Function.update_apply]
        split_ifs <;> first | (left; rfl) | (right; rfl) | omega
      · intro d; simp only [xc, postX, hxdef, Function.update_apply]
        split_ifs <;> first | (left; rfl) | (right; rfl) | omega
      · intro d; simp only [xc, postX, hxdef, Function.update_apply]
        split_ifs <;> first | (left; rfl) | (right; rfl) | omega
      · intro d; simp only [xc, postX, hxdef, Function.update_apply]
        split_ifs <;> first | (left; rfl) | (right; rfl) | omega
  · -- no circuit left
    have hle : L.length ≤ c.val := by omega
    have htake : L.take c.val = L := List.take_of_length_le hle
    have htake1 : L.take (c.val + 1) = L := List.take_of_length_le (by omega)
    have hbit : sf w s.sp = false := by
      simp only [hsdef, Native.chainSt, htake]
      rw [show 1 + pre.length + (L.flatMap F).length = (pre.length + (L.flatMap F).length) + 1 by omega, sf_succ]
      apply List.getD_eq_default
      rw [hw]; simp
    have hrun : LRuns W (blockW c) (blockWCost W w.length B P) (R w s x) (R w { s with fl := false } x) := by
      unfold blockW blockWCost
      have hq : LRuns W (nop (26 + 20)) 0 (R w { s with fl := sf w s.sp } x) (R w { s with fl := false } x) := by
        rw [hbit]; exact nop_lruns _
      exact Ite.runs (W := W) (np := Native.bodyCost W w.length + 1 + Win.tailCost w.length B P) (nq := 0) _ _ _
        (Fin.castAdd 20 (6 : Fin 26)) false e0 (by rw [R_castAdd]; simp [Native.nv, hbit]) (fun h => by simp at h) (fun _ => hq)
    have hstate : ({ s with fl := false, ct := Native.ctAfter (c.val + 1) } : Native.NS) =
        Native.chainSt S0 pre L F g (c.val + 1) bb pp := by
      simp only [hsdef, Native.chainSt, htake, htake1]
    refine ⟨bb, pp, f1, f2, ?_⟩
    rw [← hstate]
    refine hrun.weaken (R_weaken W w _ _ _ _ ?_ ?_)
    · refine Native.weaken_ct w _ _ ?_
      intro j H A h
      simp only [hct] at h
      fin_cases c <;> fin_cases j <;> first | trivial | exact h
    · refine xr_weaken W _ _ ?_ ?_ ?_ ?_ ?_ rfl rfl
      · simp only [xc, hxdef]
        rw [outAt_succ]; simp [winAt, hc]
      · intro d; simp only [xc, hxdef]
        split_ifs <;> first | (left; rfl) | (right; rfl) | omega
      · intro d; simp only [xc, hxdef]
        split_ifs <;> first | (left; rfl) | (right; rfl) | omega
      · intro d; simp only [xc, hxdef]
        split_ifs <;> first | (left; rfl) | (right; rfl) | omega
      · intro d; simp only [xc, hxdef]
        split_ifs <;> first | (left; rfl) | (right; rfl) | omega

/-! ## The whole program -/

theorem winAt_length_le {α : Type} (L : List α) (tp : α → List Bool) (offs : ℕ → ℕ) (P d : ℕ) :
    (winAt L tp offs P d).length ≤ P := by
  unfold winAt; split_ifs <;> simp [win]

theorem outAt_length_le {α : Type} (L : List α) (tp : α → List Bool) (offs : ℕ → ℕ) (P : ℕ) :
    ∀ c, (outAt L tp offs P c).length ≤ c * P := by
  intro c
  induction c with
  | zero => simp [outAt]
  | succ c ih =>
    rw [outAt_succ, List.length_append, Nat.succ_mul]
    have := winAt_length_le L tp offs P c
    omega

/-- The entry roles of the 20 extra tapes: blank output pair and top tapes, the unary offsets and the window length
(head 0), two flags. -/
def xin (offs : ℕ → ℕ) (P : ℕ) : Fin 20 → TS := fun i =>
  if i.val < 10 then .cells PacketsMeta.blank 0 else if i.val < 14 then uw (offs (i.val - 10)) 0
  else if i.val < 18 then uw P 0 else .flag false

/-- Both output tapes to cursor `1`. -/
def initOutW := RecoveryFocus.machine ![ex 0 (by omega), ex 1 (by omega)]
  (oneStep 2 (fun _ => (fun _ => none, fun _ => .right)))

theorem initOutW_run (W : ℕ) (σ : Fin 26 → TS) (offs : ℕ → ℕ) (P : ℕ) :
    LRuns W initOutW 1 (Fin.addCases σ (xin offs P)) (Fin.addCases σ (xr (xc [] 0 offs P false false))) := by
  have h := (PacketsSymBits.initOut_local W).dockK ![ex 0 (by omega), ex 1 (by omega)] (by decide)
    (Fin.addCases σ (xin offs P)) (by intro i; fin_cases i <;> rfl) [0, 1] (by intro i hi; fin_cases i <;> simp at hi)
  refine h.congr_out ?_
  funext i; fin_cases i <;> rfl

/-- Rewind the output pair to cursor `1`. -/
def rwSlots : Fin 2 → Fin (26 + 20) := ![ex 1 (by omega), ex 0 (by omega)]

theorem rwSlots_inj : Function.Injective rwSlots := by decide

def rewindOutW := RecoveryFocus.machine rwSlots rewind

/-- **The SYM lookup-bit program.** -/
def symProg :=
  Composition.machine initOutW
    (Composition.machine (liftW Native.front)
      (Composition.machine (liftW Native.header)
        (Composition.machine (liftW (swAt addF true true (4 : Fin 26) 12 7 6))
          (Composition.machine (blockW 0)
            (Composition.machine (blockW 1)
              (Composition.machine (blockW 2)
                (Composition.machine (blockW 3) rewindOutW)))))))

def symCost (W m B P : ℕ) : ℕ :=
  1 + 1 + (Native.frontCost W m + 1 + (Native.headerCost W + 1 + ((2 * W + 3) + 1 +
    (blockWCost W m B P + 1 + (blockWCost W m B P + 1 + (blockWCost W m B P + 1 + (blockWCost W m B P + 1 +
      (4 * P + 5))))))))

/-- **The program's run.** On the native word of a SYM request, with circuit `c`'s offset `offs c` and the window
length `P` in unary on tapes `36+c`, `40+c`, the output pair ends holding `outAt L tp offs P 4` at cursor `1`. -/
theorem symProg_run {α : Type} (q Lv tg : ℕ) (L : List α) (pay : α → List Bool) (num : α → ℕ)
    (tp rest : α → List Bool) (w : List Bool)
    (hw : w = Native.hdr 0 q Lv tg L.length ++ L.flatMap (fun a => frame (pay a)))
    (hpay : ∀ a, pay a = natWord (num a) ++ frame (tp a) ++ rest a)
    (hnb : ∀ a ∈ L, natBitLength (num a) ≤ 8 * w.length)
    (hsumB : (L.map (fun a => num a + 1)).sum < 2 ^ (8 * w.length))
    (hprodB : (L.map (fun a => num a + 1)).prod < 2 ^ (8 * w.length))
    (offs : ℕ → ℕ) (P B : ℕ) (hB : ∀ d, d < L.length → offs d ≤ B) :
    ∃ σ' : Fin (26 + 20) → TS, LRuns (8 * w.length) symProg (symCost (8 * w.length) w.length B P)
      (Fin.addCases (PacketsKeys.initRoles 26 w) (xin offs P)) σ' ∧
      σ' (ex 0 (by omega)) = .cells (sf (outAt L tp offs P 4)) 1 ∧
      σ' (ex 1 (by omega)) = .cells (sf (List.replicate (outAt L tp offs P 4).length true)) 1 := by
  have hW1 : 1 ≤ w.length := by rw [hw]; simp [Native.hdr, ReadNat.natWord_length]; omega
  have hW8 : 1 ≤ 8 * w.length := by omega
  have hwl : w.length < 2 ^ (8 * w.length) := PacketsKeys.Native.small_lt _ hW1
  have e0 := initOutW_run (8 * w.length) (PacketsKeys.initRoles 26 w) offs P
  have e1 := PacketsSymBits.liftL (Native.front_run w (natWord q ++ natWord Lv ++ natWord tg ++ natWord L.length ++
    L.flatMap (fun a => frame (pay a))) 0 (by rw [hw]; simp [Native.hdr]) (by omega) hW1)
    (xr (xc [] 0 offs P false false))
  have e2 := PacketsSymBits.liftL (Native.header_run w (L.flatMap (fun a => frame (pay a))) 0 q Lv tg L.length hw
    (by omega)) (xr (xc [] 0 offs P false false))
  have e3 := PacketsSymBits.liftL (Native.incProd (W := 8 * w.length) w (Native.sH w 0 q Lv tg L.length) (by
    show 0 + 1 < _
    omega)) (xr (xc [] 0 offs P false false))
  have hs0 := PacketsSymBits.start_eq (Native.sH w 0 q Lv tg L.length) (Native.hdr 0 q Lv tg L.length) L
    (fun a => frame (pay a)) (fun a => num a + 1) rfl rfl rfl rfl
  rw [hs0] at e3
  obtain ⟨b1, p1, f11, f21, g0⟩ := blockW_run (W := 8 * w.length) w (Native.hdr 0 q Lv tg L.length) L pay num tp rest
    hw hpay hnb hW8 hsumB hprodB (Native.sH w 0 q Lv tg L.length) offs P B hB 0
    (Native.sH w 0 q Lv tg L.length).b (Native.sH w 0 q Lv tg L.length).p2 false false
  obtain ⟨b2, p2, f12, f22, g1⟩ := blockW_run (W := 8 * w.length) w (Native.hdr 0 q Lv tg L.length) L pay num tp rest
    hw hpay hnb hW8 hsumB hprodB (Native.sH w 0 q Lv tg L.length) offs P B hB 1 b1 p1 f11 f21
  obtain ⟨b3, p3, f13, f23, g2⟩ := blockW_run (W := 8 * w.length) w (Native.hdr 0 q Lv tg L.length) L pay num tp rest
    hw hpay hnb hW8 hsumB hprodB (Native.sH w 0 q Lv tg L.length) offs P B hB 2 b2 p2 f12 f22
  obtain ⟨b4, p4, f14, f24, g3⟩ := blockW_run (W := 8 * w.length) w (Native.hdr 0 q Lv tg L.length) L pay num tp rest
    hw hpay hnb hW8 hsumB hprodB (Native.sH w 0 q Lv tg L.length) offs P B hB 3 b3 p3 f13 f23
  have hml := outAt_length_le L tp offs P 4
  have e5 := (rewind_lruns (8 * w.length) (outAt L tp offs P 4).length ((outAt L tp offs P 4).length + 1)
    (sf (outAt L tp offs P 4)) (by omega) (by omega)).dockK
    rwSlots rwSlots_inj
    (R w (Native.chainSt (Native.sH w 0 q Lv tg L.length) (Native.hdr 0 q Lv tg L.length) L (fun a => frame (pay a))
      (fun a => num a + 1) 4 b4 p4) (xc (outAt L tp offs P 4) 4 offs P f14 f24))
    (by intro i; fin_cases i <;> rfl) [0, 1] (by intro i hi; fin_cases i <;> simp at hi)
  have hall := e0.seq (e1.seq (e2.seq (e3.seq (g0.seq (g1.seq (g2.seq (g3.seq e5)))))))
  refine ⟨_, hall.enlarge ?_, rfl, rfl⟩
  unfold symCost
  omega

end
end NearCubicWires.PacketsSymBits.Prog
