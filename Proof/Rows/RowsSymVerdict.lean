import Proof.Rows.RowsSymMeaning
import Proof.Rows.CountFlags
import Proof.Rows.FinalCellComparator

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.SymVerdict
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairSource.CloseoutFinal
open SignedSortKey
noncomputable section

/-! ## 1. Generic focusing -/

theorem focus_at {t u s : Nat} {p : Machine t s} {n : Nat} {hin hout : Fin t → ℕ}
    {tin tout : Fin t → List Bool} (h : Step p n hin tin hout tout) (slots : Fin t → Fin u)
    (hi : Function.Injective slots) (H : Fin u → ℕ) (A : Fin u → List Bool)
    (hH : ∀ j, H (slots j) = hin j) (hA : ∀ j, A (slots j) = tin j) :
    Step (RecoveryFocus.machine slots p) n H A (dockH slots H hout) (install slots A tout) := by
  have h' := h.focus slots hi H A
  rwa [dockH_existing slots H hin hH, install_existing slots A tin hA] at h'

/-! ## 2. The comparator and the counter as `Step`s -/

theorem cmp_step (left right output : List Bool) (hw : left.length = right.length) :
    Step C10CellComparator.machine (2*left.length+1)
      ![0, 0, output.length] ![frame left, frame right, output]
      ![2*left.length+1, 2*right.length+1, (output ++ [decide (left = right)]).length]
      ![frame left, frame right, output ++ [decide (left = right)]] := by
  obtain ⟨r, hr, hf, _⟩ := C10CellComparator.equal_run [] [] left right [] [] output hw
  simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at hr hf
  exact Step.of_run hr (by rw [hf]; rfl) (by rw [hf]; rfl)

/-- The comparator with its output head reset (so the verdict is read at head 0). -/
theorem cmp_masked (left right : List Bool) (cap : Nat) (hw : left.length = right.length)
    (hcap : 2*left.length+1 ≤ cap) :
    Step (MaskedReset.machine C10CellComparator.machine (fun i => decide (i = 2)))
      (2*(2*left.length+1)+2)
      (Fin.addCases (![0, 0, 0] : Fin 3 → ℕ) (fun _ : Fin 1 => 0))
      (Fin.addCases (![frame left, frame right, []] : Fin 3 → List Bool)
        (fun _ : Fin 1 => List.replicate cap false))
      (Fin.addCases (![2*left.length+1, 2*right.length+1, 0] : Fin 3 → ℕ) (fun _ : Fin 1 => 0))
      (Fin.addCases (![frame left, frame right, [decide (left = right)]] : Fin 3 → List Bool)
        (fun _ : Fin 1 => List.replicate cap false)) := by
  have h := (cmp_step left right [] hw).mask (cap := cap) (fun i => decide (i = 2))
    (by intro i hi; fin_cases i <;> simp at hi ⊢) hcap
  refine (h.congr_in rfl rfl).congr ?_ rfl
  funext i
  refine Fin.addCases (m:=3) (n:=1) (fun j => ?_) (fun j => ?_) i
  · fin_cases j <;> rfl
  · simp only [Fin.addCases_right]

/-- `CountFlags` with its source head reset: counts the `true` flags of the first `N` bits. -/
theorem count_masked (W : List Bool) (N w D cap : Nat) (hN : N ≤ W.length) (hw : N < 2^w)
    (hD : 2*w+1 ≤ D) (hcap : PCJ45bee56da9f34d5a_CountFlags.budget N w ≤ cap) :
    Step (MaskedReset.machine PCJ45bee56da9f34d5a_CountFlags.machine (fun i => decide (i = 2)))
      (2*PCJ45bee56da9f34d5a_CountFlags.budget N w+2)
      (Fin.addCases (![0, 0, 0, 1] : Fin 4 → ℕ) (fun _ : Fin 1 => 0))
      (Fin.addCases (![frame (binary w 0), List.replicate D false, W, CompareMachine.word N] :
        Fin 4 → List Bool) (fun _ : Fin 1 => List.replicate cap false))
      (Fin.addCases (![0, 0, 0, 1] : Fin 4 → ℕ) (fun _ : Fin 1 => 0))
      (Fin.addCases (![frame (binary w ((W.take N).count true)), List.replicate D false, W,
        CompareMachine.word N] : Fin 4 → List Bool) (fun _ : Fin 1 => List.replicate cap false)) := by
  have hlen : (W.take N).length = N := List.length_take_of_le hN
  have base := PCJ45bee56da9f34d5a_CountFlags.run (W.take N) (W.drop N) w D (by rw [hlen]; exact hw) hD
  rw [List.take_append_drop, hlen] at base
  have h := base.mask (cap := cap) (fun i => decide (i = 2))
    (by intro i hi; fin_cases i <;> simp at hi ⊢) hcap
  refine (h.congr_in rfl rfl).congr ?_ rfl
  funext i
  refine Fin.addCases (m:=4) (n:=1) (fun j => ?_) (fun j => ?_) i
  · fin_cases j <;> rfl
  · simp only [Fin.addCases_right]

/-! ## 3. Updating one port -/

theorem install_update {t u : Nat} (slots : Fin t → Fin u) (hi : Function.Injective slots)
    (A : Fin u → List Bool) (tout : Fin t → List Bool) (j0 : Fin t)
    (h : ∀ j, j ≠ j0 → tout j = A (slots j)) :
    install slots A tout = Function.update A (slots j0) (tout j0) := by
  funext x
  by_cases hx : x = slots j0
  · subst hx
    rw [install_slot _ hi, Function.update_self]
  · rw [Function.update_of_ne hx]
    cases hp : RecoveryFocus.pick slots x with
    | none => simp [install, hp]
    | some j =>
      have he := RecoveryFocus.slot_of_pick slots hp
      simp only [install, hp]
      have hj : j ≠ j0 := fun hj => hx (by rw [← he, hj])
      rw [h j hj, he]

/-! ## 4. The local compare phase: four comparisons appended to one bit list -/

def loc9 {α : Type} (cnt tgt : Fin 4 → α) (b : α) : Fin 9 → α :=
  Fin.addCases (m:=8) (n:=1) (Fin.addCases (m:=4) (n:=4) cnt tgt) (fun _ => b)

def cslots (i : Fin 4) : Fin 3 → Fin 9 :=
  ![(i.castAdd 4).castAdd 1, (i.natAdd 4).castAdd 1, (0 : Fin 1).natAdd 8]

theorem cslots_val (i : Fin 4) (j : Fin 3) : (cslots i j).val = ![i.val, 4+i.val, 8] j := by
  fin_cases j <;> rfl

theorem cslots_injective (i : Fin 4) : Function.Injective (cslots i) := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [cslots_val, cslots_val] at hv
  have := i.isLt
  fin_cases a <;> fin_cases b <;> simp at hv ⊢ <;> omega

def cmpI (i : Fin 4) := RecoveryFocus.machine (cslots i) C10CellComparator.machine

theorem cover9 {motive : Fin 9 → Prop} (hc : ∀ k : Fin 4, motive ((k.castAdd 4).castAdd 1))
    (ht : ∀ k : Fin 4, motive ((k.natAdd 4).castAdd 1)) (hb : motive ((0 : Fin 1).natAdd 8))
    (x : Fin 9) : motive x := by
  refine Fin.addCases (m:=8) (n:=1) (fun y => ?_) (fun z => ?_) x
  · exact Fin.addCases (m:=4) (n:=4) (fun k => hc k) (fun k => ht k) y
  · have hz : z = 0 := Fin.eq_zero z
    subst hz
    exact hb

@[simp] theorem loc9_cnt {α : Type} (cnt tgt : Fin 4 → α) (b : α) (k : Fin 4) :
    loc9 cnt tgt b ((k.castAdd 4).castAdd 1) = cnt k := by
  simp only [loc9, Fin.addCases_left]
@[simp] theorem loc9_tgt {α : Type} (cnt tgt : Fin 4 → α) (b : α) (k : Fin 4) :
    loc9 cnt tgt b ((k.natAdd 4).castAdd 1) = tgt k := by
  simp only [loc9, Fin.addCases_left, Fin.addCases_right]
@[simp] theorem loc9_bits {α : Type} (cnt tgt : Fin 4 → α) (b : α) :
    loc9 cnt tgt b ((0 : Fin 1).natAdd 8) = b := by
  simp only [loc9, Fin.addCases_right]

theorem cmpI_step (i : Fin 4) (cnt tgt : Fin 4 → List Bool) (hc ht : Fin 4 → ℕ) (bits l r : List Bool)
    (hw : l.length = r.length) (hcnt : cnt i = frame l) (htgt : tgt i = frame r)
    (hhc : hc i = 0) (hht : ht i = 0) :
    Step (cmpI i) (2*l.length+1) (loc9 hc ht bits.length) (loc9 cnt tgt bits)
      (loc9 (Function.update hc i (2*l.length+1)) (Function.update ht i (2*r.length+1))
        (bits ++ [decide (l = r)]).length)
      (loc9 cnt tgt (bits ++ [decide (l = r)])) := by
  have h := focus_at (cmp_step l r bits hw) (cslots i) (cslots_injective i) (loc9 hc ht bits.length)
    (loc9 cnt tgt bits)
    (by
      intro j
      fin_cases j
      · show loc9 hc ht bits.length ((i.castAdd 4).castAdd 1) = 0
        rw [loc9_cnt]; exact hhc
      · show loc9 hc ht bits.length ((i.natAdd 4).castAdd 1) = 0
        rw [loc9_tgt]; exact hht
      · show loc9 hc ht bits.length ((0 : Fin 1).natAdd 8) = bits.length
        rw [loc9_bits])
    (by
      intro j
      fin_cases j
      · show loc9 cnt tgt bits ((i.castAdd 4).castAdd 1) = frame l
        rw [loc9_cnt]; exact hcnt
      · show loc9 cnt tgt bits ((i.natAdd 4).castAdd 1) = frame r
        rw [loc9_tgt]; exact htgt
      · show loc9 cnt tgt bits ((0 : Fin 1).natAdd 8) = bits
        rw [loc9_bits])
  refine h.congr ?_ ?_
  · funext x
    refine cover9 (motive := fun x => dockH (cslots i) (loc9 hc ht bits.length)
      ![2*l.length+1, 2*r.length+1, (bits ++ [decide (l = r)]).length] x =
      loc9 (Function.update hc i (2*l.length+1)) (Function.update ht i (2*r.length+1))
        (bits ++ [decide (l = r)]).length x) (fun k => ?_) (fun k => ?_) ?_ x
    · rw [loc9_cnt]
      by_cases hk : k = i
      · subst hk
        rw [Function.update_self, show ((k.castAdd 4).castAdd 1 : Fin 9) = cslots k 0 from rfl,
          dockH_slot _ (cslots_injective k)]
        rfl
      · rw [dockH_other _ _ _ _ (fun j he => by
          have hv := congrArg Fin.val he
          rw [cslots_val] at hv
          have hne : k.val ≠ i.val := fun h' => hk (Fin.ext h')
          fin_cases j <;> simp at hv <;> omega), loc9_cnt, Function.update_of_ne hk]
    · rw [loc9_tgt]
      by_cases hk : k = i
      · subst hk
        rw [Function.update_self, show ((k.natAdd 4).castAdd 1 : Fin 9) = cslots k 1 from rfl,
          dockH_slot _ (cslots_injective k)]
        rfl
      · rw [dockH_other _ _ _ _ (fun j he => by
          have hv := congrArg Fin.val he
          rw [cslots_val] at hv
          have hne : k.val ≠ i.val := fun h' => hk (Fin.ext h')
          have := i.isLt
          fin_cases j <;> simp at hv <;> omega), loc9_tgt, Function.update_of_ne hk]
    · rw [loc9_bits, show ((0 : Fin 1).natAdd 8 : Fin 9) = cslots i 2 from rfl,
        dockH_slot _ (cslots_injective i)]
      rfl
  · funext x
    refine cover9 (motive := fun x => install (cslots i) (loc9 cnt tgt bits)
      ![frame l, frame r, bits ++ [decide (l = r)]] x = loc9 cnt tgt (bits ++ [decide (l = r)]) x)
      (fun k => ?_) (fun k => ?_) ?_ x
    · rw [loc9_cnt]
      by_cases hk : k = i
      · subst hk
        rw [show ((k.castAdd 4).castAdd 1 : Fin 9) = cslots k 0 from rfl, install_slot _ (cslots_injective k)]
        exact hcnt.symm
      · rw [install_other _ _ _ _ (fun j he => by
          have hv := congrArg Fin.val he
          rw [cslots_val] at hv
          have hne : k.val ≠ i.val := fun h' => hk (Fin.ext h')
          fin_cases j <;> simp at hv <;> omega), loc9_cnt]
    · rw [loc9_tgt]
      by_cases hk : k = i
      · subst hk
        rw [show ((k.natAdd 4).castAdd 1 : Fin 9) = cslots k 1 from rfl, install_slot _ (cslots_injective k)]
        exact htgt.symm
      · rw [install_other _ _ _ _ (fun j he => by
          have hv := congrArg Fin.val he
          rw [cslots_val] at hv
          have hne : k.val ≠ i.val := fun h' => hk (Fin.ext h')
          have := i.isLt
          fin_cases j <;> simp at hv <;> omega), loc9_tgt]
    · rw [loc9_bits, show ((0 : Fin 1).natAdd 8 : Fin 9) = cslots i 2 from rfl,
        install_slot _ (cslots_injective i)]
      rfl

def cmpLocal := Composition.machine (cmpI 0) (Composition.machine (cmpI 1)
  (Composition.machine (cmpI 2) (cmpI 3)))

def bitsOf (w : Nat) (S T : Fin 4 → Nat) : List Bool :=
  [decide (binary w (S 0) = binary w (T 0)), decide (binary w (S 1) = binary w (T 1)),
    decide (binary w (S 2) = binary w (T 2)), decide (binary w (S 3) = binary w (T 3))]

/-- **The compare phase**: four framed-count comparisons, one bit each, on the local 9-tape layout. -/
theorem cmp_phase (w : Nat) (S T : Fin 4 → Nat) :
    Step cmpLocal ((2*w+1)+1+((2*w+1)+1+((2*w+1)+1+(2*w+1))))
      (loc9 (fun _ => 0) (fun _ => 0) 0)
      (loc9 (fun c => frame (binary w (S c))) (fun c => frame (binary w (T c))) [])
      (loc9 (fun _ => 2*w+1) (fun _ => 2*w+1) 4)
      (loc9 (fun c => frame (binary w (S c))) (fun c => frame (binary w (T c))) (bitsOf w S T)) := by
  have hl : ∀ c, (binary w (S c)).length = w := fun c => binary_length _ _
  have hr : ∀ c, (binary w (T c)).length = w := fun c => binary_length _ _
  have hw : ∀ c, (binary w (S c)).length = (binary w (T c)).length := fun c => by rw [hl, hr]
  let cnt : Fin 4 → List Bool := fun c => frame (binary w (S c))
  let tgt : Fin 4 → List Bool := fun c => frame (binary w (T c))
  let b : Fin 4 → Bool := fun c => decide (binary w (S c) = binary w (T c))
  let v : Nat := 2*w+1
  have s0 := cmpI_step 0 cnt tgt (fun _ => 0) (fun _ => 0) [] (binary w (S 0)) (binary w (T 0)) (hw 0)
    rfl rfl rfl rfl
  have s1 := cmpI_step 1 cnt tgt (Function.update (fun _ => 0) 0 (2*(binary w (S 0)).length+1))
    (Function.update (fun _ => 0) 0 (2*(binary w (T 0)).length+1)) ([] ++ [b 0])
    (binary w (S 1)) (binary w (T 1)) (hw 1) rfl rfl
    (by rw [Function.update_of_ne (by decide)]) (by rw [Function.update_of_ne (by decide)])
  have s2 := cmpI_step 2 cnt tgt
    (Function.update (Function.update (fun _ => 0) 0 (2*(binary w (S 0)).length+1)) 1
      (2*(binary w (S 1)).length+1))
    (Function.update (Function.update (fun _ => 0) 0 (2*(binary w (T 0)).length+1)) 1
      (2*(binary w (T 1)).length+1)) ([] ++ [b 0] ++ [b 1])
    (binary w (S 2)) (binary w (T 2)) (hw 2) rfl rfl
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)])
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)])
  have s3 := cmpI_step 3 cnt tgt
    (Function.update (Function.update (Function.update (fun _ => 0) 0 (2*(binary w (S 0)).length+1)) 1
      (2*(binary w (S 1)).length+1)) 2 (2*(binary w (S 2)).length+1))
    (Function.update (Function.update (Function.update (fun _ => 0) 0 (2*(binary w (T 0)).length+1)) 1
      (2*(binary w (T 1)).length+1)) 2 (2*(binary w (T 2)).length+1)) ([] ++ [b 0] ++ [b 1] ++ [b 2])
    (binary w (S 3)) (binary w (T 3)) (hw 3) rfl rfl
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)])
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)])
  have all := s0.seq (s1.seq (s2.seq s3))
  rw [hl 0, hl 1, hl 2, hl 3, hr 0, hr 1, hr 2, hr 3] at all
  refine all.congr ?_ rfl
  have hfun : Function.update (Function.update (Function.update (Function.update
      (fun _ : Fin 4 => (0 : Nat)) 0 (2*w+1)) 1 (2*w+1)) 2 (2*w+1)) 3 (2*w+1) = fun _ => 2*w+1 := by
    funext c
    fin_cases c <;> simp [Function.update]
  simp only [hfun]
  rfl

/-- The compare phase with the bit-list head reset (the AND count reads it from 0). -/
theorem cmp_phase_masked (w cap : Nat) (S T : Fin 4 → Nat)
    (hcap : (2*w+1)+1+((2*w+1)+1+((2*w+1)+1+(2*w+1))) ≤ cap) :
    Step (MaskedReset.machine cmpLocal (fun j => decide (j = (0 : Fin 1).natAdd 8)))
      (2*((2*w+1)+1+((2*w+1)+1+((2*w+1)+1+(2*w+1))))+2)
      (Fin.addCases (loc9 (fun _ => 0) (fun _ => 0) 0) (fun _ : Fin 1 => 0))
      (Fin.addCases (loc9 (fun c => frame (binary w (S c))) (fun c => frame (binary w (T c))) [])
        (fun _ : Fin 1 => List.replicate cap false))
      (Fin.addCases (loc9 (fun _ => 2*w+1) (fun _ => 2*w+1) 0) (fun _ : Fin 1 => 0))
      (Fin.addCases (loc9 (fun c => frame (binary w (S c))) (fun c => frame (binary w (T c)))
        (bitsOf w S T)) (fun _ : Fin 1 => List.replicate cap false)) := by
  have h := (cmp_phase w S T).mask (cap := cap) (fun j => decide (j = (0 : Fin 1).natAdd 8))
    (by
      intro j hj
      have hj' : j = (0 : Fin 1).natAdd 8 := of_decide_eq_true hj
      subst hj'
      rfl) hcap
  refine h.congr ?_ rfl
  funext i
  refine Fin.addCases (m:=9) (n:=1) (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.addCases_left]
    by_cases hj : j = (0 : Fin 1).natAdd 8
    · subst hj
      rw [if_pos (by simp), loc9_bits]
    · rw [if_neg (by simpa using hj)]
      refine cover9 (motive := fun j => j ≠ (0 : Fin 1).natAdd 8 →
        loc9 (fun _ => 2*w+1) (fun _ => 2*w+1) 4 j = loc9 (fun _ => 2*w+1) (fun _ => 2*w+1) 0 j)
        (fun k _ => ?_) (fun k _ => ?_) (fun h => absurd rfl h) j hj
      · rw [loc9_cnt, loc9_cnt]
      · rw [loc9_tgt, loc9_tgt]
  · simp only [Fin.addCases_right]

/-! ## 5. The SYM cell layout (254 tapes) -/

def symLayout {α : Type} (F : Fin 128 → α) (A : Fin 18 → α) (b o : α) : Fin 254 → α :=
  Fin.addCases (m:=128) (n:=126) F
    (Fin.addCases (m:=18) (n:=108) A (Fin.addCases (m:=107) (n:=1) (fun _ => b) (fun _ => o)))

def flagP (i : Fin 128) : Fin 254 := i.castAdd 126
def auxP (j : Fin 18) : Fin 254 := (j.castAdd 108).natAdd 128
def outP : Fin 254 := (((0 : Fin 1).natAdd 107).natAdd 18).natAdd 128

@[simp] theorem layout_flag {α : Type} (F : Fin 128 → α) (A : Fin 18 → α) (b o : α) (i : Fin 128) :
    symLayout F A b o (flagP i) = F i := by simp [symLayout, flagP]
@[simp] theorem layout_aux {α : Type} (F : Fin 128 → α) (A : Fin 18 → α) (b o : α) (j : Fin 18) :
    symLayout F A b o (auxP j) = A j := by simp [symLayout, auxP]
@[simp] theorem layout_out {α : Type} (F : Fin 128 → α) (A : Fin 18 → α) (b o : α) :
    symLayout F A b o outP = o := rfl

theorem flagP_val (i : Fin 128) : (flagP i).val = i.val := rfl
theorem auxP_val (j : Fin 18) : (auxP j).val = 128+j.val := rfl
theorem outP_val : outP.val = 253 := rfl

/-! ## 6. Stages at arbitrary distinct ports -/

def slots5 (p0 p1 p2 p3 p4 : Fin 254) : Fin (4+1) → Fin 254 :=
  Fin.addCases (m:=4) (n:=1) ![p0, p1, p2, p3] (fun _ => p4)

theorem slots5_val (p0 p1 p2 p3 p4 : Fin 254) (j : Fin (4+1)) :
    (slots5 p0 p1 p2 p3 p4 j).val = ![p0.val, p1.val, p2.val, p3.val, p4.val] j := by
  fin_cases j <;> rfl

theorem slots5_injective (p0 p1 p2 p3 p4 : Fin 254)
    (h : [p0.val, p1.val, p2.val, p3.val, p4.val].Nodup) : Function.Injective (slots5 p0 p1 p2 p3 p4) := by
  intro a b hab
  have hv := congrArg Fin.val hab
  rw [slots5_val, slots5_val] at hv
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at h
  fin_cases a <;> fin_cases b <;> simp at hv ⊢ <;> omega

def slots4 (p0 p1 p2 p3 : Fin 254) : Fin (3+1) → Fin 254 :=
  Fin.addCases (m:=3) (n:=1) ![p0, p1, p2] (fun _ => p3)

theorem slots4_val (p0 p1 p2 p3 : Fin 254) (j : Fin (3+1)) :
    (slots4 p0 p1 p2 p3 j).val = ![p0.val, p1.val, p2.val, p3.val] j := by
  fin_cases j <;> rfl

theorem slots4_injective (p0 p1 p2 p3 : Fin 254) (h : [p0.val, p1.val, p2.val, p3.val].Nodup) :
    Function.Injective (slots4 p0 p1 p2 p3) := by
  intro a b hab
  have hv := congrArg Fin.val hab
  rw [slots4_val, slots4_val] at hv
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at h
  fin_cases a <;> fin_cases b <;> simp at hv ⊢ <;> omega

/-- A masked count at five distinct ports (counter, scratch, source, driver, log): the counter is the
only port that changes, heads return. -/
theorem count_at (p0 p1 p2 p3 p4 : Fin 254) (hinj : Function.Injective (slots5 p0 p1 p2 p3 p4))
    (W : List Bool) (N w D cap : Nat) (hN : N ≤ W.length) (hw : N < 2^w) (hD : 2*w+1 ≤ D)
    (hcap : PCJ45bee56da9f34d5a_CountFlags.budget N w ≤ cap) (H : Fin 254 → ℕ) (A : Fin 254 → List Bool)
    (h0 : H p0 = 0) (h1 : H p1 = 0) (h2 : H p2 = 0) (h3 : H p3 = 1) (h4 : H p4 = 0)
    (a0 : A p0 = frame (binary w 0)) (a1 : A p1 = List.replicate D false) (a2 : A p2 = W)
    (a3 : A p3 = CompareMachine.word N) (a4 : A p4 = List.replicate cap false) :
    Step (RecoveryFocus.machine (slots5 p0 p1 p2 p3 p4)
        (MaskedReset.machine PCJ45bee56da9f34d5a_CountFlags.machine (fun i => decide (i = 2))))
      (2*PCJ45bee56da9f34d5a_CountFlags.budget N w+2) H A H
      (Function.update A p0 (frame (binary w ((W.take N).count true)))) := by
  have h := focus_at (count_masked W N w D cap hN hw hD hcap) (slots5 p0 p1 p2 p3 p4) hinj H A
    (by intro j; fin_cases j
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4)
    (by intro j; fin_cases j
        · exact a0
        · exact a1
        · exact a2
        · exact a3
        · exact a4)
  refine h.congr ?_ ?_
  · apply dockH_existing
    intro j; fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  · apply install_update (slots5 p0 p1 p2 p3 p4) hinj A _ ((0 : Fin 4).castAdd 1)
    intro j hj; fin_cases j
    · exact absurd rfl hj
    · exact a1.symm
    · exact a2.symm
    · exact a3.symm
    · exact a4.symm

/-- A masked comparison at four distinct ports (left, right, empty output, log): the output becomes the
one-bit verdict with head 0. -/
theorem cmp_at (p0 p1 p2 p3 : Fin 254) (hinj : Function.Injective (slots4 p0 p1 p2 p3))
    (l r : List Bool) (cap : Nat) (hw : l.length = r.length) (hcap : 2*l.length+1 ≤ cap)
    (H : Fin 254 → ℕ) (A : Fin 254 → List Bool)
    (h0 : H p0 = 0) (h1 : H p1 = 0) (h2 : H p2 = 0) (h3 : H p3 = 0)
    (a0 : A p0 = frame l) (a1 : A p1 = frame r) (a2 : A p2 = []) (a3 : A p3 = List.replicate cap false) :
    ∃ H', Step (RecoveryFocus.machine (slots4 p0 p1 p2 p3)
        (MaskedReset.machine C10CellComparator.machine (fun i => decide (i = 2))))
      (2*(2*l.length+1)+2) H A H' (Function.update A p2 [decide (l = r)]) ∧ H' p2 = 0 := by
  have h := focus_at (cmp_masked l r cap hw hcap) (slots4 p0 p1 p2 p3) hinj H A
    (by intro j; fin_cases j
        · exact h0
        · exact h1
        · exact h2
        · exact h3)
    (by intro j; fin_cases j
        · exact a0
        · exact a1
        · exact a2
        · exact a3)
  refine ⟨_, h.congr rfl ?_, ?_⟩
  · apply install_update (slots4 p0 p1 p2 p3) hinj A _ ((2 : Fin 3).castAdd 1)
    intro j hj; fin_cases j
    · exact a0.symm
    · exact a1.symm
    · exact absurd rfl hj
    · exact a3.symm
  · exact dockH_slot (slots4 p0 p1 p2 p3) hinj H _ ((2 : Fin 3).castAdd 1)

/-! ## 7. The bit the machine writes is the row selector -/

theorem binary_inj (w a b : Nat) (ha : a < 2^w) (hb : b < 2^w) : binary w a = binary w b ↔ a = b := by
  constructor
  · intro h
    have := congrArg RadixSemantics.value h
    rwa [binary_value w a ha, binary_value w b hb] at this
  · intro h; rw [h]

theorem count4 (b0 b1 b2 b3 : Bool) :
    [b0, b1, b2, b3].count true = 4 ↔ (b0 = true ∧ b1 = true ∧ b2 = true ∧ b3 = true) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide

theorem count4_le (b0 b1 b2 b3 : Bool) : [b0, b1, b2, b3].count true ≤ 4 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide

variable (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)

/-- **The verdict bit.** With cumulative drivers and targets fitting `w` bits, the comparison of the
count of agreeing slots with `4` decides exactly the SYM row selector. -/
theorem bit_eq (four : r.circuits.length ≤ 4) (I : Finset (Fin r.q)) (x : BitInput r.q)
    (offset : Fin r.circuits.length → Nat) (w : Nat) (hw4 : 4 < 2^w)
    (hN : ∀ c : Fin 4, SymMeaning.driverLen r c.val < 2^w)
    (hT : ∀ c : Fin 4, SymMeaning.targetCount r offset c.val < 2^w) :
    decide (binary w (((bitsOf w
        (fun c : Fin 4 => ((PCJ45bee56da9f34d5a_NativeFlags.word (SymMeaning.circuits r) I x).take
          (SymMeaning.driverLen r c.val)).count true)
        (fun c : Fin 4 => SymMeaning.targetCount r offset c.val)).take 4).count true) = binary w 4) =
      decide (PCJ9eff70d512234a4c_Fixed.LiveRows.symOffsets r I x = offset) := by
  set W := PCJ45bee56da9f34d5a_NativeFlags.word (SymMeaning.circuits r) I x with hWdef
  have hW : W = SymMeaning.flagged (r.circuits.map (fun k => SymMeaning.block k I x)) ++ [true] := by
    rw [hWdef, SymMeaning.word_eq, SymMeaning.flagged, List.flatMap_map]
  have hS : ∀ c : Fin 4, (W.take (SymMeaning.driverLen r c.val)).count true < 2^w := fun c =>
    lt_of_le_of_lt ((List.count_le_length).trans (List.length_take_le _ _)) (hN c)
  have hbit : ∀ c : Fin 4, decide (binary w ((W.take (SymMeaning.driverLen r c.val)).count true) =
      binary w (SymMeaning.targetCount r offset c.val)) =
      decide ((W.take (SymMeaning.driverLen r c.val)).count true = SymMeaning.targetCount r offset c.val) :=
    fun c => decide_eq_decide.mpr (binary_inj w _ _ (hS c) (hT c))
  unfold bitsOf
  rw [hbit 0, hbit 1, hbit 2, hbit 3]
  have htake : ∀ l : List Bool, l.length = 4 → l.take 4 = l := fun l hl => List.take_of_length_le (by omega)
  rw [htake _ rfl]
  have hk := count4_le (decide ((W.take (SymMeaning.driverLen r (0 : Fin 4).val)).count true =
      SymMeaning.targetCount r offset (0 : Fin 4).val))
    (decide ((W.take (SymMeaning.driverLen r (1 : Fin 4).val)).count true =
      SymMeaning.targetCount r offset (1 : Fin 4).val))
    (decide ((W.take (SymMeaning.driverLen r (2 : Fin 4).val)).count true =
      SymMeaning.targetCount r offset (2 : Fin 4).val))
    (decide ((W.take (SymMeaning.driverLen r (3 : Fin 4).val)).count true =
      SymMeaning.targetCount r offset (3 : Fin 4).val))
  have e : ∀ k : Nat, k ≤ 4 → decide (binary w k = binary w 4) = decide (k = 4) := fun k hk' =>
    decide_eq_decide.mpr (binary_inj w k 4 (lt_of_le_of_lt hk' hw4) hw4)
  rw [e _ hk]
  apply decide_eq_decide.mpr
  rw [count4, SymMeaning.sym_select_iff r I x offset, ← hW]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩ c
    by_cases hc : c < 4
    · interval_cases c
      · exact h0
      · exact h1
      · exact h2
      · exact h3
    · have hc' : ¬ c < r.circuits.length := by omega
      simp [SymMeaning.driverLen, SymMeaning.targetCount, hc']
  · intro h
    exact ⟨h 0, h 1, h 2, h 3⟩

/-! ## 8. The flag stage and the compare stage on the SYM layout -/

def flagSlots : Fin (128+1) → Fin 254 := Fin.addCases (m:=128) (n:=1) flagP (fun _ => auxP 6)

theorem flagSlots_val (j : Fin (128+1)) : (flagSlots j).val = if j.val < 128 then j.val else 134 := by
  refine Fin.addCases (m:=128) (n:=1) (fun i => ?_) (fun k => ?_) j
  · simp only [flagSlots, Fin.addCases_left, flagP_val, Fin.val_castAdd]
    rw [if_pos i.isLt]
  · have hk : k = 0 := Fin.eq_zero k
    subst hk
    rfl

theorem flagSlots_injective : Function.Injective flagSlots := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [flagSlots_val, flagSlots_val] at hv
  have := a.isLt
  have := b.isLt
  apply Fin.ext
  split_ifs at hv <;> omega

theorem not_flag_aux (k : Fin 18) (hk : k ≠ 6) : ∀ j, flagSlots j ≠ auxP k := by
  intro j he
  have hv := congrArg Fin.val he
  rw [flagSlots_val, auxP_val] at hv
  have hk' : k.val ≠ 6 := fun h => hk (Fin.ext h)
  split_ifs at hv <;> omega

theorem not_flag_out : ∀ j, flagSlots j ≠ outP := by
  intro j he
  have hv := congrArg Fin.val he
  rw [flagSlots_val, outP_val] at hv
  split_ifs at hv <;> omega

def flagStage := RecoveryFocus.machine flagSlots
  (MaskedReset.machine PCJ45bee56da9f34d5a_NativeFamilyFlags.machine (fun i => decide (i = 107)))

def src (L target : Nat) := PCJ45bee56da9f34d5a_NativeFamilyFlags.source 0 L target (SymMeaning.circuits r)

theorem flag_stage (I : Finset (Fin r.q)) (x : BitInput r.q) (T L target cap : Nat)
    (hb : (src r L target).length ≤ T)
    (hcap : PCJ45bee56da9f34d5a_NativeFamilyFlags.budget 0 r.q L target (SymMeaning.circuits r).length T ≤ cap)
    (H : Fin 254 → ℕ) (A : Fin 254 → List Bool)
    (hH : ∀ i, H (flagP i) = PCJ45bee56da9f34d5a_NativeFamilyCount.heads 0 [] 0 0 i) (hH6 : H (auxP 6) = 0)
    (hA : ∀ i, A (flagP i) = PCJ45bee56da9f34d5a_NativeFamilyCount.bank I x T 0 (src r L target) []
      (List.replicate (PCJ45bee56da9f34d5a_UniformMinimumBounds.U T r.q (T+1)) false) i)
    (hA6 : A (auxP 6) = List.replicate cap false) :
    ∃ H' A', Step flagStage
        (2*PCJ45bee56da9f34d5a_NativeFamilyFlags.budget 0 r.q L target (SymMeaning.circuits r).length T+2)
        H A H' A' ∧
      A' (flagP 107) = PCJ45bee56da9f34d5a_NativeFlags.word (SymMeaning.circuits r) I x ∧
      H' (flagP 107) = 0 ∧ H' (auxP 6) = 0 ∧ A' (auxP 6) = List.replicate cap false ∧
      ∀ p, (∀ j, flagSlots j ≠ p) → H' p = H p ∧ A' p = A p := by
  have base := (PCJ45bee56da9f34d5a_NativeFamilyFlags.run (SymMeaning.circuits r) I x [] T 0 0 L target hb).mask
    (cap := cap) (fun i => decide (i = 107)) (by
      intro i hi
      have hi' : i = 107 := of_decide_eq_true hi
      subst hi'
      rfl) hcap
  have h := focus_at base flagSlots flagSlots_injective H A
    (by
      intro j
      refine Fin.addCases (m:=128) (n:=1) (fun i => ?_) (fun k => ?_) j
      · simp only [flagSlots, Fin.addCases_left]; exact hH i
      · simp only [flagSlots, Fin.addCases_right]; exact hH6)
    (by
      intro j
      refine Fin.addCases (m:=128) (n:=1) (fun i => ?_) (fun k => ?_) j
      · simp only [flagSlots, Fin.addCases_left]; exact hA i
      · simp only [flagSlots, Fin.addCases_right]; exact hA6)
  refine ⟨_, _, h, ?_, ?_, ?_, ?_, ?_⟩
  · have e : flagP 107 = flagSlots ((107 : Fin 128).castAdd 1) := by simp only [flagSlots, Fin.addCases_left]
    rw [e, install_slot _ flagSlots_injective]
    simp only [Fin.addCases_left, List.nil_append]
    rfl
  · have e : flagP 107 = flagSlots ((107 : Fin 128).castAdd 1) := by simp only [flagSlots, Fin.addCases_left]
    rw [e, dockH_slot _ flagSlots_injective, Fin.addCases_left]
    simp
  · have e : auxP 6 = flagSlots ((0 : Fin 1).natAdd 128) := by simp only [flagSlots, Fin.addCases_right]
    rw [e, dockH_slot _ flagSlots_injective]
    simp only [Fin.addCases_right]
  · have e : auxP 6 = flagSlots ((0 : Fin 1).natAdd 128) := by simp only [flagSlots, Fin.addCases_right]
    rw [e, install_slot _ flagSlots_injective]
    simp only [Fin.addCases_right]
  · intro p hp
    exact ⟨dockH_other _ _ _ _ hp, install_other _ _ _ _ hp⟩

def cIdx (c : Fin 4) : Fin 18 := c.castLE (by omega)
def dIdx (c : Fin 4) : Fin 18 := ⟨7+c.val, by omega⟩
def tIdx (c : Fin 4) : Fin 18 := ⟨12+c.val, by omega⟩

def cmpSlots : Fin (9+1) → Fin 254 :=
  Fin.addCases (m:=9) (n:=1) (loc9 (fun c => auxP (cIdx c)) (fun c => auxP (tIdx c)) (auxP 17))
    (fun _ => auxP 6)

theorem cmpSlots_val (j : Fin (9+1)) :
    (cmpSlots j).val = ![128, 129, 130, 131, 140, 141, 142, 143, 145, 134] j := by
  fin_cases j <;> rfl

theorem cmpSlots_injective : Function.Injective cmpSlots := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [cmpSlots_val, cmpSlots_val] at hv
  fin_cases a <;> fin_cases b <;> simp at hv ⊢

def cmpStage := RecoveryFocus.machine cmpSlots
  (MaskedReset.machine cmpLocal (fun j => decide (j = (0 : Fin 1).natAdd 8)))

theorem cmp_stage (w cap : Nat) (S T : Fin 4 → Nat)
    (hcap : (2*w+1)+1+((2*w+1)+1+((2*w+1)+1+(2*w+1))) ≤ cap) (H : Fin 254 → ℕ) (A : Fin 254 → List Bool)
    (hHc : ∀ c, H (auxP (cIdx c)) = 0) (hHt : ∀ c, H (auxP (tIdx c)) = 0) (hH17 : H (auxP 17) = 0)
    (hH6 : H (auxP 6) = 0) (hAc : ∀ c, A (auxP (cIdx c)) = frame (binary w (S c)))
    (hAt : ∀ c, A (auxP (tIdx c)) = frame (binary w (T c))) (hA17 : A (auxP 17) = [])
    (hA6 : A (auxP 6) = List.replicate cap false) :
    ∃ H', Step cmpStage (2*((2*w+1)+1+((2*w+1)+1+((2*w+1)+1+(2*w+1))))+2) H A H'
        (Function.update A (auxP 17) (bitsOf w S T)) ∧
      H' (auxP 17) = 0 ∧ H' (auxP 6) = 0 ∧ ∀ p, (∀ j, cmpSlots j ≠ p) → H' p = H p := by
  have h := focus_at (cmp_phase_masked w cap S T hcap) cmpSlots cmpSlots_injective H A
    (by
      intro j
      refine Fin.addCases (m:=9) (n:=1) (fun y => ?_) (fun k => ?_) j
      · simp only [cmpSlots, Fin.addCases_left]
        refine cover9 (motive := fun y => H (loc9 (fun c => auxP (cIdx c)) (fun c => auxP (tIdx c))
          (auxP 17) y) = loc9 (fun _ => 0) (fun _ => 0) 0 y) (fun k => ?_) (fun k => ?_) ?_ y
        · rw [loc9_cnt, loc9_cnt]; exact hHc k
        · rw [loc9_tgt, loc9_tgt]; exact hHt k
        · rw [loc9_bits, loc9_bits]; exact hH17
      · simp only [cmpSlots, Fin.addCases_right]; exact hH6)
    (by
      intro j
      refine Fin.addCases (m:=9) (n:=1) (fun y => ?_) (fun k => ?_) j
      · simp only [cmpSlots, Fin.addCases_left]
        refine cover9 (motive := fun y => A (loc9 (fun c => auxP (cIdx c)) (fun c => auxP (tIdx c))
          (auxP 17) y) = loc9 (fun c => frame (binary w (S c))) (fun c => frame (binary w (T c))) [] y)
          (fun k => ?_) (fun k => ?_) ?_ y
        · rw [loc9_cnt, loc9_cnt]; exact hAc k
        · rw [loc9_tgt, loc9_tgt]; exact hAt k
        · rw [loc9_bits, loc9_bits]; exact hA17
      · simp only [cmpSlots, Fin.addCases_right]; exact hA6)
  have ebits : auxP 17 = cmpSlots (((0 : Fin 1).natAdd 8).castAdd 1) := by
    simp only [cmpSlots, Fin.addCases_left, loc9_bits]
  have elog : auxP 6 = cmpSlots ((0 : Fin 1).natAdd 9) := by
    simp only [cmpSlots, Fin.addCases_right]
  refine ⟨_, h.congr rfl ?_, ?_, ?_, ?_⟩
  · rw [install_update cmpSlots cmpSlots_injective A _ (((0 : Fin 1).natAdd 8).castAdd 1), ← ebits]
    · simp only [Fin.addCases_left, loc9_bits]
    · intro j hj
      refine Fin.addCases (m:=9) (n:=1) (motive := fun j => j ≠ (((0 : Fin 1).natAdd 8).castAdd 1) →
        Fin.addCases (loc9 (fun c => frame (binary w (S c))) (fun c => frame (binary w (T c)))
          (bitsOf w S T)) (fun _ : Fin 1 => List.replicate cap false) j = A (cmpSlots j))
        (fun y hy => ?_) (fun k _ => ?_) j hj
      · simp only [cmpSlots, Fin.addCases_left]
        refine cover9 (motive := fun y => Fin.castAdd 1 y ≠ (((0 : Fin 1).natAdd 8).castAdd 1) →
          loc9 (fun c => frame (binary w (S c))) (fun c => frame (binary w (T c))) (bitsOf w S T) y =
          A (loc9 (fun c => auxP (cIdx c)) (fun c => auxP (tIdx c)) (auxP 17) y))
          (fun k _ => ?_) (fun k _ => ?_) (fun hb => absurd rfl hb) y hy
        · rw [loc9_cnt, loc9_cnt]; exact (hAc k).symm
        · rw [loc9_tgt, loc9_tgt]; exact (hAt k).symm
      · simp only [cmpSlots, Fin.addCases_right]; exact hA6.symm
  · rw [ebits, dockH_slot _ cmpSlots_injective, Fin.addCases_left, loc9_bits]
  · rw [elog, dockH_slot _ cmpSlots_injective]
    simp only [Fin.addCases_right]
  · intro p hp
    exact dockH_other _ _ _ _ hp

/-! ## 9. The SYM verdict machine and its run -/

def auxIn (w Dc cap : Nat) (N T : Fin 4 → Nat) : Fin 18 → List Bool :=
  ![frame (binary w 0), frame (binary w 0), frame (binary w 0), frame (binary w 0), frame (binary w 0),
    List.replicate Dc false, List.replicate cap false,
    CompareMachine.word (N 0), CompareMachine.word (N 1), CompareMachine.word (N 2), CompareMachine.word (N 3),
    CompareMachine.word 4,
    frame (binary w (T 0)), frame (binary w (T 1)), frame (binary w (T 2)), frame (binary w (T 3)),
    frame (binary w 4), []]

def auxHeads0 : Fin 18 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0]

def countStage (c : Fin 4) := RecoveryFocus.machine
  (slots5 (auxP (cIdx c)) (auxP 5) (flagP 107) (auxP (dIdx c)) (auxP 6))
  (MaskedReset.machine PCJ45bee56da9f34d5a_CountFlags.machine (fun i => decide (i = 2)))
def andStage := RecoveryFocus.machine (slots5 (auxP 4) (auxP 5) (auxP 17) (auxP 11) (auxP 6))
  (MaskedReset.machine PCJ45bee56da9f34d5a_CountFlags.machine (fun i => decide (i = 2)))
def finStage := RecoveryFocus.machine (slots4 (auxP 4) (auxP 16) outP (auxP 6))
  (MaskedReset.machine C10CellComparator.machine (fun i => decide (i = 2)))

/-- **The fixed SYM verdict machine** (254 tapes; chosen before any request). -/
def machine := Composition.machine flagStage (Composition.machine (countStage 0)
  (Composition.machine (countStage 1) (Composition.machine (countStage 2)
  (Composition.machine (countStage 3) (Composition.machine cmpStage
  (Composition.machine andStage finStage))))))

/-- Resident drivers and targets (cell-free: they depend only on the request and the row's offsets). -/
def N (c : Fin 4) : Nat := SymMeaning.driverLen r c.val
def Tg (offset : Fin r.circuits.length → Nat) (c : Fin 4) : Nat := SymMeaning.targetCount r offset c.val

def input (I : Finset (Fin r.q)) (x : BitInput r.q) (L target T w Dc cap : Nat)
    (offset : Fin r.circuits.length → Nat) : Fin 254 → List Bool :=
  symLayout (PCJ45bee56da9f34d5a_NativeFamilyCount.bank I x T 0 (src r L target) []
      (List.replicate (PCJ45bee56da9f34d5a_UniformMinimumBounds.U T r.q (T+1)) false))
    (auxIn w Dc cap (N r) (Tg r offset)) [] []

def heads0 : Fin 254 → ℕ := symLayout (PCJ45bee56da9f34d5a_NativeFamilyCount.heads 0 [] 0 0) auxHeads0 0 0

def cmpCost (w : Nat) : Nat := 2*((2*w+1)+1+((2*w+1)+1+((2*w+1)+1+(2*w+1))))+2

def cost (L target T w : Nat) : Nat :=
  (2*PCJ45bee56da9f34d5a_NativeFamilyFlags.budget 0 r.q L target (SymMeaning.circuits r).length T+2)+1+
  ((2*PCJ45bee56da9f34d5a_CountFlags.budget (N r 0) w+2)+1+
  ((2*PCJ45bee56da9f34d5a_CountFlags.budget (N r 1) w+2)+1+
  ((2*PCJ45bee56da9f34d5a_CountFlags.budget (N r 2) w+2)+1+
  ((2*PCJ45bee56da9f34d5a_CountFlags.budget (N r 3) w+2)+1+
  (cmpCost w+1+((2*PCJ45bee56da9f34d5a_CountFlags.budget 4 w+2)+1+(2*(2*w+1)+2)))))))

/-- **C3(c): the SYM cell verdict.** From the cell's input bank (the native SYM family at mode tag 0,
the cell's assignment `x`, resident cumulative drivers/targets), the fixed machine reaches SOME bank
whose port 253 holds exactly the SYM row selector at `x`, head 0 — the per-cell verdict slot. -/
theorem run (four : r.circuits.length ≤ 4) (I : Finset (Fin r.q)) (x : BitInput r.q)
    (L target T w Dc cap : Nat) (offset : Fin r.circuits.length → Nat)
    (hb : (src r L target).length ≤ T) (hw4 : 4 < 2^w) (hN : ∀ c : Fin 4, N r c < 2^w)
    (hT : ∀ c : Fin 4, Tg r offset c < 2^w) (hD : 2*w+1 ≤ Dc)
    (hcap1 : PCJ45bee56da9f34d5a_NativeFamilyFlags.budget 0 r.q L target (SymMeaning.circuits r).length T ≤ cap)
    (hcapN : ∀ c : Fin 4, PCJ45bee56da9f34d5a_CountFlags.budget (N r c) w ≤ cap)
    (hcap3 : (2*w+1)+1+((2*w+1)+1+((2*w+1)+1+(2*w+1))) ≤ cap)
    (hcap4 : PCJ45bee56da9f34d5a_CountFlags.budget 4 w ≤ cap) :
    ∃ J B, Step machine (cost r L target T w) heads0 (input r I x L target T w Dc cap offset) J B ∧
      J outP = 0 ∧
      readTapeBit (B outP) 0 = decide (PCJ9eff70d512234a4c_Fixed.LiveRows.symOffsets r I x = offset) := by
  set W := PCJ45bee56da9f34d5a_NativeFlags.word (SymMeaning.circuits r) I x with hWdef
  have hWlen : ∀ c : Fin 4, N r c ≤ W.length := by
    intro c
    have h := SymMeaning.driverLen_le r I x c.val
    rw [SymMeaning.flagged, List.flatMap_map] at h
    rw [hWdef, SymMeaning.word_eq]
    exact h
  -- stage 1: flags
  obtain ⟨H1, A1, s1, a107, h107, h6, a6, hoth⟩ := flag_stage r I x T L target cap hb hcap1
    heads0 (input r I x L target T w Dc cap offset)
    (fun i => by rw [heads0, layout_flag]) (by rw [heads0, layout_aux]; rfl)
    (fun i => by rw [input, layout_flag]) (by rw [input, layout_aux]; rfl)
  have hA1 : ∀ k : Fin 18, k ≠ 6 → A1 (auxP k) = auxIn w Dc cap (N r) (Tg r offset) k := by
    intro k hk
    rw [(hoth _ (not_flag_aux k hk)).2, input, layout_aux]
  have hH1 : ∀ k : Fin 18, k ≠ 6 → H1 (auxP k) = auxHeads0 k := by
    intro k hk
    rw [(hoth _ (not_flag_aux k hk)).1, heads0, layout_aux]
  have hAo : A1 outP = [] := by rw [(hoth _ not_flag_out).2, input, layout_out]
  have hHo : H1 outP = 0 := by rw [(hoth _ not_flag_out).1, heads0, layout_out]
  let S : Fin 4 → Nat := fun c => (W.take (N r c)).count true
  -- stages 2-5: the four prefix counts
  have s20 := count_at (auxP (cIdx 0)) (auxP 5) (flagP 107) (auxP (dIdx 0)) (auxP 6)
    (slots5_injective _ _ _ _ _ (by decide)) W (N r 0) w Dc cap (hWlen 0) (hN 0) hD (hcapN 0) H1 A1
    (by rw [hH1 _ (by decide)]; rfl) (by rw [hH1 _ (by decide)]; rfl) h107 (by rw [hH1 _ (by decide)]; rfl) h6
    (by rw [hA1 _ (by decide)]; rfl) (by rw [hA1 _ (by decide)]; rfl) a107 (by rw [hA1 _ (by decide)]; rfl) a6
  have s21 := count_at (auxP (cIdx 1)) (auxP 5) (flagP 107) (auxP (dIdx 1)) (auxP 6)
    (slots5_injective _ _ _ _ _ (by decide)) W (N r 1) w Dc cap (hWlen 1) (hN 1) hD (hcapN 1) H1
    (Function.update A1 (auxP (cIdx 0)) (frame (binary w (S 0))))
    (by rw [hH1 _ (by decide)]; rfl) (by rw [hH1 _ (by decide)]; rfl) h107 (by rw [hH1 _ (by decide)]; rfl) h6
    (by rw [Function.update_of_ne (by decide), hA1 _ (by decide)]; rfl)
    (by rw [Function.update_of_ne (by decide), hA1 _ (by decide)]; rfl)
    (by rw [Function.update_of_ne (by decide), a107])
    (by rw [Function.update_of_ne (by decide), hA1 _ (by decide)]; rfl)
    (by rw [Function.update_of_ne (by decide), a6])
  have s22 := count_at (auxP (cIdx 2)) (auxP 5) (flagP 107) (auxP (dIdx 2)) (auxP 6)
    (slots5_injective _ _ _ _ _ (by decide)) W (N r 2) w Dc cap (hWlen 2) (hN 2) hD (hcapN 2) H1
    (Function.update (Function.update A1 (auxP (cIdx 0)) (frame (binary w (S 0)))) (auxP (cIdx 1))
      (frame (binary w (S 1))))
    (by rw [hH1 _ (by decide)]; rfl) (by rw [hH1 _ (by decide)]; rfl) h107 (by rw [hH1 _ (by decide)]; rfl) h6
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hA1 _ (by decide)]; rfl)
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hA1 _ (by decide)]; rfl)
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), a107])
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hA1 _ (by decide)]; rfl)
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), a6])
  have s23 := count_at (auxP (cIdx 3)) (auxP 5) (flagP 107) (auxP (dIdx 3)) (auxP 6)
    (slots5_injective _ _ _ _ _ (by decide)) W (N r 3) w Dc cap (hWlen 3) (hN 3) hD (hcapN 3) H1
    (Function.update (Function.update (Function.update A1 (auxP (cIdx 0)) (frame (binary w (S 0))))
      (auxP (cIdx 1)) (frame (binary w (S 1)))) (auxP (cIdx 2)) (frame (binary w (S 2))))
    (by rw [hH1 _ (by decide)]; rfl) (by rw [hH1 _ (by decide)]; rfl) h107 (by rw [hH1 _ (by decide)]; rfl) h6
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), hA1 _ (by decide)]; rfl)
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), hA1 _ (by decide)]; rfl)
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), a107])
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), hA1 _ (by decide)]; rfl)
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), a6])
  let A5 := Function.update (Function.update (Function.update (Function.update A1 (auxP (cIdx 0))
    (frame (binary w (S 0)))) (auxP (cIdx 1)) (frame (binary w (S 1)))) (auxP (cIdx 2))
    (frame (binary w (S 2)))) (auxP (cIdx 3)) (frame (binary w (S 3)))
  have hA5c : ∀ c : Fin 4, A5 (auxP (cIdx c)) = frame (binary w (S c)) := by
    intro c
    fin_cases c
    · show A5 (auxP (cIdx 0)) = _
      simp only [A5]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_self]
      rfl
    · show A5 (auxP (cIdx 1)) = _
      simp only [A5]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]
      rfl
    · show A5 (auxP (cIdx 2)) = _
      simp only [A5]
      rw [Function.update_of_ne (by decide), Function.update_self]
      rfl
    · show A5 (auxP (cIdx 3)) = _
      simp only [A5]
      rw [Function.update_self]
      rfl
  have hA5 : ∀ k : Fin 18, 4 ≤ k.val → k ≠ 6 → A5 (auxP k) = auxIn w Dc cap (N r) (Tg r offset) k := by
    intro k hk hk6
    have hne : ∀ c : Fin 4, auxP k ≠ auxP (cIdx c) := by
      intro c he
      have hv := congrArg Fin.val he
      rw [auxP_val, auxP_val] at hv
      have : (cIdx c).val = c.val := rfl
      have := c.isLt
      omega
    simp only [A5]
    rw [Function.update_of_ne (hne 3), Function.update_of_ne (hne 2), Function.update_of_ne (hne 1),
      Function.update_of_ne (hne 0), hA1 k hk6]
  have hA56 : A5 (auxP 6) = List.replicate cap false := by
    have hne : ∀ c : Fin 4, auxP 6 ≠ auxP (cIdx c) := by
      intro c he
      have hv := congrArg Fin.val he
      rw [auxP_val, auxP_val] at hv
      have : (cIdx c).val = c.val := rfl
      have := c.isLt
      omega
    simp only [A5]
    rw [Function.update_of_ne (hne 3), Function.update_of_ne (hne 2), Function.update_of_ne (hne 1),
      Function.update_of_ne (hne 0), a6]
  have hA5o : A5 outP = [] := by
    have hne : ∀ c : Fin 4, outP ≠ auxP (cIdx c) := by
      intro c he
      have hv := congrArg Fin.val he
      rw [outP_val, auxP_val] at hv
      have : (cIdx c).val = c.val := rfl
      have := c.isLt
      omega
    simp only [A5]
    rw [Function.update_of_ne (hne 3), Function.update_of_ne (hne 2), Function.update_of_ne (hne 1),
      Function.update_of_ne (hne 0), hAo]
  -- stage 6: compare each count with its target
  obtain ⟨H6, s3, h617, h66, h6oth⟩ := cmp_stage w cap S (Tg r offset) hcap3 H1 A5
    (fun c => by fin_cases c <;> (rw [hH1 _ (by decide)]; rfl))
    (fun c => by fin_cases c <;> (rw [hH1 _ (by decide)]; rfl))
    (by rw [hH1 _ (by decide)]; rfl) h6 hA5c
    (fun c => by fin_cases c <;> (rw [hA5 _ (by decide) (by decide)]; rfl))
    (by rw [hA5 _ (by decide) (by decide)]; rfl) hA56
  have notcmp : ∀ k : Fin 18, (k.val = 4 ∨ k.val = 5 ∨ k.val = 11 ∨ k.val = 16) → ∀ j, cmpSlots j ≠ auxP k := by
    intro k hk j he
    have hv := congrArg Fin.val he
    rw [cmpSlots_val, auxP_val] at hv
    fin_cases j <;> simp at hv <;> omega
  have notcmpo : ∀ j, cmpSlots j ≠ outP := by
    intro j he
    have hv := congrArg Fin.val he
    rw [cmpSlots_val, outP_val] at hv
    fin_cases j <;> simp at hv
  let A6 := Function.update A5 (auxP 17) (bitsOf w S (Tg r offset))
  have hbits_len : (bitsOf w S (Tg r offset)).length = 4 := rfl
  -- stage 7: count the agreeing slots
  have s4 := count_at (auxP 4) (auxP 5) (auxP 17) (auxP 11) (auxP 6)
    (slots5_injective _ _ _ _ _ (by decide)) (bitsOf w S (Tg r offset)) 4 w Dc cap (by rw [hbits_len])
    hw4 hD hcap4 H6 A6
    (by rw [h6oth _ (notcmp 4 (by decide)), hH1 _ (by decide)]; rfl)
    (by rw [h6oth _ (notcmp 5 (by decide)), hH1 _ (by decide)]; rfl) h617
    (by rw [h6oth _ (notcmp 11 (by decide)), hH1 _ (by decide)]; rfl) h66
    (by simp only [A6]; rw [Function.update_of_ne (by decide), hA5 _ (by decide) (by decide)]; rfl)
    (by simp only [A6]; rw [Function.update_of_ne (by decide), hA5 _ (by decide) (by decide)]; rfl)
    (by simp only [A6]; rw [Function.update_self])
    (by simp only [A6]; rw [Function.update_of_ne (by decide), hA5 _ (by decide) (by decide)]; rfl)
    (by simp only [A6]; rw [Function.update_of_ne (by decide), hA56])
  let k := ((bitsOf w S (Tg r offset)).take 4).count true
  let A7 := Function.update A6 (auxP 4) (frame (binary w k))
  -- stage 8: compare that count with 4
  obtain ⟨H8, s5, h8o⟩ := cmp_at (auxP 4) (auxP 16) outP (auxP 6)
    (slots4_injective _ _ _ _ (by decide)) (binary w k) (binary w 4) cap
    (by rw [binary_length, binary_length]) (by rw [binary_length]; omega) H6 A7
    (by rw [h6oth _ (notcmp 4 (by decide)), hH1 _ (by decide)]; rfl)
    (by rw [h6oth _ (notcmp 16 (by decide)), hH1 _ (by decide)]; rfl)
    (by rw [h6oth _ notcmpo, hHo]) h66
    (by simp only [A7]; rw [Function.update_self])
    (by simp only [A7, A6]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      hA5 _ (by decide) (by decide)]; rfl)
    (by simp only [A7, A6]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hA5o])
    (by simp only [A7, A6]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hA56])
  have all := s1.seq (s20.seq (s21.seq (s22.seq (s23.seq (s3.seq (s4.seq s5))))))
  refine ⟨H8, Function.update A7 outP [decide (binary w k = binary w 4)], ?_, h8o, ?_⟩
  · rw [binary_length] at all
    exact all
  · rw [Function.update_self]
    show decide (binary w k = binary w 4) = _
    exact bit_eq r four I x offset w hw4 hN hT

end
end RowsConstruction.SymVerdict
