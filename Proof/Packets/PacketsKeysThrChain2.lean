import Proof.Packets.PacketsKeysThrPass2

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.PacketsKeys.ThrProg
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.PacketsMeta NearCubicWires.PacketsKeys.RM
open NearCubicWires.RepairRepresentation NearCubicWires.PacketsSymBits
noncomputable section

def p2Block (c : Fin 4) := Ite (mPeek (NR := 24) (NO := 29) (ocs c)) (p2Body c) nopT FL

/-- Dropping circuit `c`'s tapes. -/
theorem dropC {W : ℕ} (z : TZ) (c : Fin 4) :
    ∀ i H A, TR W (roles (toSt z) i) H A →
      TR W (roles (toSt { z with cc := Function.update (Function.update z.cc (cs c) .any) (cm c) .any }) i) H A := by
  intro i H A h
  have e : roles (toSt { z with cc := Function.update (Function.update z.cc (cs c) .any) (cm c) .any }) =
      Function.update (Function.update (roles (toSt z)) (os (ocs c)) .any) (os (ocm c)) .any := by
    rw [upd_os, upd_os]
    show roles (toSt { z with cc := _ }) = roles ⟨z.rl, z.fl, rgv z, Function.update (Function.update (otv z) (ocs c) .any)
      (ocm c) .any⟩
    rw [oset2]
    rfl
  rw [e]
  simp only [Function.update_apply]
  split_ifs
  · trivial
  · trivial
  · exact h

theorem peekC {W : ℕ} (z : TZ) (c : Fin 4) (f : ℕ → Bool) (p : ℕ) (h : z.cc (cs c) = .cells f p) :
    LRuns W (mPeek (NR := 24) (NO := 29) (ocs c)) 1 (roles (toSt z)) (roles (toSt { z with fl := f p })) :=
  (peek_run (W := W) (toSt z) (ocs c) f p (by show otv z (ocs c) = _; rw [get_cs, h])).congr_out
    (fixR (z' := { z with fl := f p }) rfl rfl rfl rfl)

theorem natWord_head (x : ℕ) (post : List Bool) : sf (natWord x ++ post) 1 = true := by
  rw [sf_succ]
  unfold natWord NearCubicWires.WilliamsPublishedForm.framedNatBits
  have h : 1 ≤ natBitLength x := by unfold natBitLength; omega
  obtain ⟨m, hm⟩ : ∃ m, natBitLength x = m + 1 := ⟨natBitLength x - 1, by omega⟩
  rw [hm, List.replicate_succ]
  rfl

section Chain2
variable {α : Type} (ar : α → ℕ) (ch : (x : α) → List (ExactThresholdGate (ar x)))

/-- The bits pass 2 emits for circuit `c` (none past the circuit list). -/
def bitsAt (L : List α) (S : Fin 4 → ℕ) (B P j : ℕ) (c : ℕ) : List Bool :=
  if h : c < L.length ∧ c < 4 then
    (if h2 : S ⟨c, h.2⟩ < (ch L[c]).length then
      (List.ofFn ((ch L[c])[S ⟨c, h.2⟩]).weight).map (wb (B ^ c % P) P j) else [])
  else []

def outK (L : List α) (S : Fin 4 → ℕ) (B P j k : ℕ) : List Bool := ((List.range k).map (bitsAt ar ch L S B P j)).flatten

/-- The circuit tapes during pass 2: the first `k` present circuits dropped. -/
def ccR (L : List α) (base : Fin 8 → TS) (k : ℕ) : Fin 8 → TS := fun e =>
  if e.val / 2 < k ∧ e.val / 2 < L.length then .any else ccP (L.map (payOf ar ch)) base e

/-- The state between pass-2 blocks. -/
def st2 (z1 : TZ) (L : List α) (base : Fin 8 → TS) (B j k : ℕ) : TZ :=
  p2S z1 (ccR ar ch L base k) 0 0 0 0 (B ^ (min k L.length) % z1.P) 0 0 0 0 0 0 0 (outK ar ch L z1.S B z1.P j k) false

theorem ccR_cs (L : List α) (base : Fin 8 → TS) (c : Fin 4) (hc : c.val < L.length) :
    ccR ar ch L base c.val (cs c) = .cells (sf (payOf ar ch L[c.val])) 1 := by
  unfold ccR ccP
  have h2 : (cs c).val / 2 = c.val := by simp [cs]
  rw [if_neg (by rw [h2]; omega), dif_pos (by simp; omega), if_pos (by simp [cs])]
  simp [h2]

theorem ccR_cm (L : List α) (base : Fin 8 → TS) (c : Fin 4) (hc : c.val < L.length) :
    ccR ar ch L base c.val (cm c) = .cells (mks (payOf ar ch L[c.val])) 1 := by
  unfold ccR ccP
  have h2 : (cm c).val / 2 = c.val := by simp [cm]; omega
  rw [if_neg (by rw [h2]; omega), dif_pos (by simp; omega), if_neg (by simp [cm])]
  simp [h2]

theorem ccR_cs_out (L : List α) (base : Fin 8 → TS) (c : Fin 4) (hc : L.length ≤ c.val) :
    ccR ar ch L base c.val (cs c) = base (cs c) := by
  unfold ccR ccP
  have h2 : (cs c).val / 2 = c.val := by simp [cs]
  rw [if_neg (by rw [h2]; omega), dif_neg (by simp; omega)]

theorem ccR_succ (L : List α) (base : Fin 8 → TS) (c : Fin 4) (hc : c.val < L.length) (t : Fin 8 → TS)
    (ht : ∀ e, e ≠ cs c → e ≠ cm c → t e = ccR ar ch L base c.val e) :
    Function.update (Function.update t (cs c) .any) (cm c) .any = ccR ar ch L base (c.val + 1) := by
  funext e
  simp only [Function.update_apply]
  split_ifs with h1 h2
  · subst h1; unfold ccR; rw [if_pos (by simp [cm]; omega)]
  · subst h2; unfold ccR; rw [if_pos (by simp [cs]; omega)]
  · rw [ht e h2 h1]
    unfold ccR
    have hne : e.val / 2 ≠ c.val := by
      intro hh
      rcases Nat.even_or_odd e.val with ⟨m, hm⟩ | ⟨m, hm⟩
      · exact h2 (Fin.ext (by simp [cs]; omega))
      · exact h1 (Fin.ext (by simp [cm]; omega))
    by_cases hk : e.val / 2 < c.val ∧ e.val / 2 < L.length
    · rw [if_pos hk, if_pos ⟨by omega, hk.2⟩]
    · rw [if_neg hk]
      by_cases hk2 : e.val / 2 < c.val + 1 ∧ e.val / 2 < L.length
      · exfalso; exact hk ⟨by omega, hk2.2⟩
      · rw [if_neg hk2]

theorem ccR_stable (L : List α) (base : Fin 8 → TS) (k : ℕ) (hk : L.length ≤ k) :
    ccR ar ch L base (k + 1) = ccR ar ch L base k := by
  funext e
  unfold ccR
  by_cases h : e.val / 2 < L.length
  · rw [if_pos ⟨by omega, h⟩, if_pos ⟨by omega, h⟩]
  · rw [if_neg (fun hh => h hh.2), if_neg (fun hh => h hh.2)]

theorem outK_succ (L : List α) (S : Fin 4 → ℕ) (B P j k : ℕ) :
    outK ar ch L S B P j (k + 1) = outK ar ch L S B P j k ++ bitsAt ar ch L S B P j k := by
  unfold outK
  rw [List.range_succ, List.map_append, List.map_singleton, List.flatten_append, List.flatten_singleton]

def p2BlockCost (W P : ℕ) : ℕ := 1 + p2BodyCost W W W P + 0 + 2

theorem p2BodyCost_mono (W A s P : ℕ) (hA : A ≤ W) (hs : s ≤ W) : p2BodyCost W A s P ≤ p2BodyCost W W W P := by
  unfold p2BodyCost seekCost skipAllCost skipAllBodyCost
  have h1 : (s + 1) * (2 * W + 3 + (2 * W + 3 + 1 + (2 * W + 3 + 1 + ((A + 1 + 1) * (2 * W + 3 + skipBodyCost W + 2) + 1
      + (2 * W + 3)))) + 2) ≤ (W + 1) * (2 * W + 3 + (2 * W + 3 + 1 + (2 * W + 3 + 1 + ((W + 1 + 1) *
      (2 * W + 3 + skipBodyCost W + 2) + 1 + (2 * W + 3)))) + 2) := by gcongr
  have h2 : (A + 1) * (2 * W + 3 + wBodyCost W P + 2) ≤ (W + 1) * (2 * W + 3 + wBodyCost W P + 2) := by gcongr
  omega

section Block2
variable {W : ℕ} (z1 : TZ) (hr : z1.rl = .ruler) (L : List α) (base : Fin 8 → TS)
  (hbase : ∀ e, base e = .cells blank 0) (B j : ℕ)
  (hsel : ∀ (i : Fin 4) (hi : i.val < L.length), z1.S i < (ch L[i.val]).length)
  (hW : ∀ x ∈ L, (payOf ar ch x).length ≤ W) (hAW : ∀ x ∈ L, ar x + 2 < 2 ^ W)
  (hgW : ∀ x ∈ L, (ch x).length < 2 ^ W)
  (hE : z1.E = 2 ^ (j + 1)) (hE2m : z1.E2m = 2 ^ (j + 1) - 1) (hEm : z1.Em = 2 ^ j - 1)
  (hP : 0 < z1.P) (hP2 : 2 * z1.P ≤ 2 ^ W) (hPP : z1.P * z1.P < 2 ^ W) (hBm : z1.Bm = B % z1.P)
  (hEW : 2 ^ (j + 1) < 2 ^ W) (hW1 : 1 ≤ W)
include hr hbase hsel hW hAW hgW hE hE2m hEm hP hP2 hPP hBm hEW hW1

theorem p2Block_run (c : Fin 4) :
    LRuns W (p2Block c) (p2BlockCost W z1.P) (roles (toSt (st2 ar ch z1 L base B j c.val)))
      (roles (toSt (st2 ar ch z1 L base B j (c.val + 1)))) := by
  by_cases hc : c.val < L.length
  · have hmem : L[c.val] ∈ L := List.getElem_mem hc
    have hpk := peekC (W := W) (st2 ar ch z1 L base B j c.val) c (sf (payOf ar ch L[c.val])) 1
      (ccR_cs ar ch L base c hc)
    have hhd : sf (payOf ar ch L[c.val]) 1 = true := by
      unfold payOf; rw [List.append_assoc]; exact natWord_head _ _
    rw [hhd] at hpk
    have hFl : (st2 ar ch z1 L base B j c.val).F < z1.P := Nat.mod_lt _ hP
    have hbody := p2Body_run (W := W) (st2 ar ch z1 L base B j c.val) hr c (payOf ar ch L[c.val]) (ch L[c.val])
      (outK ar ch L z1.S B z1.P j c.val) j rfl (ccR_cs ar ch L base c hc) (ccR_cm ar ch L base c hc) (hsel c hc)
      (hW _ hmem) (hAW _ hmem) (hgW _ hmem) hE hE2m hEm hP hP2 hPP hFl
      (by show z1.Bm < z1.P; rw [hBm]; exact Nat.mod_lt _ hP) hEW hW1
    have hbody' := hbody.weaken (dropC _ c)
    have hA : ar L[c.val] ≤ W := le_trans (ar_le_pay ar ch _ (List.ne_nil_of_length_pos (by
      have := hsel c hc; omega))) (hW _ hmem)
    have hS : z1.S c ≤ W :=
      le_trans (le_trans (hsel c hc).le (ch_le_pay ar ch _)) (hW _ hmem)
    have hcost := p2BodyCost_mono W (ar L[c.val]) (z1.S c) z1.P hA hS
    have hmin : min c.val L.length = c.val := by omega
    have hmin1 : min (c.val + 1) L.length = c.val + 1 := by omega
    have hF1 : B ^ (min c.val L.length) % z1.P * z1.Bm % z1.P = B ^ (min (c.val + 1) L.length) % z1.P := by
      rw [hmin, hmin1, hBm, pow_succ, Nat.mul_mod, Nat.mod_mod, Nat.mod_mod, ← Nat.mul_mod]
    have hbits : bitsAt ar ch L z1.S B z1.P j c.val = (List.ofFn ((ch L[c.val])[z1.S c]'(hsel c hc)).weight).map
        (wb (B ^ (min c.val L.length) % z1.P) z1.P j) := by
      unfold bitsAt
      rw [dif_pos ⟨hc, c.isLt⟩, dif_pos (hsel c hc), hmin]
    have hfin : roles (toSt { p2S (st2 ar ch z1 L base B j c.val)
        (strm (ccR ar ch L base c.val) c (payOf ar ch L[c.val])
          ((natWord (ar L[c.val]) ++ natWord (ch L[c.val]).length ++
            ((ch L[c.val]).take (z1.S c)).flatMap exactWord).length + 1 +
            ((List.ofFn ((ch L[c.val])[z1.S c]'(hsel c hc)).weight).flatMap intWord).length)) 0 (z1.S c - z1.S c) 0 0
        (B ^ (min c.val L.length) % z1.P * z1.Bm % z1.P) 0 0 0 0 0 0 0
        (outK ar ch L z1.S B z1.P j c.val ++ (List.ofFn ((ch L[c.val])[z1.S c]'(hsel c hc)).weight).map
          (wb (B ^ (min c.val L.length) % z1.P) z1.P j)) false with
        cc := Function.update (Function.update (strm (ccR ar ch L base c.val) c (payOf ar ch L[c.val])
          ((natWord (ar L[c.val]) ++ natWord (ch L[c.val]).length ++
            ((ch L[c.val]).take (z1.S c)).flatMap exactWord).length + 1 +
            ((List.ofFn ((ch L[c.val])[z1.S c]'(hsel c hc)).weight).flatMap intWord).length)) (cs c) .any) (cm c) .any }) =
        roles (toSt (st2 ar ch z1 L base B j (c.val + 1))) := by
      rw [ccR_succ ar ch L base c hc _ (by
        intro e h1 h2
        unfold strm
        rw [Function.update_of_ne h2, Function.update_of_ne h1]), Nat.sub_self, hF1, ← hbits,
        ← outK_succ ar ch L z1.S B z1.P j c.val]
      rfl
    refine (Ite.runs (W := W) (nq := 0) (mPeek (NR := 24) (NO := 29) (ocs c)) (p2Body c) nopT FL true hpk rfl
      (fun _ => hbody'.congr_out hfin) (fun h => absurd h (by simp))).enlarge ?_
    show 1 + p2BodyCost W (ar L[c.val]) (z1.S c) z1.P + 0 + 2 ≤ p2BlockCost W z1.P
    unfold p2BlockCost
    omega
  · have hc' : L.length ≤ c.val := by omega
    have hpk := peekC (W := W) (st2 ar ch z1 L base B j c.val) c blank 0
      (by rw [show (st2 ar ch z1 L base B j c.val).cc = ccR ar ch L base c.val from rfl, ccR_cs_out ar ch L base c hc',
        hbase])
    have hsame : st2 ar ch z1 L base B j (c.val + 1) = st2 ar ch z1 L base B j c.val := by
      unfold st2
      rw [ccR_stable ar ch L base c.val hc', show min (c.val + 1) L.length = min c.val L.length by omega,
        outK_succ]
      have hb : bitsAt ar ch L z1.S B z1.P j c.val = [] := by
        unfold bitsAt; rw [dif_neg (by omega)]
      rw [hb, List.append_nil]
    have hn : LRuns W nopT 0 (roles (toSt { st2 ar ch z1 L base B j c.val with fl := blank 0 }))
        (roles (toSt (st2 ar ch z1 L base B j (c.val + 1)))) := by
      rw [hsame]; exact nop_lruns _
    exact Ite.runs (W := W) (np := p2BodyCost W W W z1.P) (nq := 0) (mPeek (NR := 24) (NO := 29) (ocs c)) (p2Body c)
      nopT FL false hpk rfl (fun h => absurd h (by simp)) (fun _ => hn)

end Block2

/-- **Pass 2**: the four blocks. -/
def p2Pass := Composition.machine (p2Block 0) (Composition.machine (p2Block 1) (Composition.machine (p2Block 2) (p2Block 3)))

def p2PassCost (W P : ℕ) : ℕ := p2BlockCost W P + 1 + (p2BlockCost W P + 1 + (p2BlockCost W P + 1 + p2BlockCost W P))

theorem p2Pass_run {W : ℕ} (z1 : TZ) (hr : z1.rl = .ruler) (L : List α) (base : Fin 8 → TS)
    (hbase : ∀ e, base e = .cells blank 0) (B j : ℕ)
    (hsel : ∀ (i : Fin 4) (hi : i.val < L.length), z1.S i < (ch L[i.val]).length)
    (hW : ∀ x ∈ L, (payOf ar ch x).length ≤ W) (hAW : ∀ x ∈ L, ar x + 2 < 2 ^ W)
    (hgW : ∀ x ∈ L, (ch x).length < 2 ^ W)
    (hE : z1.E = 2 ^ (j + 1)) (hE2m : z1.E2m = 2 ^ (j + 1) - 1) (hEm : z1.Em = 2 ^ j - 1)
    (hP : 0 < z1.P) (hP2 : 2 * z1.P ≤ 2 ^ W) (hPP : z1.P * z1.P < 2 ^ W) (hBm : z1.Bm = B % z1.P)
    (hEW : 2 ^ (j + 1) < 2 ^ W) (hW1 : 1 ≤ W) :
    LRuns W p2Pass (p2PassCost W z1.P) (roles (toSt (st2 ar ch z1 L base B j 0)))
      (roles (toSt (st2 ar ch z1 L base B j 4))) :=
  (p2Block_run ar ch z1 hr L base hbase B j hsel hW hAW hgW hE hE2m hEm hP hP2 hPP hBm hEW hW1 0).seq
    ((p2Block_run ar ch z1 hr L base hbase B j hsel hW hAW hgW hE hE2m hEm hP hP2 hPP hBm hEW hW1 1).seq
      ((p2Block_run ar ch z1 hr L base hbase B j hsel hW hAW hgW hE hE2m hEm hP hP2 hPP hBm hEW hW1 2).seq
        (p2Block_run ar ch z1 hr L base hbase B j hsel hW hAW hgW hE hE2m hEm hP hP2 hPP hBm hEW hW1 3)))

end Chain2

end
end NearCubicWires.PacketsKeys.ThrProg

