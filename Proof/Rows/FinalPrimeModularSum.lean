import Proof.Rows.FinalPrimeResidueWord

/-! # GAP 3: gated modular addition and modular accumulation

The threshold row of Appendix A.13 is
`(∑ i, weights i * bitInt (input i)) - target  (mod p)`.  Because `bitInt` of a
Boolean is `0` or `1`, the products are *gated* coefficients, not general
multiplications, so the row is a modular accumulation of coefficient residues
under a gate stream.

This file supplies that accumulation.  `machine : Machine 6 34` performs one
whole update

    res := (res + gate * x)  (mod p)

in a single left-to-right sweep of framed `L`-bit words, running the two carry
chains (`res + gate*x`, then `+ (2^L - p)`) simultaneously in its finite
control.  As in `FinalPrimeRow` the two candidates are written in place on `T`
and `U` and the decisive carry on the one-cell tape `F`, so the next sweep
consumes them directly and `FinalPrimeResidue` materialises the answer.

Tapes: `0 = T`, `1 = U`, `2 = P`, `3 = F` (one cell, head pinned at 0),
`4 = G` (the gate stream, one cell per sweep), `5 = X` (the summand stream,
one framed word per sweep).  Only `T`, `U`, `P` are reset between sweeps, so
the nesting is again exactly `pass -> MaskedReset -> RepeatMachine`: three
tape levels, no fourth.

Driving this machine with a gate stream that is constantly `true` and a
summand stream `x, x, ...` interleaved with `FinalPrimeRow.machine` sweeps on
an empty bit tape (which perform `res := 2*res mod p`) is the shift-add-reduce
modular multiplication; that schedule is a driver, not a new machine.
-/
namespace NearCubicWires.RepairOrdinary.FinalPrimeModular
open LocalBitMultitape RecoveryExecution RadixSemantics ExtDecompositionBatch
open RepairSource.VerifierDecoding RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## 1. Finite control -/

def markerState (sel gate c1 c2 : Bool) : Fin 34 :=
  if sel then
    (if gate then (if c1 then (if c2 then 17 else 16) else (if c2 then 15 else 14))
      else (if c1 then (if c2 then 13 else 12) else (if c2 then 11 else 10)))
  else
    (if gate then (if c1 then (if c2 then 9 else 8) else (if c2 then 7 else 6))
      else (if c1 then (if c2 then 5 else 4) else (if c2 then 3 else 2)))

def bitState (sel gate c1 c2 : Bool) : Fin 34 :=
  if sel then
    (if gate then (if c1 then (if c2 then 33 else 32) else (if c2 then 31 else 30))
      else (if c1 then (if c2 then 29 else 28) else (if c2 then 27 else 26)))
  else
    (if gate then (if c1 then (if c2 then 25 else 24) else (if c2 then 23 else 22))
      else (if c1 then (if c2 then 21 else 20) else (if c2 then 19 else 18)))

def selOf (q : Fin 34) : Bool := decide (8 ≤ (q.val - 2) % 16)
def gateOf (q : Fin 34) : Bool := decide (4 ≤ (q.val - 2) % 8)
def c1Of (q : Fin 34) : Bool := decide (2 ≤ (q.val - 2) % 4)
def c2Of (q : Fin 34) : Bool := decide ((q.val - 2) % 2 = 1)


def mv : Fin 6 → HeadMove := fun i => if i.val ≤ 2 then .right else if i.val = 5 then .right else .stay
def emv : Fin 6 → HeadMove := fun i => if i.val = 4 then .right else .stay

def machine : Machine 6 34 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q scanned =>
    if q.val = 0 then
      some ⟨markerState (scanned 3) (scanned 4) false true, fun _ => none, emv⟩
    else if q.val = 1 then none
    else if q.val < 18 then
      (if scanned 0 then some ⟨bitState (selOf q) (gateOf q) (c1Of q) (c2Of q), fun _ => none, mv⟩
        else some ⟨1, fun i => if i.val = 3 then some (c2Of q) else none, mv⟩)
    else
      some ⟨markerState (selOf q) (gateOf q)
          (Add.carry (if selOf q then scanned 1 else scanned 0) (gateOf q && scanned 5) (c1Of q))
          (Add.carry
            (Add.bit (if selOf q then scanned 1 else scanned 0) (gateOf q && scanned 5) (c1Of q))
            (!scanned 2) (c2Of q)),
        fun i =>
          if i.val = 0 then
            some (Add.bit (if selOf q then scanned 1 else scanned 0) (gateOf q && scanned 5) (c1Of q))
          else if i.val = 1 then
            some (Add.bit
              (Add.bit (if selOf q then scanned 1 else scanned 0) (gateOf q && scanned 5) (c1Of q))
              (!scanned 2) (c2Of q))
          else none,
        mv⟩

def cfg (q : Fin 34) (T U P F G X : List Bool) (pos gpos xpos : ℕ) : Configuration 6 34 :=
  ⟨q, ![pos, pos, pos, 0, gpos, xpos], ![T, U, P, F, G, X]⟩

theorem write_mid (pre tail : List Bool) (old v : Bool) :
    writeTapeBit (pre ++ old :: tail) pre.length v = pre ++ v :: tail := by
  induction pre with
  | nil => rfl
  | cons b pre ih => simpa [writeTapeBit] using congrArg (List.cons b) ih

/-! ## 2. The four local transitions -/

theorem entry_step (T U P F G X : List Bool) (gpos xpos : ℕ) (sel gate : Bool)
    (hF : readTapeBit F 0 = sel) (hG : readTapeBit G gpos = gate) :
    step machine (cfg 0 T U P F G X 0 gpos xpos) =
      some (cfg (markerState sel gate false true) T U P F G X 0 (gpos + 1) xpos) := by
  simp [step, machine, cfg, Configuration.scanned, hF, hG]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply, emv]
  · funext i; fin_cases i <;> simp [applyAction]

theorem marker_step (sel gate c1 c2 : Bool) (T U P F G X : List Bool) (pos gpos xpos : ℕ)
    (hT : readTapeBit T pos = true) :
    step machine (cfg (markerState sel gate c1 c2) T U P F G X pos gpos xpos) =
      some (cfg (bitState sel gate c1 c2) T U P F G X (pos + 1) gpos (xpos + 1)) := by
  cases sel <;> cases gate <;> cases c1 <;> cases c2 <;>
    simp [step, machine, cfg, Configuration.scanned, hT, markerState, bitState,
      selOf, gateOf, c1Of, c2Of] <;>
    apply configuration_ext
  all_goals first
    | rfl
    | (funext i; fin_cases i <;> simp [applyAction, HeadMove.apply, mv])

theorem halt_step (sel gate c1 c2 : Bool) (T U P F G X : List Bool) (pos gpos xpos : ℕ)
    (hT : readTapeBit T pos = false) :
    step machine (cfg (markerState sel gate c1 c2) T U P F G X pos gpos xpos) =
      some (cfg 1 T U P (writeTapeBit F 0 c2) G X (pos + 1) gpos (xpos + 1)) := by
  cases sel <;> cases gate <;> cases c1 <;> cases c2 <;>
    simp [step, machine, cfg, Configuration.scanned, hT, markerState,
      selOf, gateOf, c1Of, c2Of] <;>
    apply configuration_ext
  all_goals first
    | rfl
    | (funext i; fin_cases i <;> simp [applyAction, HeadMove.apply, mv])

theorem bit_step (sel gate c1 c2 t u pp x : Bool)
    (aT tT aU tU aP tP F G aX tX : List Bool) (gpos : ℕ)
    (hU : aU.length = aT.length)
    (hTr : readTapeBit (aT ++ t :: tT) aT.length = t)
    (hUr : readTapeBit (aU ++ u :: tU) aT.length = u)
    (hPr : readTapeBit (aP ++ pp :: tP) aT.length = pp)
    (hXr : readTapeBit (aX ++ x :: tX) aX.length = x) :
    step machine (cfg (bitState sel gate c1 c2) (aT ++ t :: tT) (aU ++ u :: tU)
        (aP ++ pp :: tP) F G (aX ++ x :: tX) aT.length gpos aX.length) =
      some (cfg
        (markerState sel gate
          (Add.carry (if sel then u else t) (gate && x) c1)
          (Add.carry (Add.bit (if sel then u else t) (gate && x) c1) (!pp) c2))
        (aT ++ Add.bit (if sel then u else t) (gate && x) c1 :: tT)
        (aU ++ Add.bit (Add.bit (if sel then u else t) (gate && x) c1) (!pp) c2 :: tU)
        (aP ++ pp :: tP) F G (aX ++ x :: tX) (aT.length + 1) gpos (aX.length + 1)) := by
  have wT : ∀ v, writeTapeBit (aT ++ t :: tT) aT.length v = aT ++ v :: tT :=
    fun v => write_mid aT tT t v
  have wU : ∀ v, writeTapeBit (aU ++ u :: tU) aT.length v = aU ++ v :: tU := by
    intro v; rw [← hU]; exact write_mid aU tU u v
  cases sel <;> cases gate <;> cases c1 <;> cases c2 <;>
    simp [step, machine, cfg, Configuration.scanned, hTr, hUr, hPr, hXr, markerState,
      bitState, selOf, gateOf, c1Of, c2Of] <;>
    apply configuration_ext
  all_goals first
    | rfl
    | (funext i; fin_cases i <;> simp [applyAction, HeadMove.apply, mv, wT, wU])

/-! ## 3. One sweep -/

def gateWord (gate : Bool) : List Bool → List Bool
  | [] => []
  | x :: xs => (gate && x) :: gateWord gate xs

@[simp] theorem gateWord_length (gate : Bool) (xs : List Bool) :
    (gateWord gate xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [gateWord, ih]

theorem sweep_timed (sel gate : Bool) :
    ∀ (ts us ps xs : List Bool), us.length = ts.length → ps.length = ts.length →
      xs.length = ts.length →
      ∀ (aT aU aP aX tX : List Bool), aU.length = aT.length → aP.length = aT.length →
        ∀ (F G : List Bool) (gpos : ℕ) (c1 c2 : Bool),
          Timed machine (2 * ts.length + 1)
            (cfg (markerState sel gate c1 c2) (aT ++ frame ts) (aU ++ frame us)
              (aP ++ frame ps) F G (aX ++ frame xs ++ tX) aT.length gpos aX.length)
            (cfg 1
              (aT ++ frame (Add.sum (if sel then us else ts) (gateWord gate xs) c1))
              (aU ++ frame (Add.sum
                (Add.sum (if sel then us else ts) (gateWord gate xs) c1)
                (FinalPrimeRow.negWord ps) c2))
              (aP ++ frame ps)
              (writeTapeBit F 0 (Add.overflow
                (Add.sum (if sel then us else ts) (gateWord gate xs) c1)
                (FinalPrimeRow.negWord ps) c2))
              G (aX ++ frame xs ++ tX)
              (aT.length + 2 * ts.length + 1) gpos (aX.length + 2 * ts.length + 1)) := by
  intro ts
  induction ts with
  | nil =>
    intro us ps xs hus hps hxs aT aU aP aX tX _haU _haP F G gpos c1 c2
    have hu : us = [] := List.length_eq_zero_iff.mp (by simpa using hus)
    have hp : ps = [] := List.length_eq_zero_iff.mp (by simpa using hps)
    have hx : xs = [] := List.length_eq_zero_iff.mp (by simpa using hxs)
    subst hu; subst hp; subst hx
    have hread : readTapeBit (aT ++ frame ([] : List Bool)) aT.length = false := by
      simpa [frame] using Streaming.read_append aT ([] : List Bool) false
    have hstep := halt_step sel gate c1 c2 (aT ++ frame ([] : List Bool))
      (aU ++ frame ([] : List Bool)) (aP ++ frame ([] : List Bool)) F G
      (aX ++ frame ([] : List Bool) ++ tX) aT.length gpos aX.length hread
    have h := Timed.single (p := machine)
      (by cases sel <;> cases gate <;> cases c1 <;> cases c2 <;> rfl) hstep
    simpa [frame, gateWord, Add.sum, Add.overflow, FinalPrimeRow.negWord] using h
  | cons t ts ih =>
    intro us ps xs hus hps hxs aT aU aP aX tX haU haP F G gpos c1 c2
    cases us with
    | nil => simp at hus
    | cons u us =>
      cases ps with
      | nil => simp at hps
      | cons pp ps =>
        cases xs with
        | nil => simp at hxs
        | cons x xs =>
          have hus' : us.length = ts.length := by simpa using hus
          have hps' : ps.length = ts.length := by simpa using hps
          have hxs' : xs.length = ts.length := by simpa using hxs
          have hmark : readTapeBit (aT ++ frame (t :: ts)) aT.length = true := by
            simpa [frame, List.append_assoc] using Streaming.read_append aT (t :: frame ts) true
          have hfirst := marker_step sel gate c1 c2 (aT ++ frame (t :: ts))
            (aU ++ frame (u :: us)) (aP ++ frame (pp :: ps)) F G
            (aX ++ frame (x :: xs) ++ tX) aT.length gpos aX.length hmark
          have hreadT : readTapeBit ((aT ++ [true]) ++ t :: frame ts) (aT ++ [true]).length = t :=
            Streaming.read_append (aT ++ [true]) (frame ts) t
          have hreadU : readTapeBit ((aU ++ [true]) ++ u :: frame us) (aT ++ [true]).length = u := by
            have h := Streaming.read_append (aU ++ [true]) (frame us) u
            simp only [List.length_append, List.length_cons, List.length_nil, haU] at h ⊢
            exact h
          have hreadP : readTapeBit ((aP ++ [true]) ++ pp :: frame ps)
              (aT ++ [true]).length = pp := by
            have h := Streaming.read_append (aP ++ [true]) (frame ps) pp
            simp only [List.length_append, List.length_cons, List.length_nil, haP] at h ⊢
            exact h
          have hreadX : readTapeBit ((aX ++ [true]) ++ x :: (frame xs ++ tX))
              (aX ++ [true]).length = x := Streaming.read_append (aX ++ [true]) (frame xs ++ tX) x
          have hsecond : step machine (cfg (bitState sel gate c1 c2) (aT ++ frame (t :: ts))
              (aU ++ frame (u :: us)) (aP ++ frame (pp :: ps)) F G (aX ++ frame (x :: xs) ++ tX)
              (aT.length + 1) gpos (aX.length + 1)) =
                some (cfg (markerState sel gate
                    (Add.carry (if sel then u else t) (gate && x) c1)
                    (Add.carry (Add.bit (if sel then u else t) (gate && x) c1) (!pp) c2))
                  ((aT ++ [true, Add.bit (if sel then u else t) (gate && x) c1]) ++ frame ts)
                  ((aU ++ [true, Add.bit (Add.bit (if sel then u else t) (gate && x) c1) (!pp) c2])
                    ++ frame us)
                  ((aP ++ [true, pp]) ++ frame ps) F G
                  ((aX ++ [true, x]) ++ frame xs ++ tX) (aT.length + 2) gpos (aX.length + 2)) := by
            have h := bit_step sel gate c1 c2 t u pp x (aT ++ [true]) (frame ts) (aU ++ [true])
              (frame us) (aP ++ [true]) (frame ps) F G (aX ++ [true]) (frame xs ++ tX) gpos
              (by simp [haU]) hreadT hreadU hreadP hreadX
            simp only [List.length_append, List.length_cons, List.length_nil] at h
            simpa [frame, List.append_assoc] using h
          have htail := ih us ps xs hus' hps' hxs'
            (aT ++ [true, Add.bit (if sel then u else t) (gate && x) c1])
            (aU ++ [true, Add.bit (Add.bit (if sel then u else t) (gate && x) c1) (!pp) c2])
            (aP ++ [true, pp]) (aX ++ [true, x]) tX (by simp [haU]) (by simp [haP]) F G gpos
            (Add.carry (if sel then u else t) (gate && x) c1)
            (Add.carry (Add.bit (if sel then u else t) (gate && x) c1) (!pp) c2)
          have hlenT : (aT ++ [true, Add.bit (if sel then u else t) (gate && x) c1]).length =
              aT.length + 2 := by simp
          have hlenX : (aX ++ [true, x]).length = aX.length + 2 := by simp
          rw [hlenT, hlenX] at htail
          have hjoin := (Timed.single (p := machine)
              (by cases sel <;> cases gate <;> cases c1 <;> cases c2 <;> rfl) hfirst).trans
            ((Timed.single (p := machine)
              (by cases sel <;> cases gate <;> cases c1 <;> cases c2 <;> rfl) hsecond).trans
              (by simpa [List.append_assoc] using htail))
          have htime : 1 + (1 + (2 * ts.length + 1)) = 2 * (t :: ts).length + 1 := by simp; omega
          have hposT : aT.length + 2 + 2 * ts.length + 1 = aT.length + 2 * (t :: ts).length + 1 := by
            simp; omega
          have hposX : aX.length + 2 + 2 * ts.length + 1 = aX.length + 2 * (t :: ts).length + 1 := by
            simp; omega
          rw [htime, hposT, hposX] at hjoin
          have hif : (if sel then u :: us else t :: ts) =
              (if sel then u else t) :: (if sel then us else ts) := by cases sel <;> rfl
          rw [hif]
          simpa [gateWord, Add.sum, Add.overflow, FinalPrimeRow.negWord, frame,
            List.append_assoc] using hjoin

/-! ## 4. The whole pass -/

def nextState (prime width : ℕ) (gate : Bool) (xs : List Bool)
    (st : List Bool × List Bool × Bool) : List Bool × List Bool × Bool :=
  let t := Add.sum (if st.2.2 then st.2.1 else st.1) (gateWord gate xs) false
  (t, Add.sum t (FinalPrimeRow.negWord (SignedSortKey.binary width prime)) true,
    Add.overflow t (FinalPrimeRow.negWord (SignedSortKey.binary width prime)) true)

theorem pass_run (prime width : ℕ) (gate : Bool) (xs F G aX tX : List Bool) (gpos : ℕ)
    (st : List Bool × List Bool × Bool)
    (hT : st.1.length = width) (hU : st.2.1.length = width) (hxs : xs.length = width)
    (hF : readTapeBit F 0 = st.2.2) (hG : readTapeBit G gpos = gate) :
    ∃ r : ExecutionReceipt 6 34,
      runFrom machine (2 * width + 2)
          ⟨machine.start, ![0, 0, 0, 0, gpos, aX.length],
            ![frame st.1, frame st.2.1, frame (SignedSortKey.binary width prime), F, G,
              aX ++ frame xs ++ tX]⟩ = some r ∧
        r.steps = 2 * width + 2 ∧
        r.final.heads = ![2 * width + 1, 2 * width + 1, 2 * width + 1, 0, gpos + 1,
          aX.length + (2 * width + 1)] ∧
        r.final.tapes =
          ![frame (nextState prime width gate xs st).1,
            frame (nextState prime width gate xs st).2.1,
            frame (SignedSortKey.binary width prime),
            writeTapeBit F 0 (nextState prime width gate xs st).2.2, G,
            aX ++ frame xs ++ tX] := by
  have hentry := entry_step (frame st.1) (frame st.2.1)
    (frame (SignedSortKey.binary width prime)) F G (aX ++ frame xs ++ tX) gpos aX.length
    st.2.2 gate hF hG
  have hps : (SignedSortKey.binary width prime).length = st.1.length := by
    rw [SignedSortKey.binary_length, hT]
  have hsweep := sweep_timed st.2.2 gate st.1 st.2.1 (SignedSortKey.binary width prime) xs
    (by rw [hU, hT]) hps (by rw [hxs, hT]) [] [] [] aX tX rfl rfl F G (gpos + 1) false true
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at hsweep
  have hall := (Timed.single (p := machine) (by rfl) hentry).trans hsweep
  have htime : 1 + (2 * st.1.length + 1) = 2 * width + 2 := by rw [hT]; omega
  rw [htime] at hall
  obtain ⟨r, hr, hf, hs⟩ := hall.run (by rfl)
  refine ⟨r, ?_, hs, ?_, ?_⟩
  · have hc : cfg 0 (frame st.1) (frame st.2.1) (frame (SignedSortKey.binary width prime)) F G
        (aX ++ frame xs ++ tX) 0 gpos aX.length =
        (⟨machine.start, ![0, 0, 0, 0, gpos, aX.length],
          ![frame st.1, frame st.2.1, frame (SignedSortKey.binary width prime), F, G,
            aX ++ frame xs ++ tX]⟩ : Configuration 6 34) := by
      apply configuration_ext
      · rfl
      · rfl
      · rfl
    rw [hc] at hr
    exact hr
  · rw [hf, hT]; funext i; fin_cases i <;> rfl
  · rw [hf, hT]; funext i; fin_cases i <;> rfl

/-! ## 5. Exact arithmetic of one gated modular addition -/

theorem gateWord_true (xs : List Bool) : gateWord true xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [gateWord, ih]

theorem gateWord_false_value (xs : List Bool) : value (gateWord false xs) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [gateWord, value, ih]

theorem gateWord_value (gate : Bool) (xs : List Bool) :
    value (gateWord gate xs) = if gate then value xs else 0 := by
  cases gate
  · simpa using gateWord_false_value xs
  · simpa using congrArg value (gateWord_true xs)

/-- The single conditional subtraction: a value below `2 * prime` is reduced. -/
theorem reduce_core (prime width : ℕ) (t : List Bool) (ht : t.length = width)
    (hp : 2 * prime ≤ 2 ^ width) (hlt : value t < 2 * prime) :
    (if Add.overflow t (FinalPrimeRow.negWord (SignedSortKey.binary width prime)) true then
        value (Add.sum t (FinalPrimeRow.negWord (SignedSortKey.binary width prime)) true)
      else value t) = value t % prime := by
  set np := FinalPrimeRow.negWord (SignedSortKey.binary width prime) with hnp
  have hnplen : np.length = width := by
    rw [hnp, FinalPrimeRow.negWord_length, SignedSortKey.binary_length]
  have hnpval : value np + prime + 1 = 2 ^ width := by
    have h := FinalPrimeRow.negWord_value (SignedSortKey.binary width prime)
    rw [← hnp, SignedSortKey.binary_length,
      SignedSortKey.binary_value width prime (by omega)] at h
    exact h
  have hw : t.length = np.length := by rw [ht, hnplen]
  have hsum := Add.sum_value t np true hw
  rw [ht] at hsum
  have hsumlt : value (Add.sum t np true) < 2 ^ width := by
    have h := value_lt (Add.sum t np true)
    rwa [Add.sum_length t np true hw, ht] at h
  cases hov : Add.overflow t np true with
  | false =>
    rw [hov, Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.add_zero] at hsum
    rw [if_neg (by simp)]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  | true =>
    rw [hov, Bool.toNat_true, Nat.mul_one] at hsum
    have hge : prime ≤ value t := by omega
    have heq : value (Add.sum t np true) = value t - prime := by omega
    rw [if_pos rfl, heq, Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]

theorem nextState_length (prime width : ℕ) (gate : Bool) (xs : List Bool)
    (st : List Bool × List Bool × Bool) (h1 : st.1.length = width) (h2 : st.2.1.length = width)
    (hxs : xs.length = width) :
    (nextState prime width gate xs st).1.length = width ∧
      (nextState prime width gate xs st).2.1.length = width := by
  have hres : (if st.2.2 then st.2.1 else st.1).length = width := by split <;> assumption
  have hg : (if st.2.2 then st.2.1 else st.1).length = (gateWord gate xs).length := by
    rw [hres, gateWord_length, hxs]
  have hT : (Add.sum (if st.2.2 then st.2.1 else st.1) (gateWord gate xs) false).length = width := by
    rw [Add.sum_length _ _ _ hg, hres]
  refine ⟨hT, ?_⟩
  have hw : (Add.sum (if st.2.2 then st.2.1 else st.1) (gateWord gate xs) false).length =
      (FinalPrimeRow.negWord (SignedSortKey.binary width prime)).length := by
    rw [hT, FinalPrimeRow.negWord_length, SignedSortKey.binary_length]
  show (Add.sum (Add.sum (if st.2.2 then st.2.1 else st.1) (gateWord gate xs) false)
    (FinalPrimeRow.negWord (SignedSortKey.binary width prime)) true).length = width
  rw [Add.sum_length _ _ _ hw, hT]

/-- One sweep is exactly one gated modular addition. -/
theorem nextState_residue (prime width : ℕ) (gate : Bool) (xs : List Bool)
    (st : List Bool × List Bool × Bool) (h1 : st.1.length = width) (h2 : st.2.1.length = width)
    (hxs : xs.length = width) (hp : 2 * prime ≤ 2 ^ width)
    (hres : FinalPrimeRow.residueOf st < prime) (hx : value xs < prime) :
    FinalPrimeRow.residueOf (nextState prime width gate xs st) =
      (FinalPrimeRow.residueOf st + (if gate then value xs else 0)) % prime := by
  have hreslen : (if st.2.2 then st.2.1 else st.1).length = width := by split <;> assumption
  have hg : (if st.2.2 then st.2.1 else st.1).length = (gateWord gate xs).length := by
    rw [hreslen, gateWord_length, hxs]
  set t := Add.sum (if st.2.2 then st.2.1 else st.1) (gateWord gate xs) false with htdef
  have htlen : t.length = width := by rw [htdef, Add.sum_length _ _ _ hg, hreslen]
  have hsum := Add.sum_value (if st.2.2 then st.2.1 else st.1) (gateWord gate xs) false hg
  rw [hreslen] at hsum
  have htlt : value t < 2 ^ width := by
    have h := value_lt t
    rwa [htlen] at h
  have hgv : value (gateWord gate xs) = if gate then value xs else 0 := gateWord_value gate xs
  have hfit : FinalPrimeRow.residueOf st + (if gate then value xs else 0) < 2 ^ width := by
    have : (if gate then value xs else 0) < prime := by split <;> omega
    omega
  have htval : value t = FinalPrimeRow.residueOf st + (if gate then value xs else 0) := by
    rw [hgv] at hsum
    have hro : value (if st.2.2 then st.2.1 else st.1) = FinalPrimeRow.residueOf st := rfl
    rw [hro] at hsum
    cases hov : Add.overflow (if st.2.2 then st.2.1 else st.1) (gateWord gate xs) false <;>
      rw [hov] at hsum <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero,
        Nat.mul_one, Nat.add_zero] at hsum <;> omega
  have hlt2 : value t < 2 * prime := by
    have : (if gate then value xs else 0) < prime := by split <;> omega
    omega
  have hcore := reduce_core prime width t htlen hp hlt2
  have hgoal : FinalPrimeRow.residueOf (nextState prime width gate xs st) =
      (if Add.overflow t (FinalPrimeRow.negWord (SignedSortKey.binary width prime)) true then
        value (Add.sum t (FinalPrimeRow.negWord (SignedSortKey.binary width prime)) true)
      else value t) := by
    simp only [FinalPrimeRow.residueOf, nextState, ← htdef]
    split <;> rfl
  rw [hgoal, hcore, htval]

/-! ## 6. The summand stream and the driven accumulation -/

def selected : Fin 6 → Bool := ![true, true, true, false, false, false]

def body := MaskedReset.machine machine selected

def cost (width : ℕ) : ℕ := 2 * (2 * width + 2) + 2

def blocks (w : ℕ → List Bool) : ℕ → ℕ → List Bool
  | _, 0 => []
  | j, n + 1 => frame (w j) ++ blocks w (j + 1) n

theorem blocks_add (w : ℕ → List Bool) (j m n : ℕ) :
    blocks w j (m + n) = blocks w j m ++ blocks w (j + m) n := by
  induction m generalizing j with
  | zero => simp [blocks]
  | succ m ih =>
    have h : m + 1 + n = (m + n) + 1 := by omega
    rw [h]
    show frame (w j) ++ blocks w (j + 1) (m + n) = _
    rw [ih (j + 1), show j + (m + 1) = j + 1 + m by omega,
      show blocks w j (m + 1) = frame (w j) ++ blocks w (j + 1) m from rfl,
      List.append_assoc]

theorem blocks_length (w : ℕ → List Bool) (width : ℕ) (hw : ∀ i, (w i).length = width) (j n : ℕ) :
    (blocks w j n).length = n * (2 * width + 1) := by
  induction n generalizing j with
  | zero => simp [blocks]
  | succ n ih => simp [blocks, ih (j + 1), hw j]; ring

def stateAt (prime width : ℕ) (w : ℕ → List Bool) (gates : List Bool) :
    ℕ → List Bool × List Bool × Bool
  | 0 => (SignedSortKey.binary width 0, SignedSortKey.binary width 0, false)
  | j + 1 => nextState prime width (gates.getD j false) (w j) (stateAt prime width w gates j)

def partialSum (w : ℕ → List Bool) (gates : List Bool) (j : ℕ) : ℕ :=
  (List.range j).foldl
    (fun acc i => acc + (if gates.getD i false then value (w i) else 0)) 0

theorem partialSum_succ (w : ℕ → List Bool) (gates : List Bool) (j : ℕ) :
    partialSum w gates (j + 1) =
      partialSum w gates j + (if gates.getD j false then value (w j) else 0) := by
  simp [partialSum, List.range_succ]

theorem stateAt_length (prime width : ℕ) (w : ℕ → List Bool) (gates : List Bool)
    (hwlen : ∀ i, (w i).length = width) (j : ℕ) :
    (stateAt prime width w gates j).1.length = width ∧
      (stateAt prime width w gates j).2.1.length = width := by
  induction j with
  | zero => simp [stateAt]
  | succ j ih =>
    exact nextState_length prime width _ _ _ ih.1 ih.2 (hwlen j)

theorem stateAt_residue (prime width : ℕ) (w : ℕ → List Bool) (gates : List Bool)
    (hwlen : ∀ i, (w i).length = width) (hwval : ∀ i, value (w i) < prime)
    (hp0 : 0 < prime) (hp : 2 * prime ≤ 2 ^ width) (j : ℕ) :
    FinalPrimeRow.residueOf (stateAt prime width w gates j) = partialSum w gates j % prime := by
  induction j with
  | zero =>
    have h2 : (0 : ℕ) < 2 ^ width := by positivity
    simp [stateAt, FinalPrimeRow.residueOf, partialSum,
      SignedSortKey.binary_value width 0 h2]
  | succ j ih =>
    have hlen := stateAt_length prime width w gates hwlen j
    have hres : FinalPrimeRow.residueOf (stateAt prime width w gates j) < prime := by
      rw [ih]; exact Nat.mod_lt _ hp0
    have hstep := nextState_residue prime width (gates.getD j false) (w j)
      (stateAt prime width w gates j) hlen.1 hlen.2 (hwlen j) hp hres (hwval j)
    rw [show stateAt prime width w gates (j + 1) =
      nextState prime width (gates.getD j false) (w j) (stateAt prime width w gates j) from rfl,
      hstep, ih, partialSum_succ]
    exact ((Nat.mod_modEq (partialSum w gates j) prime).add_right
      (if gates.getD j false then value (w j) else 0))

noncomputable def sourceCfg (prime width cap Q : ℕ) (w : ℕ → List Bool) (gates : List Bool)
    (j : ℕ) : Configuration (6 + 1) (34 + 2) :=
  ⟨body.start,
    Fin.addCases (motive := fun _ => ℕ)
      (![0, 0, 0, 0, j, j * (2 * width + 1)] : Fin 6 → ℕ) (fun _ : Fin 1 => 0),
    Fin.addCases (motive := fun _ => List Bool)
      (![frame (stateAt prime width w gates j).1, frame (stateAt prime width w gates j).2.1,
        frame (SignedSortKey.binary width prime), [(stateAt prime width w gates j).2.2],
        gates, blocks w 0 Q] : Fin 6 → List Bool)
      (fun _ : Fin 1 => List.replicate cap false)⟩

theorem body_supplier (prime width cap Q : ℕ) (w : ℕ → List Bool) (gates : List Bool)
    (hwlen : ∀ i, (w i).length = width) (hcap : 2 * width + 2 ≤ cap) (j : ℕ) (hj : j < Q) :
    ∃ r, runFrom body (cost width) (sourceCfg prime width cap Q w gates j) = some r ∧
      r.final.heads = (sourceCfg prime width cap Q w gates (j + 1)).heads ∧
      r.final.tapes = (sourceCfg prime width cap Q w gates (j + 1)).tapes ∧ r.steps ≤ cost width := by
  obtain ⟨hT, hU⟩ := stateAt_length prime width w gates hwlen j
  obtain ⟨k, hk⟩ : ∃ k, Q = j + (k + 1) := ⟨Q - j - 1, by omega⟩
  have hsplit : blocks w 0 Q = blocks w 0 j ++ frame (w j) ++ blocks w (j + 1) k := by
    have h1 := blocks_add w 0 j (k + 1)
    rw [Nat.zero_add, ← hk] at h1
    rw [h1, show blocks w j (k + 1) = frame (w j) ++ blocks w (j + 1) k from rfl,
      ← List.append_assoc]
  have hblen : (blocks w 0 j).length = j * (2 * width + 1) := blocks_length w width hwlen 0 j
  have hF : readTapeBit [(stateAt prime width w gates j).2.2] 0 =
      (stateAt prime width w gates j).2.2 := rfl
  have hG : readTapeBit gates j = gates.getD j false := rfl
  obtain ⟨raw, hraw, hsteps, hheads, htapes⟩ :=
    pass_run prime width (gates.getD j false) (w j)
      [(stateAt prime width w gates j).2.2] gates (blocks w 0 j)
      (blocks w (j + 1) k) j (stateAt prime width w gates j) hT hU (hwlen j) hF hG
  rw [hblen] at hraw hheads
  rw [← hsplit] at hraw htapes
  have hstep : Step machine (2 * width + 2)
      (![0, 0, 0, 0, j, j * (2 * width + 1)] : Fin 6 → ℕ)
      (![frame (stateAt prime width w gates j).1, frame (stateAt prime width w gates j).2.1,
        frame (SignedSortKey.binary width prime), [(stateAt prime width w gates j).2.2],
        gates, blocks w 0 Q] : Fin 6 → List Bool)
      (![2 * width + 1, 2 * width + 1, 2 * width + 1, 0, j + 1,
        (j + 1) * (2 * width + 1)] : Fin 6 → ℕ)
      (![frame (stateAt prime width w gates (j + 1)).1,
        frame (stateAt prime width w gates (j + 1)).2.1,
        frame (SignedSortKey.binary width prime),
        [(stateAt prime width w gates (j + 1)).2.2], gates,
        blocks w 0 Q] : Fin 6 → List Bool) := by
    refine Step.of_run (r := raw) hraw ?_ ?_
    · have hmul : (j + 1) * (2 * width + 1) = j * (2 * width + 1) + (2 * width + 1) := by ring
      rw [hheads, hmul]
    · rw [htapes]
      funext i
      fin_cases i <;> rfl
  obtain ⟨r, hr, hh, ht, hs⟩ := hstep.mask selected
    (by intro i; fin_cases i <;> simp [selected]) hcap
  refine ⟨r, hr, ?_, ht, hs⟩
  have hheadsEq : (sourceCfg prime width cap Q w gates (j + 1)).heads =
      Fin.addCases (motive := fun _ => ℕ)
        (fun i => if selected i then 0
          else (![2 * width + 1, 2 * width + 1, 2 * width + 1, 0, j + 1,
            (j + 1) * (2 * width + 1)] : Fin 6 → ℕ) i) (fun _ : Fin 1 => 0) := by
    show Fin.addCases (motive := fun _ => ℕ)
      (![0, 0, 0, 0, j + 1, (j + 1) * (2 * width + 1)] : Fin 6 → ℕ) (fun _ : Fin 1 => 0) = _
    congr 1
    funext k
    fin_cases k <;> simp [selected]
  rw [hh]
  exact hheadsEq.symm

/-- The modular accumulation row: `Q` driven sweeps add the gated summands
`w 0, …, w (Q-1)` modulo `prime`, in `Q * (4 * width + 9) + 3` ordinary steps. -/
theorem accumulate_loop (prime width cap Q : ℕ) (w : ℕ → List Bool) (gates : List Bool)
    (hwlen : ∀ i, (w i).length = width) (hwval : ∀ i, value (w i) < prime)
    (hp0 : 0 < prime) (hp : 2 * prime ≤ 2 ^ width) (hcap : 2 * width + 2 ≤ cap) :
    ∃ r, runFrom (CloseoutRowsDegreeLoop.machine body) (Q * (cost width + 3) + 3)
        (RepeatMachine.cfg 0 (sourceCfg prime width cap Q w gates 0) Q 1) = some r ∧
      r.final = RepeatMachine.cfg 3 (sourceCfg prime width cap Q w gates Q) Q 1 ∧
      r.steps ≤ Q * (cost width + 3) + 3 ∧
      FinalPrimeRow.residueOf (stateAt prime width w gates Q) = partialSum w gates Q % prime := by
  obtain ⟨r, hr, hf, hs⟩ := CloseoutRowsDegreeLoop.loop_run body
    (fun j _ => sourceCfg prime width cap Q w gates j) (fun _ => []) (cost width) Q
    (fun _ _ _ => rfl)
    (fun j hj _ => by
      obtain ⟨rr, h1, h2, h3, h4⟩ := body_supplier prime width cap Q w gates hwlen hcap j hj
      exact ⟨rr, h1, h2, h3, h4⟩) []
  exact ⟨r, hr, hf, hs, stateAt_residue prime width w gates hwlen hwval hp0 hp Q⟩

end NearCubicWires.RepairOrdinary.FinalPrimeModular
