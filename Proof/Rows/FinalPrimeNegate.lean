import Proof.Rows.FinalPrimeModularSum

/-! # Modular negation: the residue of a negative coefficient

`FinalPrimeThresholdRow.threshold_row_run` asks its summand stream to carry,
for each index, the residue of that **signed** weight modulo the prime.
`FinalPrimeResidue.prime_row_word` supplies that for a natural number; this
file supplies the remaining half, `z ↦ (p - z) mod p`, so a negative weight
`-m` is handled as "reduce `m`, then negate".

`machine : Machine 5 9` is again a single sweep with two carry chains running
at once in the finite control:

    t := p + (2 ^ L - 1 - z) + 1 = p - z ,   u := t + (2 ^ L - p) ,

and the decisive carry of the second chain lands on `F`, so `(T, U, F)` is
delivered in exactly the two-candidate form every other stage consumes.
`p - z < 2 * p`, so one conditional subtraction is again enough, and the
`z = 0` case (where `p - z = p`) is reduced to `0` by that same subtraction.

Tapes: `0 = T`, `1 = U`, `2 = P`, `3 = F` (head pinned at 0), `4 = Z`.
-/
namespace NearCubicWires.RepairOrdinary.FinalPrimeNegate
open LocalBitMultitape RecoveryExecution RadixSemantics ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def markerState (c1 c2 : Bool) : Fin 9 :=
  if c1 then (if c2 then 4 else 3) else (if c2 then 2 else 1)
def bitState (c1 c2 : Bool) : Fin 9 :=
  if c1 then (if c2 then 8 else 7) else (if c2 then 6 else 5)
def c1Of (q : Fin 9) : Bool := decide (2 ≤ (q.val - 1) % 4)
def c2Of (q : Fin 9) : Bool := decide ((q.val - 1) % 2 = 1)


def mv : Fin 5 → HeadMove := fun i => if i.val = 3 then .stay else .right

def machine : Machine 5 9 where
  descriptionBits := 0
  start := markerState true true
  halted := fun q => q.val == 0
  rule := fun q scanned =>
    if q.val = 0 then none
    else if q.val < 5 then
      (if scanned 0 then some ⟨bitState (c1Of q) (c2Of q), fun _ => none, mv⟩
        else some ⟨0, fun i => if i.val = 3 then some (c2Of q) else none, mv⟩)
    else
      some ⟨markerState
          (Add.carry (scanned 2) (!scanned 4) (c1Of q))
          (Add.carry (Add.bit (scanned 2) (!scanned 4) (c1Of q)) (!scanned 2) (c2Of q)),
        fun i =>
          if i.val = 0 then some (Add.bit (scanned 2) (!scanned 4) (c1Of q))
          else if i.val = 1 then
            some (Add.bit (Add.bit (scanned 2) (!scanned 4) (c1Of q)) (!scanned 2) (c2Of q))
          else none,
        mv⟩

def cfg (q : Fin 9) (T U P F Z : List Bool) (pos : ℕ) : Configuration 5 9 :=
  ⟨q, ![pos, pos, pos, 0, pos], ![T, U, P, F, Z]⟩

theorem write_mid (pre tail : List Bool) (old v : Bool) :
    writeTapeBit (pre ++ old :: tail) pre.length v = pre ++ v :: tail := by
  induction pre with
  | nil => rfl
  | cons b pre ih => simpa [writeTapeBit] using congrArg (List.cons b) ih

theorem marker_step (c1 c2 : Bool) (T U P F Z : List Bool) (pos : ℕ)
    (hT : readTapeBit T pos = true) :
    step machine (cfg (markerState c1 c2) T U P F Z pos) =
      some (cfg (bitState c1 c2) T U P F Z (pos + 1)) := by
  cases c1 <;> cases c2 <;>
    simp [step, machine, cfg, Configuration.scanned, hT, markerState, bitState, c1Of, c2Of] <;>
    apply configuration_ext
  all_goals first
    | rfl
    | (funext i; fin_cases i <;> simp [applyAction, HeadMove.apply, mv])

theorem halt_step (c1 c2 : Bool) (T U P F Z : List Bool) (pos : ℕ)
    (hT : readTapeBit T pos = false) :
    step machine (cfg (markerState c1 c2) T U P F Z pos) =
      some (cfg 0 T U P (writeTapeBit F 0 c2) Z (pos + 1)) := by
  cases c1 <;> cases c2 <;>
    simp [step, machine, cfg, Configuration.scanned, hT, markerState, c1Of, c2Of] <;>
    apply configuration_ext
  all_goals first
    | rfl
    | (funext i; fin_cases i <;> simp [applyAction, HeadMove.apply, mv])

theorem bit_step (c1 c2 t u pb zb : Bool) (aT tT aU tU aP tP F aZ tZ : List Bool)
    (hU : aU.length = aT.length) (_hP : aP.length = aT.length) (_hZ : aZ.length = aT.length)
    (_hTr : readTapeBit (aT ++ t :: tT) aT.length = t)
    (hPr : readTapeBit (aP ++ pb :: tP) aT.length = pb)
    (hZr : readTapeBit (aZ ++ zb :: tZ) aT.length = zb) :
    step machine (cfg (bitState c1 c2) (aT ++ t :: tT) (aU ++ u :: tU) (aP ++ pb :: tP) F
        (aZ ++ zb :: tZ) aT.length) =
      some (cfg
        (markerState (Add.carry pb (!zb) c1)
          (Add.carry (Add.bit pb (!zb) c1) (!pb) c2))
        (aT ++ Add.bit pb (!zb) c1 :: tT)
        (aU ++ Add.bit (Add.bit pb (!zb) c1) (!pb) c2 :: tU)
        (aP ++ pb :: tP) F (aZ ++ zb :: tZ) (aT.length + 1)) := by
  have wT : ∀ v, writeTapeBit (aT ++ t :: tT) aT.length v = aT ++ v :: tT :=
    fun v => write_mid aT tT t v
  have wU : ∀ v, writeTapeBit (aU ++ u :: tU) aT.length v = aU ++ v :: tU := by
    intro v; rw [← hU]; exact write_mid aU tU u v
  cases c1 <;> cases c2 <;>
    simp [step, machine, cfg, Configuration.scanned, hPr, hZr, markerState, bitState,
      c1Of, c2Of] <;>
    apply configuration_ext
  all_goals first
    | rfl
    | (funext i; fin_cases i <;> simp [applyAction, HeadMove.apply, mv, wT, wU])

theorem sweep_timed :
    ∀ (ts us ps zs : List Bool), us.length = ts.length → ps.length = ts.length →
      zs.length = ts.length →
      ∀ (aT aU aP aZ : List Bool), aU.length = aT.length → aP.length = aT.length →
        aZ.length = aT.length → ∀ (F : List Bool) (c1 c2 : Bool),
          Timed machine (2 * ts.length + 1)
            (cfg (markerState c1 c2) (aT ++ frame ts) (aU ++ frame us) (aP ++ frame ps) F
              (aZ ++ frame zs) aT.length)
            (cfg 0 (aT ++ frame (Add.sum ps (FinalPrimeRow.negWord zs) c1))
              (aU ++ frame (Add.sum (Add.sum ps (FinalPrimeRow.negWord zs) c1)
                (FinalPrimeRow.negWord ps) c2))
              (aP ++ frame ps)
              (writeTapeBit F 0 (Add.overflow (Add.sum ps (FinalPrimeRow.negWord zs) c1)
                (FinalPrimeRow.negWord ps) c2))
              (aZ ++ frame zs) (aT.length + 2 * ts.length + 1)) := by
  intro ts
  induction ts with
  | nil =>
    intro us ps zs hus hps hzs aT aU aP aZ _haU _haP _haZ F c1 c2
    have hu : us = [] := List.length_eq_zero_iff.mp (by simpa using hus)
    have hp : ps = [] := List.length_eq_zero_iff.mp (by simpa using hps)
    have hz : zs = [] := List.length_eq_zero_iff.mp (by simpa using hzs)
    subst hu; subst hp; subst hz
    have hread : readTapeBit (aT ++ frame ([] : List Bool)) aT.length = false := by
      simpa [frame] using Streaming.read_append aT ([] : List Bool) false
    have hstep := halt_step c1 c2 (aT ++ frame ([] : List Bool)) (aU ++ frame ([] : List Bool))
      (aP ++ frame ([] : List Bool)) F (aZ ++ frame ([] : List Bool)) aT.length hread
    have h := Timed.single (p := machine) (by cases c1 <;> cases c2 <;> rfl) hstep
    simpa [frame, Add.sum, Add.overflow, FinalPrimeRow.negWord] using h
  | cons t ts ih =>
    intro us ps zs hus hps hzs aT aU aP aZ haU haP haZ F c1 c2
    cases us with
    | nil => simp at hus
    | cons u us =>
      cases ps with
      | nil => simp at hps
      | cons pb ps =>
        cases zs with
        | nil => simp at hzs
        | cons zb zs =>
          have hus' : us.length = ts.length := by simpa using hus
          have hps' : ps.length = ts.length := by simpa using hps
          have hzs' : zs.length = ts.length := by simpa using hzs
          have hmark : readTapeBit (aT ++ frame (t :: ts)) aT.length = true := by
            simpa [frame, List.append_assoc] using Streaming.read_append aT (t :: frame ts) true
          have hfirst := marker_step c1 c2 (aT ++ frame (t :: ts)) (aU ++ frame (u :: us))
            (aP ++ frame (pb :: ps)) F (aZ ++ frame (zb :: zs)) aT.length hmark
          have hreadT : readTapeBit ((aT ++ [true]) ++ t :: frame ts) (aT ++ [true]).length = t :=
            Streaming.read_append (aT ++ [true]) (frame ts) t
          have hreadP : readTapeBit ((aP ++ [true]) ++ pb :: frame ps)
              (aT ++ [true]).length = pb := by
            have h := Streaming.read_append (aP ++ [true]) (frame ps) pb
            simp only [List.length_append, List.length_cons, List.length_nil, haP] at h ⊢
            exact h
          have hreadZ : readTapeBit ((aZ ++ [true]) ++ zb :: frame zs)
              (aT ++ [true]).length = zb := by
            have h := Streaming.read_append (aZ ++ [true]) (frame zs) zb
            simp only [List.length_append, List.length_cons, List.length_nil, haZ] at h ⊢
            exact h
          have hsecond : step machine (cfg (bitState c1 c2) (aT ++ frame (t :: ts))
              (aU ++ frame (u :: us)) (aP ++ frame (pb :: ps)) F (aZ ++ frame (zb :: zs))
              (aT.length + 1)) =
                some (cfg (markerState (Add.carry pb (!zb) c1)
                    (Add.carry (Add.bit pb (!zb) c1) (!pb) c2))
                  ((aT ++ [true, Add.bit pb (!zb) c1]) ++ frame ts)
                  ((aU ++ [true, Add.bit (Add.bit pb (!zb) c1) (!pb) c2]) ++ frame us)
                  ((aP ++ [true, pb]) ++ frame ps) F ((aZ ++ [true, zb]) ++ frame zs)
                  (aT.length + 2)) := by
            have h := bit_step c1 c2 t u pb zb (aT ++ [true]) (frame ts) (aU ++ [true]) (frame us)
              (aP ++ [true]) (frame ps) F (aZ ++ [true]) (frame zs)
              (by simp [haU]) (by simp [haP]) (by simp [haZ]) hreadT hreadP hreadZ
            simp only [List.length_append, List.length_cons, List.length_nil] at h
            simpa [frame, List.append_assoc] using h
          have htail := ih us ps zs hus' hps' hzs' (aT ++ [true, Add.bit pb (!zb) c1])
            (aU ++ [true, Add.bit (Add.bit pb (!zb) c1) (!pb) c2]) (aP ++ [true, pb])
            (aZ ++ [true, zb]) (by simp [haU]) (by simp [haP]) (by simp [haZ]) F
            (Add.carry pb (!zb) c1) (Add.carry (Add.bit pb (!zb) c1) (!pb) c2)
          have hlen : (aT ++ [true, Add.bit pb (!zb) c1]).length = aT.length + 2 := by simp
          rw [hlen] at htail
          have hjoin := (Timed.single (p := machine)
              (by cases c1 <;> cases c2 <;> rfl) hfirst).trans
            ((Timed.single (p := machine) (by cases c1 <;> cases c2 <;> rfl) hsecond).trans htail)
          have htime : 1 + (1 + (2 * ts.length + 1)) = 2 * (t :: ts).length + 1 := by simp; omega
          have hpos : aT.length + 2 + 2 * ts.length + 1 =
              aT.length + 2 * (t :: ts).length + 1 := by simp; omega
          rw [htime, hpos] at hjoin
          simpa [Add.sum, Add.overflow, FinalPrimeRow.negWord, frame, List.append_assoc] using hjoin

def negState (prime width : ℕ) (zs : List Bool) : List Bool × List Bool × Bool :=
  let t := Add.sum (SignedSortKey.binary width prime) (FinalPrimeRow.negWord zs) true
  (t, Add.sum t (FinalPrimeRow.negWord (SignedSortKey.binary width prime)) true,
    Add.overflow t (FinalPrimeRow.negWord (SignedSortKey.binary width prime)) true)

theorem negate_step (prime width : ℕ) (ts us zs F : List Bool)
    (hts : ts.length = width) (hus : us.length = width) (hzs : zs.length = width) :
    Step machine (2 * width + 1) (![0, 0, 0, 0, 0] : Fin 5 → ℕ)
      (![frame ts, frame us, frame (SignedSortKey.binary width prime), F,
        frame zs] : Fin 5 → List Bool)
      (![2 * width + 1, 2 * width + 1, 2 * width + 1, 0, 2 * width + 1] : Fin 5 → ℕ)
      (![frame (negState prime width zs).1, frame (negState prime width zs).2.1,
        frame (SignedSortKey.binary width prime),
        writeTapeBit F 0 (negState prime width zs).2.2, frame zs] : Fin 5 → List Bool) := by
  have hps : (SignedSortKey.binary width prime).length = ts.length := by
    rw [SignedSortKey.binary_length, hts]
  have h := sweep_timed ts us (SignedSortKey.binary width prime) zs (by rw [hus, hts]) hps
    (by rw [hzs, hts]) [] [] [] [] rfl rfl rfl F true true
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at h
  rw [hts] at h
  obtain ⟨r, hr, hf, hs⟩ := h.run (by rfl)
  refine Step.of_run (r := r) ?_ ?_ ?_
  · have hc : cfg (markerState true true) (frame ts) (frame us)
        (frame (SignedSortKey.binary width prime)) F (frame zs) 0 =
        (⟨machine.start, (![0, 0, 0, 0, 0] : Fin 5 → ℕ),
          (![frame ts, frame us, frame (SignedSortKey.binary width prime), F,
            frame zs] : Fin 5 → List Bool)⟩ : Configuration 5 9) := by
      apply configuration_ext
      · rfl
      · rfl
      · rfl
    rw [hc] at hr
    exact hr
  · rw [hf]; funext i; fin_cases i <;> rfl
  · rw [hf]; funext i; fin_cases i <;> rfl

/-- One sweep delivers `(p - z) mod p` in the two-candidate form. -/
theorem negate_residue (prime width : ℕ) (zs : List Bool) (hzs : zs.length = width)
    (_hp0 : 0 < prime) (hp : 2 * prime ≤ 2 ^ width) (hz : value zs < prime) :
    FinalPrimeRow.residueOf (negState prime width zs) = (prime - value zs) % prime := by
  set ps := SignedSortKey.binary width prime with hpsdef
  have hpslen : ps.length = width := by rw [hpsdef, SignedSortKey.binary_length]
  have hpsval : value ps = prime := by
    rw [hpsdef, SignedSortKey.binary_value width prime (by omega)]
  have hnz : value (FinalPrimeRow.negWord zs) + value zs + 1 = 2 ^ width := by
    have h := FinalPrimeRow.negWord_value zs
    rwa [hzs] at h
  have hw : ps.length = (FinalPrimeRow.negWord zs).length := by
    rw [hpslen, FinalPrimeRow.negWord_length, hzs]
  set t := Add.sum ps (FinalPrimeRow.negWord zs) true with htdef
  have htlen : t.length = width := by rw [htdef, Add.sum_length _ _ _ hw, hpslen]
  have htlt : value t < 2 ^ width := by
    have h := value_lt t
    rwa [htlen] at h
  have hsum := Add.sum_value ps (FinalPrimeRow.negWord zs) true hw
  rw [hpslen, hpsval, ← htdef] at hsum
  have htval : value t = prime - value zs := by
    cases hov : Add.overflow ps (FinalPrimeRow.negWord zs) true <;>
      rw [hov] at hsum <;>
      simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one,
        Nat.add_zero] at hsum <;> omega
  have hlt2 : value t < 2 * prime := by omega
  have hcore := FinalPrimeModular.reduce_core prime width t htlen hp hlt2
  have hgoal : FinalPrimeRow.residueOf (negState prime width zs) =
      (if Add.overflow t (FinalPrimeRow.negWord ps) true then
        value (Add.sum t (FinalPrimeRow.negWord ps) true) else value t) := by
    simp only [FinalPrimeRow.residueOf, negState, ← hpsdef, ← htdef]
    split <;> rfl
  rw [hgoal, hcore, htval]

theorem negState_length (prime width : ℕ) (zs : List Bool) (hzs : zs.length = width) :
    (negState prime width zs).1.length = width ∧ (negState prime width zs).2.1.length = width := by
  have hw : (SignedSortKey.binary width prime).length = (FinalPrimeRow.negWord zs).length := by
    rw [SignedSortKey.binary_length, FinalPrimeRow.negWord_length, hzs]
  have h1 : (Add.sum (SignedSortKey.binary width prime) (FinalPrimeRow.negWord zs) true).length =
      width := by rw [Add.sum_length _ _ _ hw, SignedSortKey.binary_length]
  refine ⟨h1, ?_⟩
  have hw2 : (Add.sum (SignedSortKey.binary width prime) (FinalPrimeRow.negWord zs) true).length =
      (FinalPrimeRow.negWord (SignedSortKey.binary width prime)).length := by
    rw [h1, FinalPrimeRow.negWord_length, SignedSortKey.binary_length]
  show (Add.sum (Add.sum (SignedSortKey.binary width prime) (FinalPrimeRow.negWord zs) true)
    (FinalPrimeRow.negWord (SignedSortKey.binary width prime)) true).length = width
  rw [Add.sum_length _ _ _ hw2, h1]

end NearCubicWires.RepairOrdinary.FinalPrimeNegate
