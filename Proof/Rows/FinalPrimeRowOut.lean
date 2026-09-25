import Proof.Rows.FinalPrimeZeroTest

/-! # The row output stage: select the residue and test it for zero, in one pass

After an accumulation the residue is still split across `T`, `U` and the flag
`F`.  Materialising it (`FinalPrimeResidue`) and then testing it for zero
(`FinalPrimeZeroTest`) would be two passes with a head reset in between — a
fourth mask, for no reason.

`machine : Machine 4 10` fuses them: one left-to-right sweep writes the
selected residue word into `D` *and* accumulates "a one has been seen" in the
finite control, emitting the verdict into the one-cell result tape `R` at the
terminating marker.  `2 * L + 2` steps, no head reset, and the composition
that uses it therefore needs exactly one docking.

Tapes: `0 = D` (the first candidate, overwritten with the residue),
`1 = S` (the second candidate), `2 = F` (the decisive carry, head pinned at 0),
`3 = R` (the verdict cell, head pinned at 0).
-/
namespace NearCubicWires.RepairOrdinary.FinalPrimeRowOut
open LocalBitMultitape RecoveryExecution RadixSemantics ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def markerState (sel nz : Bool) : Fin 10 :=
  if sel then (if nz then 5 else 4) else (if nz then 3 else 2)
def bitState (sel nz : Bool) : Fin 10 :=
  if sel then (if nz then 9 else 8) else (if nz then 7 else 6)
def selOf (q : Fin 10) : Bool := decide (2 ≤ (q.val - 2) % 4)
def nzOf (q : Fin 10) : Bool := decide ((q.val - 2) % 2 = 1)


def mv : Fin 4 → HeadMove := fun i => if i.val ≤ 1 then .right else .stay

def machine : Machine 4 10 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q scanned =>
    if q.val = 0 then some ⟨markerState (scanned 2) false, fun _ => none, fun _ => .stay⟩
    else if q.val = 1 then none
    else if q.val < 6 then
      (if scanned 0 then some ⟨bitState (selOf q) (nzOf q), fun _ => none, mv⟩
        else some ⟨1, fun i => if i.val = 3 then some (!nzOf q) else none, mv⟩)
    else
      some ⟨markerState (selOf q) (nzOf q || (if selOf q then scanned 1 else scanned 0)),
        fun i => if i.val = 0 then some (if selOf q then scanned 1 else scanned 0) else none, mv⟩

def cfg (q : Fin 10) (D S F R : List Bool) (pos : ℕ) : Configuration 4 10 :=
  ⟨q, ![pos, pos, 0, 0], ![D, S, F, R]⟩

theorem write_mid (pre tail : List Bool) (old v : Bool) :
    writeTapeBit (pre ++ old :: tail) pre.length v = pre ++ v :: tail := by
  induction pre with
  | nil => rfl
  | cons b pre ih => simpa [writeTapeBit] using congrArg (List.cons b) ih

theorem entry_step (D S F R : List Bool) (sel : Bool) (hF : readTapeBit F 0 = sel) :
    step machine (cfg 0 D S F R 0) = some (cfg (markerState sel false) D S F R 0) := by
  simp [step, machine, cfg, Configuration.scanned, hF]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem marker_step (sel nz : Bool) (D S F R : List Bool) (pos : ℕ)
    (hD : readTapeBit D pos = true) :
    step machine (cfg (markerState sel nz) D S F R pos) =
      some (cfg (bitState sel nz) D S F R (pos + 1)) := by
  cases sel <;> cases nz <;>
    simp [step, machine, cfg, Configuration.scanned, hD, markerState, bitState, selOf, nzOf] <;>
    apply configuration_ext
  all_goals first
    | rfl
    | (funext i; fin_cases i <;> simp [applyAction, HeadMove.apply, mv])

theorem halt_step (sel nz : Bool) (D S F R : List Bool) (pos : ℕ)
    (hD : readTapeBit D pos = false) :
    step machine (cfg (markerState sel nz) D S F R pos) =
      some (cfg 1 D S F (writeTapeBit R 0 (!nz)) (pos + 1)) := by
  cases sel <;> cases nz <;>
    simp [step, machine, cfg, Configuration.scanned, hD, markerState, selOf, nzOf] <;>
    apply configuration_ext
  all_goals first
    | rfl
    | (funext i; fin_cases i <;> simp [applyAction, HeadMove.apply, mv])

theorem bit_step (sel nz d s : Bool) (aD tD aS tS F R : List Bool)
    (_hS : aS.length = aD.length)
    (hDr : readTapeBit (aD ++ d :: tD) aD.length = d)
    (hSr : readTapeBit (aS ++ s :: tS) aD.length = s) :
    step machine (cfg (bitState sel nz) (aD ++ d :: tD) (aS ++ s :: tS) F R aD.length) =
      some (cfg (markerState sel (nz || (if sel then s else d)))
        (aD ++ (if sel then s else d) :: tD) (aS ++ s :: tS) F R (aD.length + 1)) := by
  have wD : ∀ v, writeTapeBit (aD ++ d :: tD) aD.length v = aD ++ v :: tD :=
    fun v => write_mid aD tD d v
  cases sel <;> cases nz <;>
    simp [step, machine, cfg, Configuration.scanned, hDr, hSr, markerState, bitState,
      selOf, nzOf] <;>
    apply configuration_ext
  all_goals first
    | rfl
    | (funext i; fin_cases i <;> simp [applyAction, HeadMove.apply, mv, wD])

theorem sweep_timed (sel : Bool) :
    ∀ (ds ss : List Bool), ss.length = ds.length →
      ∀ (aD aS : List Bool), aS.length = aD.length → ∀ (F R : List Bool) (nz : Bool),
        Timed machine (2 * ds.length + 1)
          (cfg (markerState sel nz) (aD ++ frame ds) (aS ++ frame ss) F R aD.length)
          (cfg 1 (aD ++ frame (if sel then ss else ds)) (aS ++ frame ss) F
            (writeTapeBit R 0 (!FinalPrimeZeroTest.orAll nz (if sel then ss else ds)))
            (aD.length + 2 * ds.length + 1)) := by
  intro ds
  induction ds with
  | nil =>
    intro ss hss aD aS _haS F R nz
    have hs : ss = [] := List.length_eq_zero_iff.mp (by simpa using hss)
    subst hs
    have hread : readTapeBit (aD ++ frame ([] : List Bool)) aD.length = false := by
      simpa [frame] using Streaming.read_append aD ([] : List Bool) false
    have hstep := halt_step sel nz (aD ++ frame ([] : List Bool)) (aS ++ frame ([] : List Bool))
      F R aD.length hread
    have h := Timed.single (p := machine) (by cases sel <;> cases nz <;> rfl) hstep
    simpa [frame, FinalPrimeZeroTest.orAll] using h
  | cons d ds ih =>
    intro ss hss aD aS haS F R nz
    cases ss with
    | nil => simp at hss
    | cons s ss =>
      have hss' : ss.length = ds.length := by simpa using hss
      have hmark : readTapeBit (aD ++ frame (d :: ds)) aD.length = true := by
        simpa [frame, List.append_assoc] using Streaming.read_append aD (d :: frame ds) true
      have hfirst := marker_step sel nz (aD ++ frame (d :: ds)) (aS ++ frame (s :: ss)) F R
        aD.length hmark
      have hreadD : readTapeBit ((aD ++ [true]) ++ d :: frame ds) (aD ++ [true]).length = d :=
        Streaming.read_append (aD ++ [true]) (frame ds) d
      have hreadS : readTapeBit ((aS ++ [true]) ++ s :: frame ss) (aD ++ [true]).length = s := by
        have h := Streaming.read_append (aS ++ [true]) (frame ss) s
        simp only [List.length_append, List.length_cons, List.length_nil, haS] at h ⊢
        exact h
      have hsecond : step machine (cfg (bitState sel nz) (aD ++ frame (d :: ds))
          (aS ++ frame (s :: ss)) F R (aD.length + 1)) =
            some (cfg (markerState sel (nz || (if sel then s else d)))
              ((aD ++ [true, if sel then s else d]) ++ frame ds)
              ((aS ++ [true, s]) ++ frame ss) F R (aD.length + 2)) := by
        have h := bit_step sel nz d s (aD ++ [true]) (frame ds) (aS ++ [true]) (frame ss) F R
          (by simp [haS]) hreadD hreadS
        simp only [List.length_append, List.length_cons, List.length_nil] at h
        simpa [frame, List.append_assoc] using h
      have htail := ih ss hss' (aD ++ [true, if sel then s else d]) (aS ++ [true, s])
        (by simp [haS]) F R (nz || (if sel then s else d))
      have hlen : (aD ++ [true, if sel then s else d]).length = aD.length + 2 := by simp
      rw [hlen] at htail
      have hjoin := (Timed.single (p := machine) (by cases sel <;> cases nz <;> rfl) hfirst).trans
        ((Timed.single (p := machine) (by cases sel <;> cases nz <;> rfl) hsecond).trans htail)
      have htime : 1 + (1 + (2 * ds.length + 1)) = 2 * (d :: ds).length + 1 := by simp; omega
      have hpos : aD.length + 2 + 2 * ds.length + 1 = aD.length + 2 * (d :: ds).length + 1 := by
        simp; omega
      rw [htime, hpos] at hjoin
      have hif : (if sel then s :: ss else d :: ds) =
          (if sel then s else d) :: (if sel then ss else ds) := by cases sel <;> rfl
      rw [hif]
      simpa [FinalPrimeZeroTest.orAll, frame, List.append_assoc] using hjoin

/-- One pass materialises the residue on `D` and delivers the zero verdict on
`R`.  `2 * L + 2` steps. -/
theorem rowOut_step (sel : Bool) (ds ss F R : List Bool) (hss : ss.length = ds.length)
    (hF : readTapeBit F 0 = sel) :
    Step machine (2 * ds.length + 2) (![0, 0, 0, 0] : Fin 4 → ℕ)
      (![frame ds, frame ss, F, R] : Fin 4 → List Bool)
      (![2 * ds.length + 1, 2 * ds.length + 1, 0, 0] : Fin 4 → ℕ)
      (![frame (if sel then ss else ds), frame ss, F,
        writeTapeBit R 0 (decide (value (if sel then ss else ds) = 0))] : Fin 4 → List Bool) := by
  have hentry := entry_step (frame ds) (frame ss) F R sel hF
  have hsweep := sweep_timed sel ds ss hss [] [] rfl F R false
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at hsweep
  have hall := (Timed.single (p := machine) (by rfl) hentry).trans hsweep
  have htime : 1 + (2 * ds.length + 1) = 2 * ds.length + 2 := by omega
  rw [htime] at hall
  obtain ⟨r, hr, hf, hs⟩ := hall.run (by rfl)
  refine Step.of_run (r := r) ?_ ?_ ?_
  · have hc : cfg 0 (frame ds) (frame ss) F R 0 =
        (⟨machine.start, (![0, 0, 0, 0] : Fin 4 → ℕ),
          (![frame ds, frame ss, F, R] : Fin 4 → List Bool)⟩ : Configuration 4 10) := by
      apply configuration_ext
      · rfl
      · rfl
      · rfl
    rw [hc] at hr
    exact hr
  · rw [hf]; funext i; fin_cases i <;> rfl
  · rw [hf, FinalPrimeZeroTest.orAll_value]; funext i; fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.FinalPrimeRowOut
