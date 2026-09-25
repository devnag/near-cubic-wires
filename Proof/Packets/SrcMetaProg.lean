import Proof.Packets.SrcMetaAsm

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceStart.MetaProg
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation NearCubicWires.SourceStart.MetaTM NearCubicWires.SourceStart.Regs NearCubicWires.SourceStart.MetaAsm
noncomputable section

theorem padpad (C D : ℕ) (w : List Bool) (h : C ≤ D) :
    ZeroPadding.pad D (ZeroPadding.pad C w) = ZeroPadding.pad D w := by
  simp only [ZeroPadding.pad, List.length_append, List.length_replicate, List.append_assoc]
  rw [← List.replicate_add]
  congr 2
  omega

theorem pad_false1 (R : ℕ) (hR : 1 ≤ R) : ZeroPadding.pad R [false] = List.replicate R false := by
  obtain ⟨k, rfl⟩ : ∃ k, R = k + 1 := ⟨R - 1, by omega⟩
  simp [ZeroPadding.pad, List.replicate_succ]

theorem pad_blank (R : ℕ) : ZeroPadding.pad R (List.replicate R false) = List.replicate R false := by
  simp [ZeroPadding.pad]

theorem addCases_val_lt {α : Type} {a : ℕ} (f : Fin a → α) (g : Fin 1 → α) (j : Fin (a + 1)) (h : j.val < a) :
    Fin.addCases f g j = f ⟨j.val, h⟩ :=
  Fin.addCases_left (n := 1) ⟨j.val, h⟩

theorem addCases_val_eq {α : Type} {a : ℕ} (f : Fin a → α) (g : Fin 1 → α) (j : Fin (a + 1)) (h : j.val = a) :
    Fin.addCases f g j = g 0 := by
  have e : j = Fin.natAdd a (0 : Fin 1) := Fin.ext (by simp [h])
  rw [e, Fin.addCases_right]

/-! ## 1. The tracking invariant and one stage -/

/-- **Register tracking**: registers `< G` hold `pad R` of their tracked words; every tape from `f` on is blank. -/
def Trk (R G : ℕ) {NL : ℕ} (E : Fin NL → List Bool) (val : ℕ → Option (List Bool)) (f : ℕ) : Prop :=
  G ≤ f ∧ (∀ x : Fin NL, x.val < G → ∀ w, val x.val = some w → E x = ZeroPadding.pad R w) ∧
    (∀ x : Fin NL, f ≤ x.val → E x = List.replicate R false)

/-- **One stage at the tracking level.** -/
theorem trk_stage {NL R G n st c : ℕ} {M : Machine n st} {tin tout : Fin n → List Bool}
    (h : Step M c (fun _ => 0) tin (fun _ => 0) tout)
    (nm : Fin n → Option (Fin NL)) (f : ℕ) (hs : f + n ≤ NL)
    (hinj : ∀ i j r, nm i = some r → nm j = some r → i = j) (hG : ∀ j r, nm j = some r → r.val < G)
    {E : Fin NL → List Bool} {val : ℕ → Option (List Bool)} (hT : Trk R G E val f)
    (hin : ∀ j r, nm j = some r → ∃ w, val r.val = some w ∧ ZeroPadding.pad R w = ZeroPadding.pad R (tin j))
    (hsc : ∀ j, nm j = none → ZeroPadding.pad R (tin j) = List.replicate R false)
    (val' : ℕ → Option (List Bool))
    (hv : ∀ x : Fin NL, x.val < G → ∀ w, val' x.val = some w →
      (∃ j, nm j = some x ∧ ZeroPadding.pad R w = ZeroPadding.pad R (tout j)) ∨ ((∀ j, nm j ≠ some x) ∧ val x.val = some w)) :
    ∃ E', Step (RecoveryFocus.machine (nslot nm f hs) M) c (fun _ => 0) E (fun _ => 0) E' ∧ Trk R G E' val' (f + n) := by
  obtain ⟨hGf, hreg, hfr⟩ := hT
  obtain ⟨E', st', o1, o2, o3⟩ := nstage h nm f hs hinj (fun j r e => by have := hG j r e; omega) E
    (fun j r e => by
      obtain ⟨w, hw, hp⟩ := hin j r e
      rw [hreg r (hG j r e) w hw, hp]) hsc hfr
  refine ⟨E', st', by omega, ?_, o3⟩
  intro x hx w e
  rcases hv x hx w e with ⟨j, hj, hp⟩ | ⟨hn, hw⟩
  · rw [o1 j x hj, hp]
  · rw [o2 x (by omega) hn]; exact hreg x hx w hw

/-! ## 2. One or two named registers -/

/-- One named local tape `io ↦ o`. -/
def nm1 {NL n : ℕ} (o : Fin NL) (io : ℕ) (j : Fin n) : Option (Fin NL) := if j.val = io then some o else none

/-- Two named local tapes `ia ↦ a`, `ib ↦ b`. -/
def nm2 {NL n : ℕ} (a : Fin NL) (ia : ℕ) (b : Fin NL) (ib : ℕ) (j : Fin n) : Option (Fin NL) :=
  if j.val = ia then some a else if j.val = ib then some b else none

theorem nm1_cases {NL n : ℕ} (o : Fin NL) (io : ℕ) (j : Fin n) (r : Fin NL) (h : nm1 o io j = some r) :
    j.val = io ∧ r = o := by
  unfold nm1 at h
  by_cases c : j.val = io
  · rw [if_pos c] at h; exact ⟨c, (Option.some.inj h).symm⟩
  · rw [if_neg c] at h; exact absurd h (by simp)

theorem nm2_cases {NL n : ℕ} (a : Fin NL) (ia : ℕ) (b : Fin NL) (ib : ℕ) (j : Fin n) (r : Fin NL)
    (h : nm2 a ia b ib j = some r) : (j.val = ia ∧ r = a) ∨ (j.val = ib ∧ r = b) := by
  unfold nm2 at h
  by_cases c1 : j.val = ia
  · rw [if_pos c1] at h; exact Or.inl ⟨c1, (Option.some.inj h).symm⟩
  · rw [if_neg c1] at h
    by_cases c2 : j.val = ib
    · rw [if_pos c2] at h; exact Or.inr ⟨c2, (Option.some.inj h).symm⟩
    · rw [if_neg c2] at h; exact absurd h (by simp)

theorem nm2_none {NL n : ℕ} (a : Fin NL) (ia : ℕ) (b : Fin NL) (ib : ℕ) (j : Fin n) (h : nm2 a ia b ib j = none) :
    j.val ≠ ia ∧ j.val ≠ ib := by
  unfold nm2 at h
  by_cases c1 : j.val = ia
  · rw [if_pos c1] at h; exact absurd h (by simp)
  · rw [if_neg c1] at h
    by_cases c2 : j.val = ib
    · rw [if_pos c2] at h; exact absurd h (by simp)
    · exact ⟨c1, c2⟩

/-- **A stage with one named register** `o` (its entry word tracked, its exit word `wo`). -/
theorem trk1 {NL R G n st c : ℕ} {M : Machine n st} {tin tout : Fin n → List Bool}
    (h : Step M c (fun _ => 0) tin (fun _ => 0) tout) (o : Fin NL) (io : ℕ) (hio : io < n) (hoG : o.val < G)
    (f : ℕ) (hs : f + n ≤ NL) {E : Fin NL → List Bool} {val : ℕ → Option (List Bool)} (hT : Trk R G E val f)
    (hO : ∃ w, val o.val = some w ∧ ZeroPadding.pad R w = ZeroPadding.pad R (tin ⟨io, hio⟩))
    (hsc : ∀ j : Fin n, j.val ≠ io → ZeroPadding.pad R (tin j) = List.replicate R false)
    (wo : List Bool) (hwo : ZeroPadding.pad R wo = ZeroPadding.pad R (tout ⟨io, hio⟩)) :
    ∃ E', Step (RecoveryFocus.machine (nslot (nm1 o io) f hs) M) c (fun _ => 0) E (fun _ => 0) E' ∧
      Trk R G E' (Function.update val o.val (some wo)) (f + n) := by
  refine trk_stage h _ f hs ?_ ?_ hT ?_ ?_ _ ?_
  · intro i j r hi hj
    exact Fin.ext ((nm1_cases o io i r hi).1.trans (nm1_cases o io j r hj).1.symm)
  · intro j r e
    rw [(nm1_cases o io j r e).2]; exact hoG
  · intro j r e
    obtain ⟨c1, rfl⟩ := nm1_cases o io j r e
    have ej : j = ⟨io, hio⟩ := Fin.ext c1
    rw [ej]; exact hO
  · intro j e
    apply hsc
    intro c1
    unfold nm1 at e
    rw [if_pos c1] at e
    exact absurd e (by simp)
  · intro x hx w e
    by_cases hxo : x.val = o.val
    · have ex : x = o := Fin.ext hxo
      subst ex
      rw [Function.update_self] at e
      left
      refine ⟨⟨io, hio⟩, by simp [nm1], ?_⟩
      rw [← Option.some.inj e]; exact hwo
    · rw [Function.update_of_ne hxo] at e
      right
      refine ⟨fun j hj => hxo ?_, e⟩
      rw [(nm1_cases o io j x hj).2]

/-- **A stage with two named registers** `a` (exit word `wa`, `none` = forgotten) and `b` (exit word `wb`). -/
theorem trk2 {NL R G n st c : ℕ} {M : Machine n st} {tin tout : Fin n → List Bool}
    (h : Step M c (fun _ => 0) tin (fun _ => 0) tout) (a b : Fin NL) (ia ib : ℕ) (hia : ia < n) (hib : ib < n)
    (hab : a ≠ b) (haG : a.val < G) (hbG : b.val < G) (f : ℕ) (hs : f + n ≤ NL)
    {E : Fin NL → List Bool} {val : ℕ → Option (List Bool)} (hT : Trk R G E val f)
    (hA : ∃ w, val a.val = some w ∧ ZeroPadding.pad R w = ZeroPadding.pad R (tin ⟨ia, hia⟩))
    (hB : ∃ w, val b.val = some w ∧ ZeroPadding.pad R w = ZeroPadding.pad R (tin ⟨ib, hib⟩))
    (hsc : ∀ j : Fin n, j.val ≠ ia → j.val ≠ ib → ZeroPadding.pad R (tin j) = List.replicate R false)
    (wa : Option (List Bool)) (hwa : ∀ w, wa = some w → ZeroPadding.pad R w = ZeroPadding.pad R (tout ⟨ia, hia⟩))
    (wb : List Bool) (hwb : ZeroPadding.pad R wb = ZeroPadding.pad R (tout ⟨ib, hib⟩)) (hiab : ia ≠ ib) :
    ∃ E', Step (RecoveryFocus.machine (nslot (nm2 a ia b ib) f hs) M) c (fun _ => 0) E (fun _ => 0) E' ∧
      Trk R G E' (Function.update (Function.update val a.val wa) b.val (some wb)) (f + n) := by
  have hv : a.val ≠ b.val := fun e => hab (Fin.ext e)
  refine trk_stage h _ f hs ?_ ?_ hT ?_ ?_ _ ?_
  · intro i j r hi hj
    rcases nm2_cases a ia b ib i r hi with ⟨c1, e1⟩ | ⟨c2, e1⟩
    · rcases nm2_cases a ia b ib j r hj with ⟨d1, _⟩ | ⟨_, e2⟩
      · exact Fin.ext (c1.trans d1.symm)
      · exact absurd (e1.symm.trans e2) hab
    · rcases nm2_cases a ia b ib j r hj with ⟨_, e2⟩ | ⟨d2, _⟩
      · exact absurd (e2.symm.trans e1) hab
      · exact Fin.ext (c2.trans d2.symm)
  · intro j r e
    rcases nm2_cases a ia b ib j r e with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact haG
    · exact hbG
  · intro j r e
    rcases nm2_cases a ia b ib j r e with ⟨c1, rfl⟩ | ⟨c2, rfl⟩
    · have ej : j = ⟨ia, hia⟩ := Fin.ext c1
      rw [ej]; exact hA
    · have ej : j = ⟨ib, hib⟩ := Fin.ext c2
      rw [ej]; exact hB
  · intro j e
    obtain ⟨c1, c2⟩ := nm2_none a ia b ib j e
    exact hsc j c1 c2
  · intro x hx w e
    by_cases hxb : x.val = b.val
    · have ex : x = b := Fin.ext hxb
      subst ex
      rw [Function.update_self] at e
      left
      refine ⟨⟨ib, hib⟩, ?_, ?_⟩
      · simp [nm2, Ne.symm hiab]
      · rw [← Option.some.inj e]; exact hwb
    · rw [Function.update_of_ne hxb] at e
      by_cases hxa : x.val = a.val
      · have ex : x = a := Fin.ext hxa
        subst ex
        rw [Function.update_self] at e
        left
        exact ⟨⟨ia, hia⟩, by simp [nm2], hwa w e⟩
      · rw [Function.update_of_ne hxa] at e
        right
        refine ⟨fun j hj => ?_, e⟩
        rcases nm2_cases a ia b ib j x hj with ⟨_, e2⟩ | ⟨_, e2⟩
        · exact hxa (by rw [e2])
        · exact hxb (by rw [e2])

/-! ## 3. The stage kinds -/

def fixM {NL : ℕ} (bits : List Bool) (o : Fin NL) (f : ℕ) (hs : f + 2 ≤ NL) :=
  RecoveryFocus.machine (nslot (nm1 (n := 2) o 0) f hs) (HierarchyFixedWord.machine bits)

theorem fix_trk {NL R G : ℕ} (bits : List Bool) (o : Fin NL) (hoG : o.val < G) (f : ℕ) (hs : f + 2 ≤ NL)
    {E : Fin NL → List Bool} {val : ℕ → Option (List Bool)} (hT : Trk R G E val f) (hO : val o.val = some []) :
    ∃ E', Step (fixM bits o f hs) (2*bits.length+2) (fun _ => 0) E (fun _ => 0) E' ∧
      Trk R G E' (Function.update val o.val (some bits)) (f + 2) :=
  trk1 (fixed_local bits) o 0 (by decide) hoG f hs hT ⟨[], hO, rfl⟩
    (by intro j _; exact Stages.pad_nil R) bits rfl

/-- `1^b ↦ frame 1^b` from register `src` onto `o` (PG `FrameUnary`, masked). -/
def fruM {NL : ℕ} (src o : Fin NL) (f : ℕ) (hs : f + 3 ≤ NL) :=
  RecoveryFocus.machine (nslot (nm2 (n := 3) src 0 o 1) f hs)
    (MaskedReset.machine PacketsGlue.FrameUnary.machine (fun _ => true))

theorem fru_trk {NL R G : ℕ} (b : ℕ) (src o : Fin NL) (hso : src ≠ o) (hsG : src.val < G) (hoG : o.val < G)
    (f : ℕ) (hs : f + 3 ≤ NL) {E : Fin NL → List Bool} {val : ℕ → Option (List Bool)} (hT : Trk R G E val f)
    (hS : val src.val = some (List.replicate b true)) (hO : val o.val = some []) :
    ∃ E', Step (fruM src o f hs) (2*(2*b+1)+2) (fun _ => 0) E (fun _ => 0) E' ∧
      Trk R G E' (Function.update val o.val (some (RepairOrdinary.frame (List.replicate b true)))) (f + 3) := by
  obtain ⟨k, hk⟩ := frameU_local b
  have r := trk2 hk src o 0 1 (by decide) (by decide) hso hsG hoG f hs hT ⟨_, hS, rfl⟩ ⟨[], hO, rfl⟩ (by
    intro j c0 c1
    rw [addCases_val_eq _ _ j (by have := j.isLt; omega)]
    exact Stages.pad_nil R) (val src.val) (by
      intro w e
      rw [hS] at e
      rw [← Option.some.inj e]; rfl) _ rfl (by decide)
  rwa [Function.update_eq_self] at r

def zerM {NL : ℕ} (src o : Fin NL) (f : ℕ) (hs : f + 3 ≤ NL) :=
  RecoveryFocus.machine (nslot (nm2 (n := 3) src 0 o 1) f hs) (MaskedReset.machine zerosM (fun _ => true))

theorem zer_trk {NL R G : ℕ} (b : ℕ) (src o : Fin NL) (hso : src ≠ o) (hsG : src.val < G) (hoG : o.val < G)
    (f : ℕ) (hs : f + 3 ≤ NL) {E : Fin NL → List Bool} {val : ℕ → Option (List Bool)} (hT : Trk R G E val f)
    (hS : val src.val = some (List.replicate b true)) (hO : val o.val = some []) :
    ∃ E', Step (zerM src o f hs) (2*(2*b+1)+2) (fun _ => 0) E (fun _ => 0) E' ∧
      Trk R G E' (Function.update val o.val (some (RepairOrdinary.frame (List.replicate b false)))) (f + 3) := by
  obtain ⟨k, hk⟩ := zeros_local b
  have r := trk2 hk src o 0 1 (by decide) (by decide) hso hsG hoG f hs hT ⟨_, hS, rfl⟩ ⟨[], hO, rfl⟩ (by
    intro j c0 c1
    rw [addCases_val_eq _ _ j (by have := j.isLt; omega)]
    exact Stages.pad_nil R) (val src.val) (by
      intro w e
      rw [hS] at e
      rw [← Option.some.inj e]; rfl) _ rfl (by decide)
  rwa [Function.update_eq_self] at r

def cntM {NL : ℕ} (src o : Fin NL) (f : ℕ) (hs : f + 10 ≤ NL) :=
  RecoveryFocus.machine (nslot (nm2 (n := 10) src 0 o 5) f hs) CloseoutRowsCountBinary.machine

theorem cnt_trk {NL R G : ℕ} (m : ℕ) (src o : Fin NL) (hso : src ≠ o) (hsG : src.val < G) (hoG : o.val < G)
    (f : ℕ) (hs : f + 10 ≤ NL) {E : Fin NL → List Bool} {val : ℕ → Option (List Bool)} (hT : Trk R G E val f)
    (hS : val src.val = some (List.replicate m true)) (hO : val o.val = some []) :
    ∃ E', Step (cntM src o f hs) (CloseoutRowsCountBinary.budget m) (fun _ => 0) E (fun _ => 0) E' ∧
      Trk R G E' (Function.update (Function.update val src.val none) o.val
        (some (RepairOrdinary.frame (CloseoutRowsCountBinary.bits m)))) (f + 10) := by
  obtain ⟨out, h, h5⟩ := count_local m
  refine trk2 h src o 0 5 (by decide) (by decide) hso hsG hoG f hs hT ⟨_, hS, rfl⟩ ⟨[], hO, rfl⟩ ?_ none
    (by intro w e; exact absurd e (by simp)) _ (by rw [← h5]; rfl) (by decide)
  intro j c0 _
  have e : CloseoutRowsCountBinary.input m j = [] := by
    unfold CloseoutRowsCountBinary.input
    rw [if_neg (fun h => c0 (by rw [h]; rfl))]
  rw [e]; exact Stages.pad_nil R

def natM {NL : ℕ} (src o : Fin NL) (f : ℕ) (hs : f + 22 ≤ NL) :=
  RecoveryFocus.machine (nslot (nm2 (n := 22) src 0 o 20) f hs) CloseoutRowsEstimatorParity.Natural.machine

theorem nat_trk {NL R G : ℕ} (q m : ℕ) (hm : m ≤ q) (hcap : CloseoutRowsEstimatorParity.Capacity.value q ≤ R)
    (src o : Fin NL) (hso : src ≠ o) (hsG : src.val < G) (hoG : o.val < G)
    (f : ℕ) (hs : f + 22 ≤ NL) {E : Fin NL → List Bool} {val : ℕ → Option (List Bool)} (hT : Trk R G E val f)
    (hS : val src.val = some (List.replicate m true)) (hO : val o.val = some []) :
    ∃ E', Step (natM src o f hs) (CloseoutRowsEstimatorParity.Natural.budget m) (fun _ => 0) E (fun _ => 0) E' ∧
      Trk R G E' (Function.update (Function.update val src.val none) o.val
        (some (RepairOrdinary.frame (natWord m)))) (f + 22) := by
  obtain ⟨out, h, h20⟩ := nat_local q m hm
  refine trk2 h src o 0 20 (by decide) (by decide) hso hsG hoG f hs hT ⟨_, hS, ?_⟩ ⟨[], hO, ?_⟩ ?_ none
    (by intro w e; exact absurd e (by simp)) _ (by show _ = ZeroPadding.pad R (out 20); rw [h20, padpad _ _ _ hcap]) (by decide)
  · show _ = ZeroPadding.pad R (ZeroPadding.pad _ (CloseoutRowsEstimatorParity.Natural.source m ⟨0, _⟩))
    rw [padpad _ _ _ hcap]; rfl
  · show _ = ZeroPadding.pad R (ZeroPadding.pad _ (CloseoutRowsEstimatorParity.Natural.source m ⟨20, _⟩))
    rw [padpad _ _ _ hcap]; rfl
  · intro j c0 _
    show ZeroPadding.pad R (ZeroPadding.pad _ (CloseoutRowsEstimatorParity.Natural.source m j)) = _
    have e : CloseoutRowsEstimatorParity.Natural.source m j = [] := by
      unfold CloseoutRowsEstimatorParity.Natural.source
      rw [if_neg (fun h => c0 (by rw [h]; rfl))]
    rw [e, padpad _ _ _ hcap]; exact Stages.pad_nil R

/-! ## 4. The two assembly phases -/

def nmA {NL : ℕ} (m pb : ℕ) (hpb : pb + m ≤ NL) (out : Fin NL) (j : Fin (m + 2 + 1)) : Option (Fin NL) :=
  if h : j.val < m then some ⟨pb + j.val, by omega⟩ else if j.val = m then some out else none

def phAM {NL : ℕ} (m pb : ℕ) (hpb : pb + m ≤ NL) (out : Fin NL) (f : ℕ) (hs : f + (m + 2 + 1) ≤ NL) :=
  RecoveryFocus.machine (nslot (nmA m pb hpb out) f hs) (MaskedReset.machine (innerA m).2 (fun _ => true))

/-- Phase A's exit tracking: the output tracked, the pieces forgotten. -/
def valA (m pb outv : ℕ) (word : List Bool) (val : ℕ → Option (List Bool)) : ℕ → Option (List Bool) := fun i =>
  if i = outv then some word else if pb ≤ i ∧ i < pb + m then none else val i

theorem phA_trk {NL R G : ℕ} (hR : 1 ≤ R) (m pb : ℕ) (hpbG : pb + m ≤ G) (hpb : pb + m ≤ NL) (out : Fin NL)
    (hout : out.val < pb ∨ pb + m ≤ out.val) (hoG : out.val < G) (w : Fin m → List Bool)
    (f : ℕ) (hs : f + (m + 2 + 1) ≤ NL) {E : Fin NL → List Bool} {val : ℕ → Option (List Bool)} (hT : Trk R G E val f)
    (hP : ∀ k : Fin m, val (pb + k.val) = some (RepairOrdinary.frame (w k))) (hO : val out.val = some []) :
    ∃ E', Step (phAM m pb hpb out f hs) (costA m w) (fun _ => 0) E (fun _ => 0) E' ∧
      Trk R G E' (valA m pb out.val ((List.finRange m).flatMap (fun i => body false (w i)) ++ [false]) val) (f + (m + 2 + 1)) := by
  obtain ⟨tout, h, ho⟩ := phaseA_run m w
  have tinl : ∀ j : Fin (m + 2 + 1), (hj : j.val < m + 2) →
      Fin.addCases (tinA m w) (fun _ : Fin 1 => ([] : List Bool)) j = tinA m w ⟨j.val, hj⟩ :=
    fun j hj => addCases_val_lt _ _ j hj
  refine trk_stage h _ f hs ?_ ?_ hT ?_ ?_ _ ?_
  · intro i j r hi hj
    unfold nmA at hi hj
    by_cases c1 : i.val < m <;> by_cases c2 : j.val < m
    · rw [dif_pos c1] at hi; rw [dif_pos c2] at hj
      have e := congrArg Fin.val ((Option.some.inj hi).trans (Option.some.inj hj).symm)
      exact Fin.ext (by simpa using e)
    · rw [dif_pos c1] at hi; rw [dif_neg c2] at hj
      by_cases c3 : j.val = m
      · rw [if_pos c3] at hj
        have e := congrArg Fin.val ((Option.some.inj hi).trans (Option.some.inj hj).symm)
        simp only at e
        omega
      · rw [if_neg c3] at hj; exact absurd hj (by simp)
    · rw [dif_neg c1] at hi; rw [dif_pos c2] at hj
      by_cases c3 : i.val = m
      · rw [if_pos c3] at hi
        have e := congrArg Fin.val ((Option.some.inj hi).trans (Option.some.inj hj).symm)
        simp only at e
        omega
      · rw [if_neg c3] at hi; exact absurd hi (by simp)
    · rw [dif_neg c1] at hi; rw [dif_neg c2] at hj
      by_cases c3 : i.val = m
      · by_cases c4 : j.val = m
        · exact Fin.ext (c3.trans c4.symm)
        · rw [if_neg c4] at hj; exact absurd hj (by simp)
      · rw [if_neg c3] at hi; exact absurd hi (by simp)
  · intro j r e
    unfold nmA at e
    by_cases c1 : j.val < m
    · rw [dif_pos c1] at e
      rw [← Option.some.inj e]
      show pb + j.val < G
      omega
    · rw [dif_neg c1] at e
      by_cases c2 : j.val = m
      · rw [if_pos c2] at e; rw [← Option.some.inj e]; exact hoG
      · rw [if_neg c2] at e; exact absurd e (by simp)
  · intro j r e
    unfold nmA at e
    by_cases c1 : j.val < m
    · rw [dif_pos c1] at e
      rw [← Option.some.inj e]
      refine ⟨_, hP ⟨j.val, c1⟩, ?_⟩
      rw [tinl j (by omega)]
      simp [tinA, c1]
    · rw [dif_neg c1] at e
      by_cases c2 : j.val = m
      · rw [if_pos c2] at e; rw [← Option.some.inj e]
        refine ⟨[], hO, ?_⟩
        rw [tinl j (by omega)]
        simp [tinA, c2]
      · rw [if_neg c2] at e; exact absurd e (by simp)
  · intro j e
    unfold nmA at e
    by_cases c1 : j.val < m
    · rw [dif_pos c1] at e; exact absurd e (by simp)
    · rw [dif_neg c1] at e
      by_cases c2 : j.val = m
      · rw [if_pos c2] at e; exact absurd e (by simp)
      · by_cases c3 : j.val = m + 1
        · rw [tinl j (by omega)]
          have : tinA m w ⟨j.val, by omega⟩ = [false] := by simp [tinA, c1, c2]
          rw [this]; exact pad_false1 R hR
        · have c4 : j.val = m + 2 := by have := j.isLt; omega
          rw [addCases_val_eq _ _ j c4]; exact Stages.pad_nil R
  · intro x hx w' e
    unfold valA at e
    by_cases c1 : x.val = out.val
    · rw [if_pos c1] at e
      have ex : x = out := Fin.ext c1
      subst ex
      left
      refine ⟨⟨m, by omega⟩, by simp [nmA], ?_⟩
      rw [← Option.some.inj e]
      have e2 : (⟨m, by omega⟩ : Fin (m + 2 + 1)) = Fin.castAdd 1 ⟨m, by omega⟩ := Fin.ext rfl
      rw [e2, ho]
    · rw [if_neg c1] at e
      by_cases c2 : pb ≤ x.val ∧ x.val < pb + m
      · rw [if_pos c2] at e; exact absurd e (by simp)
      · rw [if_neg c2] at e
        right
        refine ⟨fun j hj => ?_, e⟩
        unfold nmA at hj
        by_cases c3 : j.val < m
        · rw [dif_pos c3] at hj
          have ev := congrArg Fin.val (Option.some.inj hj)
          simp only at ev
          exact c2 ⟨by omega, by omega⟩
        · rw [dif_neg c3] at hj
          by_cases c4 : j.val = m
          · rw [if_pos c4] at hj; exact c1 (by rw [← Option.some.inj hj])
          · rw [if_neg c4] at hj; exact absurd hj (by simp)

/-- Phase B docked: `src` (kept) to `out`. -/
def phBM {NL : ℕ} (src out : Fin NL) (f : ℕ) (hs : f + (3 + 1) ≤ NL) :=
  RecoveryFocus.machine (nslot (nm2 (n := 3 + 1) src 0 out 2) f hs) (MaskedReset.machine innerB.2 (fun _ => true))

theorem phB_trk {NL R G : ℕ} (hR : 1 ≤ R) (v : List Bool) (src out : Fin NL) (hso : src ≠ out) (hsG : src.val < G)
    (hoG : out.val < G) (f : ℕ) (hs : f + (3 + 1) ≤ NL) {E : Fin NL → List Bool} {val : ℕ → Option (List Bool)}
    (hT : Trk R G E val f) (hS : val src.val = some (RepairOrdinary.frame v)) (hO : val out.val = some []) :
    ∃ E', Step (phBM src out f hs) (2*((2*v.length+1) + 1 + (2*0+1)) + 2) (fun _ => 0) E (fun _ => 0) E' ∧
      Trk R G E' (Function.update val out.val (some (RepairOrdinary.frame (List.replicate v.length true)))) (f + (3 + 1)) := by
  obtain ⟨tout, h, ho, hs0⟩ := phaseB_run v
  have r := trk2 h src out 0 2 (by decide) (by decide) hso hsG hoG f hs hT ⟨_, hS, rfl⟩ ⟨[], hO, rfl⟩ (by
    intro j c0 c2
    by_cases c1 : j.val = 1
    · have ej : j = ⟨1, by decide⟩ := Fin.ext c1
      subst ej; exact pad_false1 R hR
    · rw [addCases_val_eq _ _ j (by have := j.isLt; omega)]
      exact Stages.pad_nil R) (val src.val) (by
      intro w e
      rw [hS] at e
      rw [← Option.some.inj e]
      have e0 : (⟨0, by decide⟩ : Fin (3 + 1)) = Fin.castAdd 1 0 := Fin.ext rfl
      rw [e0, hs0]) _ (by
      have e2 : (⟨2, by decide⟩ : Fin (3 + 1)) = Fin.castAdd 1 2 := Fin.ext rfl
      rw [e2, ho]) (by decide)
  rwa [Function.update_eq_self] at r

end
end NearCubicWires.SourceStart.MetaProg

