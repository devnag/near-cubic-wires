import Proof.SourceAssembly.SourceRequestSelSpec

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceRequest.CurSpec
open NearCubicWires NearCubicWires.SourceRequest.SelSpec
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)

/-! ## Per-slot data -/

def fSys : Option Fac → Bool
  | some (.sys _) => true
  | _ => false
def fTerm : Option Fac → Bool
  | some (.term _ _) => true
  | _ => false
def fSide : Option Fac → Bool
  | some (.sys r) => r
  | some (.term r _) => r
  | none => false
def fIdx : Option Fac → Nat
  | some (.term _ i) => i
  | _ => 0

/-- Monomial `m`'s symbolic record (`none` past the end). -/
def selAt (ph : Phase) (sL sR nL nR : Bool) (JL JR m : Nat) : Option Sel := (siteSel ph sL sR nL nR JL JR)[m]?

def facAt (σ : Option Sel) (i : Nat) : Option Fac := σ.bind (fun s => s.facs[i]?)
def kOf (σ : Option Sel) : Nat := (σ.map (fun s => s.facs.length)).getD 0

/-! ## Index algebra of the symbolic operations -/

theorem len_sadd (A B : List Sel) : (sadd A B).length = A.length + B.length := List.length_append
theorem len_sscale (q : ℚ) (A : List Sel) : (sscale q A).length = A.length := List.length_map _
theorem len_smul (A B : List Sel) : (smul A B).length = A.length * B.length :=
  MonomialSpec.length_flatMap_map A B smul1
theorem len_scoord (r : Bool) (J : Nat) : (scoord r J).length = J := by simp [scoord]
theorem len_satom (r : Bool) : (satom r).length = 1 := rfl
theorem len_sconst : sconst.length = 1 := rfl

theorem sadd_left (A B : List Sel) (m : Nat) (h : m < A.length) : (sadd A B)[m]? = A[m]? :=
  List.getElem?_append_left h
theorem sadd_right (A B : List Sel) (m : Nat) (h : A.length ≤ m) : (sadd A B)[m]? = B[m - A.length]? :=
  List.getElem?_append_right h
theorem sscale_get (q : ℚ) (A : List Sel) (m : Nat) :
    (sscale q A)[m]? = (A[m]?).map (fun a => ⟨a.facs, q * a.rho⟩) := by
  simp [sscale, List.getElem?_map]
theorem smul_get (A B : List Sel) (m : Nat) (hB : 0 < B.length) :
    (smul A B)[m]? = (A[m / B.length]?).bind (fun a => (B[m % B.length]?).map (smul1 a)) := by
  unfold smul
  rw [MonomialSpec.get_flatMap_map, if_pos hB]
theorem scoord_get (r : Bool) (J i : Nat) (h : i < J) : (scoord r J)[i]? = some ⟨[.term r i], 1⟩ := by
  simp [scoord, h]
theorem satom_get (r : Bool) : (satom r)[0]? = some ⟨[.sys r], 1⟩ := rfl
theorem sconst_get : sconst[0]? = some ⟨[], 1⟩ := rfl

/-! ## The moment phase: `T_L × T_L` -/

theorem moment_at (sL sR nL nR : Bool) (JL JR m : Nat) (h : m < JL * JL) :
    selAt .moment sL sR nL nR JL JR m = some ⟨[.term false (m / JL), .term false (m % JL)], 1⟩ := by
  have hJ : 0 < JL := by rcases Nat.eq_zero_or_pos JL with h0 | h0 <;> [simp [h0] at h; exact h0]
  unfold selAt siteSel
  rw [smul_get _ _ _ (by rw [len_scoord]; exact hJ), len_scoord,
    scoord_get false JL _ (Nat.div_lt_of_lt_mul h), scoord_get false JL _ (Nat.mod_lt _ hJ)]
  simp [smul1]

theorem moment_end (sL sR nL nR : Bool) (JL JR m : Nat) (h : JL * JL ≤ m) :
    selAt .moment sL sR nL nR JL JR m = none := by
  unfold selAt siteSel
  exact List.getElem?_eq_none (by rw [len_smul, len_scoord]; exact h)

/-! ## The penalty phase: two sides, `½ · (penSide sL L ++ penSide sR R)` -/

theorem len_penSide (s r : Bool) (J : Nat) : (penSide s r J).length = MonomialSpec.penLen s J := by
  cases s <;> simp [penSide, len_sadd, len_sscale, len_smul, len_scoord, len_satom, MonomialSpec.penLen]

def halfSel (σ : Sel) : Sel := ⟨σ.facs, 1 / 2 * σ.rho⟩

theorem penalty_left (sL sR nL nR : Bool) (JL JR m : Nat) (h : m < MonomialSpec.penLen sL JL) :
    selAt .penalty sL sR nL nR JL JR m = ((penSide sL false JL)[m]?).map halfSel := by
  unfold selAt siteSel
  rw [sscale_get, sadd_left _ _ _ (by rw [len_penSide]; exact h)]
  rfl

theorem penalty_right (sL sR nL nR : Bool) (JL JR m : Nat) (h1 : MonomialSpec.penLen sL JL ≤ m) :
    selAt .penalty sL sR nL nR JL JR m =
      ((penSide sR true JR)[m - MonomialSpec.penLen sL JL]?).map halfSel := by
  unfold selAt siteSel
  rw [sscale_get, sadd_right _ _ _ (by rw [len_penSide]; exact h1), len_penSide]
  rfl

theorem penSys_0 (r : Bool) (J : Nat) : (penSide true r J)[0]? = some ⟨[.sys r], 1⟩ := by
  unfold penSide
  rw [if_pos rfl, sadd_left _ _ _ (by rw [len_satom]; omega)]
  rfl

theorem penSys_1 (r : Bool) (J y : Nat) (h1 : 1 ≤ y) (h2 : y - 1 < J) :
    (penSide true r J)[y]? = some ⟨[.sys r, .term r (y - 1)], -2⟩ := by
  unfold penSide
  rw [if_pos rfl, sadd_right _ _ _ (by rw [len_satom]; omega), len_satom,
    sadd_left _ _ _ (by rw [len_sscale, len_smul, len_satom, len_scoord]; omega), sscale_get,
    smul_get _ _ _ (by rw [len_scoord]; omega), len_scoord, Nat.div_eq_of_lt h2, Nat.mod_eq_of_lt h2,
    satom_get, scoord_get r J _ h2]
  simp [smul1]

theorem penSys_2 (r : Bool) (J y : Nat) (h1 : 1 + J ≤ y) (h2 : y - (1 + J) < J * J) :
    (penSide true r J)[y]? =
      some ⟨[.term r ((y - (1 + J)) / J), .term r ((y - (1 + J)) % J)], 1⟩ := by
  have hJ : 0 < J := by rcases Nat.eq_zero_or_pos J with h0 | h0 <;> [simp [h0] at h2; exact h0]
  unfold penSide
  rw [if_pos rfl, sadd_right _ _ _ (by rw [len_satom]; omega), len_satom,
    sadd_right _ _ _ (by rw [len_sscale, len_smul, len_satom, len_scoord]; omega),
    len_sscale, len_smul, len_satom, len_scoord, show y - 1 - 1 * J = y - (1 + J) by omega,
    smul_get _ _ _ (by rw [len_scoord]; exact hJ), len_scoord,
    scoord_get r J _ (Nat.div_lt_of_lt_mul h2), scoord_get r J _ (Nat.mod_lt _ hJ)]
  simp [smul1]

theorem penAux_0 (r : Bool) (J y : Nat) (h : y < J * J) :
    (penSide false r J)[y]? = some ⟨[.term r (y / J), .term r (y % J)], 1⟩ := by
  have hJ : 0 < J := by rcases Nat.eq_zero_or_pos J with h0 | h0 <;> [simp [h0] at h; exact h0]
  unfold penSide
  rw [if_neg (by decide), sadd_left _ _ _ (by rw [len_smul, len_scoord]; exact h),
    smul_get _ _ _ (by rw [len_scoord]; exact hJ), len_scoord,
    scoord_get r J _ (Nat.div_lt_of_lt_mul h), scoord_get r J _ (Nat.mod_lt _ hJ)]
  simp [smul1]

theorem penAux_1 (r : Bool) (J y : Nat) (h1 : J * J ≤ y) (h2 : y - J * J < J * J * J) :
    (penSide false r J)[y]? =
      some ⟨[.term r ((y - J * J) / J / J), .term r ((y - J * J) / J % J), .term r ((y - J * J) % J)], -2⟩ := by
  have hJ : 0 < J := by rcases Nat.eq_zero_or_pos J with h0 | h0 <;> [simp [h0] at h2; exact h0]
  set z := y - J * J with hz
  have hq : z / J < J * J := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h2)
  unfold penSide
  rw [if_neg (by decide), sadd_right _ _ _ (by rw [len_smul, len_scoord]; exact h1), len_smul, len_scoord,
    ← hz, sadd_left _ _ _ (by rw [len_sscale, len_smul, len_smul, len_scoord]; exact h2), sscale_get,
    smul_get _ _ _ (by rw [len_scoord]; exact hJ), len_scoord,
    smul_get _ _ _ (by rw [len_scoord]; exact hJ), len_scoord,
    scoord_get r J _ (Nat.div_lt_of_lt_mul hq), scoord_get r J _ (Nat.mod_lt _ hJ),
    scoord_get r J _ (Nat.mod_lt _ hJ)]
  simp [smul1]

theorem penAux_2 (r : Bool) (J y : Nat) (h1 : J * J + J * J * J ≤ y)
    (h2 : y - (J * J + J * J * J) < J * J * (J * J)) :
    (penSide false r J)[y]? =
      some ⟨[.term r ((y - (J * J + J * J * J)) / J / J / J), .term r ((y - (J * J + J * J * J)) / J / J % J),
        .term r ((y - (J * J + J * J * J)) / J % J), .term r ((y - (J * J + J * J * J)) % J)], 1⟩ := by
  have hJ : 0 < J := by rcases Nat.eq_zero_or_pos J with h0 | h0 <;> [simp [h0] at h2; exact h0]
  set w := y - (J * J + J * J * J) with hw
  have hJJ : 0 < J * J := Nat.mul_pos hJ hJ
  have hq : w / (J * J) < J * J := Nat.div_lt_of_lt_mul h2
  unfold penSide
  rw [if_neg (by decide), sadd_right _ _ _ (by rw [len_smul, len_scoord]; omega), len_smul, len_scoord,
    sadd_right _ _ _ (by rw [len_sscale, len_smul, len_smul, len_scoord]; omega), len_sscale, len_smul, len_smul,
    len_scoord, show y - J * J - J * J * J = w by omega,
    smul_get _ _ _ (by rw [len_smul, len_scoord]; exact hJJ), len_smul, len_scoord,
    smul_get _ _ _ (by rw [len_scoord]; exact hJ), len_scoord,
    smul_get _ _ _ (by rw [len_scoord]; exact hJ), len_scoord,
    scoord_get r J _ (Nat.div_lt_of_lt_mul hq), scoord_get r J _ (Nat.mod_lt _ hJ),
    scoord_get r J _ (Nat.div_lt_of_lt_mul (Nat.mod_lt _ hJJ)), scoord_get r J _ (Nat.mod_lt _ hJ)]
  simp only [Option.bind_some, Option.map_some, smul1, List.cons_append, List.nil_append, mul_one,
    Option.some.injEq, Sel.mk.injEq, List.cons.injEq, Fac.term.injEq, true_and, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Nat.div_div_eq_div_mul]
  · rw [Nat.div_div_eq_div_mul]
  · exact Nat.mod_mul_right_div_self w J J
  · exact Nat.mod_mul_right_mod w J J

theorem penalty_end (sL sR nL nR : Bool) (JL JR m : Nat)
    (h : MonomialSpec.penLen sL JL + MonomialSpec.penLen sR JR ≤ m) :
    selAt .penalty sL sR nL nR JL JR m = none := by
  unfold selAt siteSel
  exact List.getElem?_eq_none (by rw [len_sscale, len_sadd, len_penSide, len_penSide]; exact h)

/-! ## The clause phase: `litL ++ (litR ++ -(litL × litR))` -/

/-- A literal list's entry: `neg ∧ i = 0` is the constant `1`; otherwise the term `i - neg`, sign `-1` if `neg`. -/
def litEntry (neg r : Bool) (i : Nat) : Sel :=
  if neg ∧ i = 0 then ⟨[], 1⟩ else ⟨[.term r (i - neg.toNat)], if neg then -1 else 1⟩

theorem len_litSel (neg r : Bool) (J : Nat) : (litSel neg r J).length = J + neg.toNat := by
  cases neg
  · simp [litSel, len_scoord]
  · simp [litSel, len_sadd, len_sscale, len_scoord, len_sconst]
    omega

theorem litSel_get (neg r : Bool) (J i : Nat) (h : i < J + neg.toNat) :
    (litSel neg r J)[i]? = some (litEntry neg r i) := by
  cases neg with
  | false =>
    simp only [Bool.toNat_false, Nat.add_zero] at h
    simp [litSel, litEntry, scoord_get r J i h]
  | true =>
    simp only [Bool.toNat_true] at h
    unfold litSel litEntry
    rw [if_pos rfl]
    by_cases h0 : i = 0
    · subst h0
      rw [sadd_left _ _ _ (by rw [len_sconst]; omega), sconst_get]
      simp
    · rw [sadd_right _ _ _ (by rw [len_sconst]; omega), len_sconst, sscale_get,
        scoord_get r J _ (by omega)]
      simp [h0]

theorem clause_litL (sL sR nL nR : Bool) (JL JR m : Nat) (h : m < JL + nL.toNat) :
    selAt .clause sL sR nL nR JL JR m = some (litEntry nL false m) := by
  unfold selAt siteSel
  rw [sadd_left _ _ _ (by rw [len_litSel]; exact h), litSel_get _ _ _ _ h]

theorem clause_litR (sL sR nL nR : Bool) (JL JR m : Nat) (h1 : JL + nL.toNat ≤ m)
    (h2 : m - (JL + nL.toNat) < JR + nR.toNat) :
    selAt .clause sL sR nL nR JL JR m = some (litEntry nR true (m - (JL + nL.toNat))) := by
  unfold selAt siteSel
  rw [sadd_right _ _ _ (by rw [len_litSel]; exact h1), len_litSel,
    sadd_left _ _ _ (by rw [len_litSel]; exact h2), litSel_get _ _ _ _ h2]

/-- The cross block's entry at digits `(iL, iR)`. -/
def crossEntry (nL nR : Bool) (iL iR : Nat) : Sel :=
  ⟨(litEntry nL false iL).facs ++ (litEntry nR true iR).facs,
    -1 * ((litEntry nL false iL).rho * (litEntry nR true iR).rho)⟩

theorem clause_cross (sL sR nL nR : Bool) (JL JR m : Nat)
    (h1 : (JL + nL.toNat) + (JR + nR.toNat) ≤ m)
    (h2 : m - ((JL + nL.toNat) + (JR + nR.toNat)) < (JL + nL.toNat) * (JR + nR.toNat)) :
    selAt .clause sL sR nL nR JL JR m =
      some (crossEntry nL nR ((m - ((JL + nL.toNat) + (JR + nR.toNat))) / (JR + nR.toNat))
        ((m - ((JL + nL.toNat) + (JR + nR.toNat))) % (JR + nR.toNat))) := by
  set aL := JL + nL.toNat with haL
  set aR := JR + nR.toNat with haR
  set y := m - (aL + aR) with hy
  have haR0 : 0 < aR := by rcases Nat.eq_zero_or_pos aR with h0 | h0 <;> [simp [h0] at h2; exact h0]
  unfold selAt siteSel
  rw [sadd_right _ _ _ (by rw [len_litSel]; omega), len_litSel, ← haL,
    sadd_right _ _ _ (by rw [len_litSel]; omega), len_litSel, ← haR,
    show m - aL - aR = y by omega, sscale_get,
    smul_get _ _ _ (by rw [len_litSel]; exact haR0), len_litSel, ← haR,
    litSel_get nL false JL (y / aR) (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h2)),
    litSel_get nR true JR (y % aR) (Nat.mod_lt _ haR0)]
  simp [smul1, crossEntry]

theorem clause_end (sL sR nL nR : Bool) (JL JR m : Nat)
    (h : (JL + nL.toNat) + ((JR + nR.toNat) + (JL + nL.toNat) * (JR + nR.toNat)) ≤ m) :
    selAt .clause sL sR nL nR JL JR m = none := by
  unfold selAt siteSel
  exact List.getElem?_eq_none (by
    rw [len_sadd, len_sadd, len_sscale, len_smul, len_litSel, len_litSel]; exact h)

end NearCubicWires.SourceRequest.CurSpec

