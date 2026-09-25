import Proof.Packets.PacketsWriterPlan

/-! # Q3 (a): the relabel source bound from ONE named degree fact.

Consumer: `RelabelFit.stream_le` and `cap_le` (`Proof/Packets/PacketsWriterPlan.lean`). They bound the relabel
stage's `S` by `smallSize`, and with it the whole back-half cost. Paper: the row's "canonical
polynomial expansion" is charged in `T_prep` (`paper.tex:1197-1200`); the prepared-size alphabet
`(alphabet)^(degree+1)` is a summand of `smallSize`
(`Proof/Assembly/Production.lean`). Budget: none (arithmetic).

The degree fact `LoweredDegree a` (every lowered row polynomial has degree at most its row's
declared `degree`) is PROVED for every request from accepted compiler-law lemmas
(`loweredDegree_holds`). The remaining steps are proved here as well:
* a normal polynomial with codes `< N` and degree `≤ D` has at most `(N+1)^D` monomials
  (`length_le_pow`);
* so its incidence stream is at most `(N+1)^D * (D*(N+1)+2) + 1` (`stream_length_le`);
* that is at most `4 * smallSize^3` (`streamCap_le`).
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent
noncomputable section

/-- Injective code of a short monomial over `[0, N)`: position `i` holds `m[i]+1`, or `0` past the end. -/
def monoCode (N D : ℕ) (m : List ℕ) : Fin D → Fin (N + 1) := fun i =>
  if h : i.val < m.length then (if h2 : m[i.val] < N then ⟨m[i.val] + 1, by omega⟩ else 0) else 0

theorem monoCode_ne_zero {N D : ℕ} {m : List ℕ} (hv : ∀ c ∈ m, c < N) (i : Fin D) :
    monoCode N D m i ≠ 0 ↔ i.val < m.length := by
  unfold monoCode
  constructor
  · intro h
    by_contra hl
    exact h (by rw [dif_neg hl])
  · intro hl
    have hc : m[i.val] < N := hv _ (List.getElem_mem hl)
    rw [dif_pos hl, dif_pos hc]
    intro he
    have := congrArg Fin.val he
    simp at this

theorem monoCode_injOn {N D : ℕ} {m m' : List ℕ} (hv : ∀ c ∈ m, c < N) (hv' : ∀ c ∈ m', c < N)
    (hd : m.length ≤ D) (hd' : m'.length ≤ D) (h : monoCode N D m = monoCode N D m') : m = m' := by
  have hlen : m.length = m'.length := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have hi : ¬ (monoCode N D m ⟨m.length, by omega⟩ ≠ 0) := by
        rw [monoCode_ne_zero hv]; simp
      have hi' : monoCode N D m' ⟨m.length, by omega⟩ ≠ 0 := by
        rw [monoCode_ne_zero hv']; exact hlt
      rw [h] at hi
      exact hi hi'
    · have hi : ¬ (monoCode N D m' ⟨m'.length, by omega⟩ ≠ 0) := by
        rw [monoCode_ne_zero hv']; simp
      have hi' : monoCode N D m ⟨m'.length, by omega⟩ ≠ 0 := by
        rw [monoCode_ne_zero hv]; exact hlt
      rw [h] at hi'
      exact hi hi'
  apply List.ext_getElem hlen
  intro i h1 h2
  have he := congrFun h ⟨i, by omega⟩
  have hc : m[i] < N := hv _ (List.getElem_mem h1)
  have hc' : m'[i] < N := hv' _ (List.getElem_mem h2)
  simp only [monoCode, dif_pos h1, dif_pos h2, dif_pos hc, dif_pos hc'] at he
  have := congrArg Fin.val he
  simp at this
  exact this

/-- A normal polynomial over codes `< N` of degree `≤ D` has at most `(N+1)^D` monomials. -/
theorem length_le_pow (N D : ℕ) (P : List (List ℕ)) (hn : P.Nodup)
    (hv : ∀ m ∈ P, ∀ c ∈ m, c < N) (hd : ∀ m ∈ P, m.length ≤ D) : P.length ≤ (N + 1) ^ D := by
  have hnd : (P.map (monoCode N D)).Nodup :=
    List.Nodup.map_on (fun x hx y hy he => monoCode_injOn (hv x hx) (hv y hy) (hd x hx) (hd y hy) he) hn
  have hle := hnd.length_le_card
  rw [List.length_map] at hle
  simpa [Fintype.card_fun, Fintype.card_fin] using hle

theorem monomialWord_length_le (N D : ℕ) (m : List ℕ) (hv : ∀ c ∈ m, c < N) (hd : m.length ≤ D) :
    (ExtIncidence.monomialWord m).length ≤ D * (N + 1) + 2 := by
  rw [ExtIncidence.monomialWord_length]
  have h : (m.flatMap ExtIncidence.block).length ≤ m.length * (N + 1) := by
    induction m with
    | nil => simp
    | cons c m ih =>
      have hc : c < N := hv c (by simp)
      have ih' := ih (fun d hd => hv d (by simp [hd])) (by simp at hd; omega)
      simp only [List.flatMap_cons, List.length_append, ExtIncidence.block_length, List.length_cons]
      nlinarith
  have h2 : m.length * (N + 1) ≤ D * (N + 1) := Nat.mul_le_mul_right _ hd
  omega

theorem stream_length_le (N D : ℕ) (P : List (List ℕ)) (hv : ∀ m ∈ P, ∀ c ∈ m, c < N)
    (hd : ∀ m ∈ P, m.length ≤ D) :
    (ExtIncidence.stream P).length ≤ P.length * (D * (N + 1) + 2) + 1 := by
  unfold ExtIncidence.stream
  rw [List.length_append, List.length_singleton]
  have h : (P.flatMap ExtIncidence.monomialWord).length ≤ P.length * (D * (N + 1) + 2) := by
    induction P with
    | nil => simp
    | cons m P ih =>
      have hm := monomialWord_length_le N D m (hv m (by simp)) (hd m (by simp))
      have ih' := ih (fun x hx => hv x (by simp [hx])) (fun x hx => hd x (by simp [hx]))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      nlinarith
  omega

/-! ## The one named fact, and the fit it gives -/

/-- **The degree clause** (open, mathematical): every lowered row has degree at most its row's
declared degree. -/
def LoweredDegree (a : DecompositionAlgorithm) : Prop :=
  ∀ r (k : rcKey a r), k ∈ rcKeys a r →
    Ring.Degree (rcDecode a r k).degree (Packets.lowered a (r.family a) (rcDecode a r k))

/-- **The degree clause HOLDS**, from the accepted compiler-law lemmas (revision 50):
`PCJc06b3608d6d34481_Rows.sym_degree`/`thr_degree` (row polynomial degree, any request) and
`PCJc06b3608d6d34481_Transport.lowered_degree` (normalized substitution by degree-1 atoms). -/
theorem loweredDegree_holds (a : DecompositionAlgorithm) : LoweredDegree a := by
  intro r k _
  apply PCJc06b3608d6d34481_Transport.lowered_degree
  cases r with
  | terminal => exact PEmpty.elim k
  | sym r four L target =>
    exact PCJc06b3608d6d34481_Rows.sym_degree r _ _ k.seed k.offset
  | thr r four L target =>
    exact PCJc06b3608d6d34481_Rows.thr_degree a r _ _ k.selection k.prime.val k.residue.val k.seed

/-- The request-level stream capacity. -/
def streamCap (a : DecompositionAlgorithm) (r : Request) : ℕ :=
  (relabelN a r + 1) ^ (r.degree a) * (r.degree a * (relabelN a r + 1) + 2) + 1

theorem decode_mem (a : DecompositionAlgorithm) (r : Request) (k : rcKey a r) (hk : k ∈ rcKeys a r) :
    rcDecode a r k ∈ (r.family a).rows := by
  rw [← rc_keys_eq a r]
  exact List.mem_map_of_mem hk

theorem stream_le_cap (a : DecompositionAlgorithm) (hdeg : LoweredDegree a) (r : Request)
    (k : rcKey a r) (hk : k ∈ rcKeys a r) :
    (ExtIncidence.stream (Packets.lowered a (r.family a) (rcDecode a r k)).reverse).length ≤
      streamCap a r := by
  have hN := lowered_normal a (r.family a) (rcDecode a r k)
  have hV := lowered_valid a (r.family a) (rcDecode a r k)
  have hrow := RCFive.PacketBounds.degree_bound a r _ (decode_mem a r k hk)
  have hD : ∀ m ∈ (Packets.lowered a (r.family a) (rcDecode a r k)).reverse, m.length ≤ r.degree a :=
    fun m hm => (hdeg r k hk m (List.mem_reverse.mp hm)).trans hrow
  have hv : ∀ m ∈ (Packets.lowered a (r.family a) (rcDecode a r k)).reverse, ∀ c ∈ m, c < relabelN a r :=
    fun m hm => hV m (List.mem_reverse.mp hm)
  have hlen := length_le_pow (relabelN a r) (r.degree a) _ (List.nodup_reverse.mpr hN.1) hv hD
  have hs := stream_length_le (relabelN a r) (r.degree a) _ hv hD
  unfold streamCap
  have := Nat.mul_le_mul_right (r.degree a * (relabelN a r + 1) + 2) hlen
  omega

theorem streamCap_le (a : DecompositionAlgorithm) (r : Request) :
    streamCap a r ≤ 4 * (r.smallSize a) ^ 3 := by
  set s := r.smallSize a with hsdef
  have hs1 : 1 ≤ s := RCFive.PacketBounds.positive a r
  have hA : relabelN a r + 2 = Packets.alphabet a (r.family a) := rfl
  have hAs : (Packets.alphabet a (r.family a))^(r.degree a + 1) ≤ s := by
    rw [hsdef]
    dsimp only [Request.smallSize]
    generalize (2:Nat)^(Packets.live (r.family a)).card = livePower
    generalize (2:Nat)^(SupplierWalkBridge.canonicalWalkLength (r.denominator a)) = walkPower
    omega
  have hpow : (relabelN a r + 1) ^ (r.degree a) ≤ s := by
    calc (relabelN a r + 1) ^ (r.degree a) ≤ (Packets.alphabet a (r.family a)) ^ (r.degree a) :=
          Nat.pow_le_pow_left (by omega) _
      _ ≤ (Packets.alphabet a (r.family a))^(r.degree a + 1) :=
          Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ s := hAs
  have hdeg : r.degree a ≤ s := by
    have h2 : r.degree a < 2 ^ (r.degree a + 1) := by
      have := Nat.lt_two_pow_self (n := r.degree a + 1)
      omega
    have h3 : 2 ^ (r.degree a + 1) ≤ (Packets.alphabet a (r.family a))^(r.degree a + 1) :=
      Nat.pow_le_pow_left (by omega) _
    omega
  have hN : relabelN a r + 1 ≤ s := by
    have h1 : Packets.alphabet a (r.family a) ≤ (Packets.alphabet a (r.family a))^(r.degree a + 1) :=
      Nat.le_self_pow (by omega) _
    omega
  have hmid : r.degree a * (relabelN a r + 1) + 2 ≤ s * s + 2 := by
    have := Nat.mul_le_mul hdeg hN
    omega
  unfold streamCap
  have h1 : (relabelN a r + 1) ^ (r.degree a) * (r.degree a * (relabelN a r + 1) + 2) ≤ s * (s * s + 2) :=
    Nat.mul_le_mul hpow hmid
  have hcube : s ^ 3 = s * s * s := by ring
  rw [hcube]
  nlinarith

/-- **`RelabelFit` from the degree clause** and the width's room. -/
def relabelFit {a : DecompositionAlgorithm} (X : WriterShape a) (hdeg : LoweredDegree a)
    (room : ∀ r, P1Closure.RawRelabelUniform.logCapacity (relabelN a r) (relabelY a r) (streamCap a r) +
      (relabelN a r * relabelY a r + 3) + (relabelY a r + 1) + 1 ≤ X.R r) : RelabelFit X where
  streamCap := streamCap a
  capCoefficient := 4
  capDegree := 3
  cap_le := streamCap_le a
  stream_le := stream_le_cap a hdeg
  room := room

end
end NearCubicWires.PacketsConstruction
