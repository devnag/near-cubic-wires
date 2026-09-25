import Proof.SourceAssembly.SourcePoolIndexReady

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceFactorSel.Item4
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source PCJ6fbdd6f776f6447d_Source
noncomputable section

/-- P's five input words (agreed 04:5x). -/
def inWord (a : DecompositionAlgorithm) (r : Request) : Fin 5 → List Bool :=
  ![RepairOrdinary.frame r.nativeWord, RepairOrdinary.frame (r.supportWord a), RepairOrdinary.frame (List.replicate r.q true),
    List.replicate r.nativeWord.length true,
    RepairOrdinary.frame (CloseoutRowsGateSupport.gateMembers (Packets.live (r.family a)))]

/-- **P's start-bank contract** (the typed hole): one fixed machine on `Fin (132 + Cold.tapes a + k)` (bank first, then P's tail with
the five inputs on `inPort`), writing the ACCEPTED runs' common entry bank for EVERY request, at request functions `B w Pc` meeting
`request_run`'s side conditions. -/
structure StartBank (a : DecompositionAlgorithm) (k : Nat) where
  states : Nat
  machine : Machine (132 + Cold.tapes a + k) states
  cost : Request → Nat
  need : Request → Nat
  B : Request → Nat
  w : Request → Nat
  Pc : Request → Nat
  inPort : Fin 5 → Fin k
  inPort_inj : Function.Injective inPort
  hw : ∀ r, 0 < w r
  hqw : ∀ r : Request, r.q ≤ w r
  hb : ∀ (r : Request), ∀ g ∈ (r.family a).occurrences, (CloseoutRowsCircuitBottom.nativeWord g).length ≤ B r
  hm : ∀ (r : Request), ∀ g ∈ (r.family a).occurrences,
    (g.gate.threshold - 1).natAbs + (∑ i, (g.gate.weight i).natAbs) < 2 ^ (w r)
  hqP : ∀ r : Request, r.q ≤ Pc r
  hi : ∀ r : Request, (segment (CloseoutRowsUniversal.pool (Packets.live (r.family a)) (r.family a).occurrences)
    []).length ≤ 1000 * (Pc r + 2) ^ 2
  run : ∀ (r : Request) (R : Nat) (E : Fin (132 + Cold.tapes a + k) → List Bool), need r ≤ R →
    (∀ j, E (Fin.natAdd (132 + Cold.tapes a) (inPort j)) = ZeroPadding.pad R (inWord a r j)) →
    (∀ x, (∀ j, Fin.natAdd (132 + Cold.tapes a) (inPort j) ≠ x) → E x = List.replicate R false) →
    ∃ E' : Fin (132 + Cold.tapes a + k) → List Bool,
      Step machine (cost r) (fun _ => 0) E
        (Fin.addCases (Fin.addCases (PoolCold.start (Packets.live (r.family a)) (r.family a).occurrences (B r) (w r) []).heads
          (PoolCold.coldHeads a)) (fun _ : Fin k => 0)) E' ∧
      (∀ i : Fin (132 + Cold.tapes a), E' (Fin.castAdd k i) = ZeroPadding.pad R
        (Fin.addCases (PoolCold.start (Packets.live (r.family a)) (r.family a).occurrences (B r) (w r) []).tapes
          (PoolCold.coldData a (Pc r) r.q) i)) ∧
      (∀ j, E' (Fin.natAdd (132 + Cold.tapes a) (inPort j)) = E (Fin.natAdd (132 + Cold.tapes a) (inPort j)))

/-! ## The index block -/

section index
variable {a : DecompositionAlgorithm} {k : Nat}

/-- P's machine docked on the index block: bank in place, tail after the six extra tapes. -/
def sbI (a : DecompositionAlgorithm) (k : Nat) (x : Fin ((132 + Cold.tapes a) + k)) : Fin ((132 + Cold.tapes a) + (6 + k)) :=
  if h : x.val < (132 + Cold.tapes a) then ⟨x.val, by omega⟩ else ⟨x.val + 6, by have := x.isLt; omega⟩

theorem sbI_val (x : Fin ((132 + Cold.tapes a) + k)) : (sbI a k x).val = if x.val < (132 + Cold.tapes a) then x.val else x.val + 6 := by
  unfold sbI; split_ifs <;> rfl

theorem sbI_inj : Function.Injective (sbI a k) := by
  intro x y h
  have hv := congrArg Fin.val h
  rw [sbI_val, sbI_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

/-- The index run docked on the index block: the identity on the bank and its six extra tapes. -/
def ixI (a : DecompositionAlgorithm) (k : Nat) (x : Fin ((132 + Cold.tapes a) + 6)) : Fin ((132 + Cold.tapes a) + (6 + k)) := ⟨x.val, by omega⟩

theorem ixI_inj : Function.Injective (ixI a k) := by
  intro x y h
  have hv := congrArg Fin.val h
  simp only [ixI] at hv
  exact Fin.ext hv

/-- The index block. -/
def idxBlock (SB : StartBank a k) :=
  Composition.machine (RecoveryFocus.machine (sbI a k) SB.machine)
    (RecoveryFocus.machine (ixI a k) (PCJ6e421fabe2aa4155_SourcePoolIndex.machine a))

/-- Its per-request cost. -/
def idxCost (SB : StartBank a k) (r : Request) : Nat :=
  SB.cost r + 1 + PCJ6e421fabe2aa4155_SourcePoolIndex.budget a (Packets.live (r.family a)) (r.family a).occurrences
    (SB.B r) (SB.w r) (SB.Pc r)

/-- The block's input ports and its output port. -/
def ixIn (SB : StartBank a k) (j : Fin 5) : Fin ((132 + Cold.tapes a) + (6 + k)) := sbI a k (Fin.natAdd ((132 + Cold.tapes a)) (SB.inPort j))
def ixOut (a : DecompositionAlgorithm) (k : Nat) : Fin ((132 + Cold.tapes a) + (6 + k)) :=
  ixI a k (PCJ6e421fabe2aa4155_SourcePoolIndex.indexPorts a 7)

theorem ixIn_val (SB : StartBank a k) (j : Fin 5) : (ixIn SB j).val = (132 + Cold.tapes a) + 6 + (SB.inPort j).val := by
  unfold ixIn; rw [sbI_val]; simp only [Fin.val_natAdd]; split_ifs <;> omega

theorem indexPort7_val : (PCJ6e421fabe2aa4155_SourcePoolIndex.indexPorts a 7).val = (132 + Cold.tapes a) + 4 := by
  simp [PCJ6e421fabe2aa4155_SourcePoolIndex.indexPorts, PCJ6e421fabe2aa4155_SourcePoolIndex.indexMap,
    PCJ6e421fabe2aa4155_SourcePoolIndex.slots]
  rfl

theorem ixOut_val : (ixOut a k).val = (132 + Cold.tapes a) + 4 := indexPort7_val

theorem idx_block_run (SB : StartBank a k) (r : Request) (R : Nat) (hR : SB.need r ≤ R)
    (E : Fin ((132 + Cold.tapes a) + (6 + k)) → List Bool)
    (hin : ∀ j, E (ixIn SB j) = ZeroPadding.pad R (inWord a r j))
    (hbl : ∀ x, (∀ j, ixIn SB j ≠ x) → E x = List.replicate R false) :
    ∃ (H' : Fin ((132 + Cold.tapes a) + (6 + k)) → Nat) (E' : Fin ((132 + Cold.tapes a) + (6 + k)) → List Bool),
      Step (idxBlock SB) (idxCost SB r) (fun _ => 0) E H' E' ∧
      H' (ixOut a k) = 0 ∧ E' (ixOut a k) = ZeroPadding.pad R (RepairOrdinary.frame (r.indexWord a)) ∧
      (∀ j, E' (ixIn SB j) = E (ixIn SB j) ∧ H' (ixIn SB j) = 0) := by
  classical
  -- stage 1: P's start bank, docked by `sbI`
  obtain ⟨E1, st1, b1, k1⟩ := SB.run r R (fun i => E (sbI a k i)) hR (fun j => hin j) (by
    intro x hx
    apply hbl
    intro j e
    exact hx j (sbI_inj e))
  have d1 := st1.dock (sbI a k) sbI_inj (fun _ => 0) E (fun _ => rfl) (fun _ => rfl)
  -- stage 2: the accepted index run, docked by `ixI`
  obtain ⟨H2, A2, st2, h2H, h2A⟩ := PCJ6e421fabe2aa4155_SourcePoolIndexReady.request_run a r (SB.B r) (SB.w r) (SB.Pc r) []
    (fun _ => R) (SB.hw r) (SB.hqw r) (SB.hb r) (SB.hm r) (SB.hqP r) (SB.hi r)
  have hbank : ∀ (i : Fin ((132 + Cold.tapes a) + 6)) (hi : i.val < (132 + Cold.tapes a)),
      ixI a k i = sbI a k (Fin.castAdd k ⟨i.val, hi⟩) := by
    intro i hi
    apply Fin.ext
    rw [sbI_val]; simp only [ixI, Fin.val_castAdd]; rw [if_pos hi]
  have hextra : ∀ i : Fin ((132 + Cold.tapes a) + 6), (132 + Cold.tapes a) ≤ i.val → ∀ y, sbI a k y ≠ ixI a k i := by
    intro i hi y e
    have hv := congrArg Fin.val e
    rw [sbI_val] at hv
    simp only [ixI] at hv
    have := i.isLt
    split_ifs at hv <;> omega
  have d2 := st2.dock (ixI a k) ixI_inj (dockH (sbI a k) (fun _ => 0)
      (Fin.addCases (Fin.addCases (PoolCold.start (Packets.live (r.family a)) (r.family a).occurrences (SB.B r) (SB.w r)
        []).heads (PoolCold.coldHeads a)) (fun _ : Fin k => 0)))
      (install (sbI a k) E E1)
    (by
      intro i
      by_cases hi : i.val < (132 + Cold.tapes a)
      · rw [hbank i hi, dockH_slot _ sbI_inj]
        have e1 : i = Fin.castAdd 6 (⟨i.val, hi⟩ : Fin ((132 + Cold.tapes a))) := Fin.ext rfl
        rw [Fin.addCases_left]
        conv_rhs => rw [e1]
        rw [Fin.addCases_left]
      · rw [dockH_other _ _ _ _ (hextra i (by omega))]
        have e1 : i = Fin.natAdd ((132 + Cold.tapes a)) (⟨i.val - (132 + Cold.tapes a), by have := i.isLt; omega⟩ : Fin 6) :=
          Fin.ext (by simp only [Fin.val_natAdd]; omega)
        rw [e1, Fin.addCases_right])
    (by
      intro i
      by_cases hi : i.val < (132 + Cold.tapes a)
      · rw [hbank i hi, install_slot _ sbI_inj, b1]
        have e1 : i = Fin.castAdd 6 (⟨i.val, hi⟩ : Fin ((132 + Cold.tapes a))) := Fin.ext rfl
        conv_rhs => rw [e1]
        rw [Fin.addCases_left]
      · rw [install_other _ _ _ _ (hextra i (by omega))]
        have e1 : i = Fin.natAdd ((132 + Cold.tapes a)) (⟨i.val - (132 + Cold.tapes a), by have := i.isLt; omega⟩ : Fin 6) :=
          Fin.ext (by simp only [Fin.val_natAdd]; omega)
        rw [hbl _ (by
          intro j e
          have hv := congrArg Fin.val e
          rw [ixIn_val] at hv
          simp only [ixI] at hv
          have := i.isLt
          omega)]
        rw [e1, Fin.addCases_right]
        simp [ZeroPadding.pad])
  refine ⟨_, _, d1.seq d2, ?_, ?_, ?_⟩
  · unfold ixOut; rw [dockH_slot _ ixI_inj]; exact h2H
  · unfold ixOut; rw [install_slot _ ixI_inj]; exact h2A
  · intro j
    have hno : ∀ y, ixI a k y ≠ ixIn SB j := by
      intro y e
      have hv := congrArg Fin.val e
      rw [ixIn_val] at hv
      simp only [ixI] at hv
      have := y.isLt
      omega
    refine ⟨?_, ?_⟩
    · rw [install_other _ _ _ _ hno]
      unfold ixIn
      rw [install_slot _ sbI_inj]
      exact k1 j
    · rw [dockH_other _ _ _ _ hno]
      unfold ixIn
      rw [dockH_slot _ sbI_inj, Fin.addCases_right]

end index

/-! ## The pool block -/

section pool
variable {a : DecompositionAlgorithm} {k : Nat}

/-- P's machine docked on the pool block: bank in place, tail after the 373 extra tapes. -/
def sbP (a : DecompositionAlgorithm) (k : Nat) (x : Fin ((132 + Cold.tapes a) + k)) : Fin ((132 + Cold.tapes a) + (373 + k)) :=
  if h : x.val < (132 + Cold.tapes a) then ⟨x.val, by omega⟩ else ⟨x.val + 373, by have := x.isLt; omega⟩

theorem sbP_val (x : Fin ((132 + Cold.tapes a) + k)) :
    (sbP a k x).val = if x.val < (132 + Cold.tapes a) then x.val else x.val + 373 := by
  unfold sbP; split_ifs <;> rfl

theorem sbP_inj : Function.Injective (sbP a k) := by
  intro x y h
  have hv := congrArg Fin.val h
  rw [sbP_val, sbP_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

/-- The cache run docked on the pool block: the identity on the bank and its 373 extra tapes. -/
def plI (a : DecompositionAlgorithm) (k : Nat) (x : Fin ((132 + Cold.tapes a) + 373)) :
    Fin ((132 + Cold.tapes a) + (373 + k)) := ⟨x.val, by omega⟩

theorem plI_inj : Function.Injective (plI a k) := by
  intro x y h
  have hv := congrArg Fin.val h
  simp only [plI] at hv
  exact Fin.ext hv

/-- The pool block. -/
def poolBlock (SB : StartBank a k) :=
  Composition.machine (RecoveryFocus.machine (sbP a k) SB.machine)
    (RecoveryFocus.machine (plI a k) (PCJ6e421fabe2aa4155_SourceCache.machine a))

/-- Its per-request cost. -/
def poolCost (SB : StartBank a k) (r : Request) : Nat :=
  SB.cost r + 1 + PCJ6e421fabe2aa4155_SourceCache.budget a (r.family a).occurrences (SB.B r) (SB.w r) (SB.Pc r)

/-- Input ports, the two resident inputs of the extra block (`225` K template, `226` mask word), the pool outputs. -/
def plIn (SB : StartBank a k) (j : Fin 5) : Fin ((132 + Cold.tapes a) + (373 + k)) :=
  sbP a k (Fin.natAdd (132 + Cold.tapes a) (SB.inPort j))
def plX (a : DecompositionAlgorithm) (k : Nat) (j : Fin 373) : Fin ((132 + Cold.tapes a) + (373 + k)) :=
  ⟨(132 + Cold.tapes a) + j.val, by omega⟩
def plOut (a : DecompositionAlgorithm) (k : Nat) (j : Fin 373) : Fin ((132 + Cold.tapes a) + (373 + k)) :=
  plI a k (PCJ6e421fabe2aa4155_SourceCache.poolSlots a j)

theorem plIn_val (SB : StartBank a k) (j : Fin 5) : (plIn SB j).val = (132 + Cold.tapes a) + 373 + (SB.inPort j).val := by
  unfold plIn; rw [sbP_val]; simp only [Fin.val_natAdd]; split_ifs <;> omega

theorem plOut_extra (j : Fin 373) (h98 : j ≠ 98) (h224 : j ≠ 224) : plOut a k j = plX a k j := by
  apply Fin.ext
  simp [plOut, plI, plX, PCJ6e421fabe2aa4155_SourceCache.poolSlots, h98, h224]

/-- **The pool block's run**: from the five input words, the K template on `plX 225` and the mask word on `plX 226`, everything
else blank at `R`, heads `0`, the block leaves the whole cold-cache input `pad R (BinaryCacheColdRun.input (cacheArgs a F) j)` on
`plOut j` with heads `0` (for `j ≠ 98, 224` that is the extra tape `plX j`, returned), and returns the inputs with heads `0`. -/
theorem pool_block_run (selector : CyclicChoice.Laws) (SB : StartBank a k) (r : Request) (R : Nat) (hR : SB.need r ≤ R)
    (E : Fin ((132 + Cold.tapes a) + (373 + k)) → List Bool)
    (hin : ∀ j, E (plIn SB j) = ZeroPadding.pad R (inWord a r j))
    (hK : E (plX a k 225) = ZeroPadding.pad R (UnaryTemplate.tape (maskData a r).K))
    (hM : E (plX a k 226) = ZeroPadding.pad R (maskData a r).word)
    (hbl : ∀ x, (∀ j, plIn SB j ≠ x) → x ≠ plX a k 225 → x ≠ plX a k 226 → E x = List.replicate R false) :
    ∃ (H' : Fin ((132 + Cold.tapes a) + (373 + k)) → Nat) (E' : Fin ((132 + Cold.tapes a) + (373 + k)) → List Bool),
      Step (poolBlock SB) (poolCost SB r) (fun _ => 0) E H' E' ∧
      (∀ j, H' (plOut a k j) = 0 ∧ E' (plOut a k j) = ZeroPadding.pad R
        (BinaryCacheColdRun.input (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)) j)) ∧
      (∀ j, E' (plIn SB j) = E (plIn SB j) ∧ H' (plIn SB j) = 0) := by
  classical
  have hXin : ∀ (j : Fin 5) (i : Fin 373), plIn SB j ≠ plX a k i := by
    intro j i e
    have hv := congrArg Fin.val e
    rw [plIn_val] at hv
    simp only [plX] at hv
    have := i.isLt
    omega
  obtain ⟨E1, st1, b1, k1⟩ := SB.run r R (fun i => E (sbP a k i)) hR (fun j => hin j) (by
    intro x hx
    have hnx : ∀ j, plIn SB j ≠ sbP a k x := fun j e => hx j (sbP_inj e)
    apply hbl _ hnx
    · intro e
      have hv := congrArg Fin.val e
      rw [sbP_val] at hv
      simp only [plX] at hv
      have := x.isLt
      split_ifs at hv with h1
      · omega
      · omega
    · intro e
      have hv := congrArg Fin.val e
      rw [sbP_val] at hv
      simp only [plX] at hv
      have := x.isLt
      split_ifs at hv with h1
      · omega
      · omega)
  have d1 := st1.dock (sbP a k) sbP_inj (fun _ => 0) E (fun _ => rfl) (fun _ => rfl)
  obtain ⟨H2, A2, st2⟩ := PCJ6e421fabe2aa4155_SourceCacheReady.request_pool_entry selector a r (SB.B r) (SB.w r) (SB.Pc r) []
    (fun _ => R) (SB.hw r) (SB.hqw r) (SB.hb r) (SB.hm r) (SB.hqP r) (SB.hi r)
  have hbank : ∀ (i : Fin ((132 + Cold.tapes a) + 373)) (hi : i.val < (132 + Cold.tapes a)),
      plI a k i = sbP a k (Fin.castAdd k ⟨i.val, hi⟩) := by
    intro i hi
    apply Fin.ext
    rw [sbP_val]; simp only [plI, Fin.val_castAdd]; rw [if_pos hi]
  have hextra : ∀ i : Fin ((132 + Cold.tapes a) + 373), (132 + Cold.tapes a) ≤ i.val → ∀ y, sbP a k y ≠ plI a k i := by
    intro i hi y e
    have hv := congrArg Fin.val e
    rw [sbP_val] at hv
    simp only [plI] at hv
    have := i.isLt
    split_ifs at hv <;> omega
  have d2 := st2.dock (plI a k) plI_inj (dockH (sbP a k) (fun _ => 0)
      (Fin.addCases (Fin.addCases (PoolCold.start (Packets.live (r.family a)) (r.family a).occurrences (SB.B r) (SB.w r)
        []).heads (PoolCold.coldHeads a)) (fun _ : Fin k => 0)))
      (install (sbP a k) E E1)
    (by
      intro i
      by_cases hi : i.val < (132 + Cold.tapes a)
      · rw [hbank i hi, dockH_slot _ sbP_inj]
        have e1 : i = Fin.castAdd 373 (⟨i.val, hi⟩ : Fin ((132 + Cold.tapes a))) := Fin.ext rfl
        rw [Fin.addCases_left]
        conv_rhs => rw [e1]
        rw [Fin.addCases_left]
      · rw [dockH_other _ _ _ _ (hextra i (by omega))]
        have e1 : i = Fin.natAdd (132 + Cold.tapes a) (⟨i.val - (132 + Cold.tapes a), by have := i.isLt; omega⟩ : Fin 373) :=
          Fin.ext (by simp only [Fin.val_natAdd]; omega)
        rw [e1, Fin.addCases_right])
    (by
      intro i
      by_cases hi : i.val < (132 + Cold.tapes a)
      · rw [hbank i hi, install_slot _ sbP_inj, b1]
        have e1 : i = Fin.castAdd 373 (⟨i.val, hi⟩ : Fin ((132 + Cold.tapes a))) := Fin.ext rfl
        conv_rhs => rw [e1]
        rw [Fin.addCases_left]
      · rw [install_other _ _ _ _ (hextra i (by omega))]
        set jj : Fin 373 := ⟨i.val - (132 + Cold.tapes a), by have := i.isLt; omega⟩ with hjj
        have e1 : i = Fin.natAdd (132 + Cold.tapes a) jj := Fin.ext (by simp only [hjj, Fin.val_natAdd]; omega)
        have ex : plI a k i = plX a k jj := Fin.ext (by simp only [plI, plX, hjj]; omega)
        rw [ex]
        conv_rhs => rw [e1]
        rw [Fin.addCases_right]
        by_cases h5 : jj = 225
        · rw [if_pos h5, h5]; exact hK
        · by_cases h6 : jj = 226
          · rw [if_neg h5, if_pos h6, h6]; exact hM
          · rw [if_neg h5, if_neg h6, hbl _ (fun j => hXin j jj)
              (fun e => h5 (by have := congrArg Fin.val e; simp only [plX] at this; exact Fin.ext (by simp; omega)))
              (fun e => h6 (by have := congrArg Fin.val e; simp only [plX] at this; exact Fin.ext (by simp; omega)))]
            simp [ZeroPadding.pad])
  refine ⟨_, _, d1.seq d2, ?_, ?_⟩
  · intro j
    unfold plOut
    refine ⟨?_, ?_⟩
    · rw [dockH_slot _ plI_inj, dockH_slot _ (PCJ6e421fabe2aa4155_SourceCache.poolSlots_injective a)]
    · rw [install_slot _ plI_inj, install_slot _ (PCJ6e421fabe2aa4155_SourceCache.poolSlots_injective a)]
  · intro j
    have hno : ∀ y, plI a k y ≠ plIn SB j := by
      intro y e
      have hv := congrArg Fin.val e
      rw [plIn_val] at hv
      simp only [plI] at hv
      have := y.isLt
      omega
    refine ⟨?_, ?_⟩
    · rw [install_other _ _ _ _ hno]
      unfold plIn
      rw [install_slot _ sbP_inj]
      exact k1 j
    · rw [dockH_other _ _ _ _ hno]
      unfold plIn
      rw [dockH_slot _ sbP_inj, Fin.addCases_right]

end pool

end
end NearCubicWires.SourceFactorSel.Item4

