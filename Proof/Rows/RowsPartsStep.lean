import Proof.Rows.RowsCompleteBank

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.PartsStep
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.P1Closure NearCubicWires.RepairOrdinary.CloseoutRowsEstimator
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open RowsConstruction.BaseLayout RowsConstruction.MaskStage RowsConstruction.CompleteWork
  RowsConstruction.CompleteRow RowsConstruction.CompleteBank
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section

/-! ## 1. The C3 bridge -/

section Bridge
variable {q Lq : Nat} (a : DecompositionAlgorithm) (F : Packets.Family q Lq) (g : Packets.Geometry F)
  (layout : Packets.Layout a F g) (facts : ∀ r ∈ F.rows, Packets.PacketFacts a F g r)
  (j : Fin F.rows.attach.length)

/-- **Field 8 of the row's datum is the printer-order selection word of the family row.** -/
theorem field8_grid :
    RowsRowLevel.fieldWord (RowsRowLevel.rowDatum a F g layout facts j) 8 =
      PCJ45bee56da9f34d5a_SelectionWord.gridWord (Packets.live F) (Packets.residual F) g.arity
        (PCJ38fbfed565f64139_Family.rowAt F j).val.select :=
  (RowsRowLevel.mask_field _).trans
    (PCJ45bee56da9f34d5a_SelectionWord.mask_cells_printerPoint (Packets.live F) (Packets.residual F) g.arity
      (PCJ38fbfed565f64139_Family.rowAt F j).val.select _ rfl _ rfl)

theorem residual_eq (g : Packets.Geometry F) : Packets.residual F = (Packets.live F)ᶜ.card := by
  rw [Finset.card_compl, Fintype.card_fin, g.card]

theorem rowAt_val (hj : j.val < F.rows.length) :
    (PCJ38fbfed565f64139_Family.rowAt F j).val = F.rows[j.val] := by
  simp [PCJ38fbfed565f64139_Family.rowAt]

theorem attach_lt : j.val < F.rows.length :=
  lt_of_lt_of_eq j.isLt List.length_attach

end Bridge

theorem gridWord_congr {n : Nat} (live : Finset (Fin n)) (s s' : Nat) (hs : s = s')
    (h : (s+1)/2+s/2 = liveᶜ.card) (h' : (s'+1)/2+s'/2 = liveᶜ.card) (sel : BitInput liveᶜ.card → Bool) :
    PCJ45bee56da9f34d5a_SelectionWord.gridWord live s h sel =
      PCJ45bee56da9f34d5a_SelectionWord.gridWord live s' h' sel := by
  subst hs
  rfl

theorem thr_hw8 (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (L target : Nat)
    (g : Packets.Geometry (Packets.thrFamily a r L target)) (layout : Packets.Layout a _ g)
    (facts : ∀ row ∈ (Packets.thrFamily a r L target).rows, Packets.PacketFacts a _ g row)
    (j : Fin (Packets.thrFamily a r L target).rows.attach.length) :
    thrW a r L target j.val (attach_lt _ j) =
      RowsRowLevel.fieldWord (RowsRowLevel.rowDatum a _ g layout facts j) 8 := by
  rw [field8_grid, rowAt_val _ j (attach_lt _ j)]
  exact gridWord_congr (thrLive r L) _ _ (residual_eq _ g).symm _ _ _

theorem sym_hw8 (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (L target : Nat)
    (g : Packets.Geometry (Packets.symFamily r L target)) (layout : Packets.Layout a _ g)
    (facts : ∀ row ∈ (Packets.symFamily r L target).rows, Packets.PacketFacts a _ g row)
    (j : Fin (Packets.symFamily r L target).rows.attach.length) :
    symW r L target j.val (attach_lt _ j) =
      RowsRowLevel.fieldWord (RowsRowLevel.rowDatum a _ g layout facts j) 8 := by
  rw [field8_grid, rowAt_val _ j (attach_lt _ j)]
  exact gridWord_congr (symLive r L) _ _ (residual_eq _ g).symm _ _ _

/-! ## 2. The `Parts` choices: row-level ports and the Header reserve -/

/-- The eight row-level work ports: `rowp` 0–7 (`RowsBaseLayout.rowpWords` holds their words at every row). -/
def rowsPorts (NI : Nat) : RowsRowLevel.RowPorts (rowsWork NI) where
  drv := rowpPort NI 0
  lg := rowpPort NI 1
  tpl := rowpPort NI 2
  tick := rowpPort NI 3
  cp := rowpPort NI 4
  ctr := rowpPort NI 5
  drvH := rowpPort NI 6
  lgH := rowpPort NI 7
  nodup := List.Nodup.map (rowpPort_injective NI) (by decide : ([0,1,2,3,4,5,6,7] : List (Fin 8)).Nodup)

def reserveOf (caps : RowCaps) (k : Fin 440) : Nat := by
  classical
  exact if PCJ45bee56da9f34d5a_HeaderErase.retained k then 0 else 2*caps.headerFuel

theorem reserveOf_retained (caps : RowCaps) (k : Fin 440) (hk : PCJ45bee56da9f34d5a_HeaderErase.retained k) :
    reserveOf caps k = 0 := by
  unfold reserveOf
  rw [if_pos hk]

theorem reserveOf_not_retained (caps : RowCaps) (k : Fin 440) (hk : ¬ PCJ45bee56da9f34d5a_HeaderErase.retained k) :
    reserveOf caps k = 2*caps.headerFuel := by
  unfold reserveOf
  rw [if_neg hk]

theorem reserveOf_mutable (caps : RowCaps) (i : Fin 430) :
    reserveOf caps (PCJ45bee56da9f34d5a_HeaderErase.mutable i) = 2*caps.headerFuel :=
  reserveOf_not_retained caps _ (PCJ45bee56da9f34d5a_HeaderErase.mutable_not_retained i)

/-! ## 3. The row-level premises from `RowCaps.Good` -/

/-- The row level's cost bound (uniform in the row): `HeaderField.budget ≤ 18K+14`, `rawBudget ≤ 34K+2`, `U = 2hF`. -/
def c1Bound (cC hF : Nat) : Nat :=
  (18*cC+14+1+(2*cC+4))+1+((2*(34*cC+2)+2)+1+(4*(2*hF)+9))

section RowLevel
variable (printer : WilliamsAlgorithm) (NI : Nat) {q Lq : Nat} (a : DecompositionAlgorithm) (F : Packets.Family q Lq)
  (g : Packets.Geometry F) (layout : Packets.Layout a F g) (caps : RowCaps)
  (base : Nat → Fin (rowWork (rowsWork NI)) → List Bool)
  (facts : ∀ r ∈ F.rows, Packets.PacketFacts a F g r) (j : Fin F.rows.attach.length) (out : List Bool)

/-- The exact row-level cost at `U = 2·headerFuel`. -/
abbrev c1Cost : Nat :=
  (PCJ45bee56da9f34d5a_HeaderField.budget (RowsRowLevel.rowDatum a F g layout facts j).row caps.copyCap+1+
    (2*caps.copyCap+4))+1+
    ((2*PCJ45bee56da9f34d5a_Constants.rawBudget (RowsRowLevel.rowDatum a F g layout facts j).row.p (RowsRowLevel.rowN F)
      (RowsRowLevel.rowDatum a F g layout facts j).Q (RowsRowLevel.rowDatum a F g layout facts j).C+2)+1+
      (4*(2*caps.headerFuel)+9))

theorem raw_le
    (hcopy : ∀ k, 2*(RowsRowLevel.fieldWord (RowsRowLevel.rowDatum a F g layout facts j) k).length+1 ≤ caps.copyCap) :
    PCJ45bee56da9f34d5a_Constants.rawBudget (RowsRowLevel.rowDatum a F g layout facts j).row.p (RowsRowLevel.rowN F)
      (RowsRowLevel.rowDatum a F g layout facts j).Q (RowsRowLevel.rowDatum a F g layout facts j).C ≤
      34*caps.copyCap+2 := by
  have h0 := hcopy 0
  have h1 := hcopy 1
  have h4 := hcopy 4
  have h6 := hcopy 6
  have h12 := hcopy 12
  have e0 : (RowsRowLevel.fieldWord (RowsRowLevel.rowDatum a F g layout facts j) 0).length =
      (Packets.residual F+1)/2 := List.length_replicate
  have e1 : (RowsRowLevel.fieldWord (RowsRowLevel.rowDatum a F g layout facts j) 1).length =
      (RowsRowLevel.rowDatum a F g layout facts j).row.p := List.length_replicate
  have e4 : (RowsRowLevel.fieldWord (RowsRowLevel.rowDatum a F g layout facts j) 4).length =
      (RowsRowLevel.rowDatum a F g layout facts j).C := List.length_replicate
  have e6 : (RowsRowLevel.fieldWord (RowsRowLevel.rowDatum a F g layout facts j) 6).length =
      (RowsRowLevel.rowDatum a F g layout facts j).Q := List.length_replicate
  have e12 : 3 ≤ (RowsRowLevel.fieldWord (RowsRowLevel.rowDatum a F g layout facts j) 12).length := by
    change 3 ≤ (frame (SignedSortKey.binary _ 1)).length
    rw [frame_length, SignedSortKey.binary_length]
    unfold NearCubicWires.RepairOrdinary.CompetitorSelectedCount.scalarWidth
    change 3 ≤ 2*((Packets.live F).card+1+_)+1
    omega
  unfold PCJ45bee56da9f34d5a_Constants.rawBudget RowsRowLevel.rowN
  omega

theorem c1_le
    (hcopy : ∀ k, 2*(RowsRowLevel.fieldWord (RowsRowLevel.rowDatum a F g layout facts j) k).length+1 ≤ caps.copyCap) :
    c1Cost a F g layout caps facts j ≤ c1Bound caps.copyCap caps.headerFuel := by
  have hH := PCJ45bee56da9f34d5a_HeaderBudget.budget_le (RowsRowLevel.rowDatum a F g layout facts j).row caps.copyCap
    (by have := hcopy 2; change 2*(Header.stream _).length+1 ≤ caps.copyCap at this; omega)
  have hR := raw_le a F g layout caps facts j hcopy
  unfold c1Cost c1Bound
  omega

/-- **The row level from `RowCaps.Good`**: rows-rowlevel `rowLevel_step` at the `rowpWords` resident words. -/
theorem rowLevel_good
    (hrowp : ∀ i, base j.val (rowpPort NI i) =
      rowpWords (RowsRowLevel.rowN F) layout.C caps.copyCap caps.headerFuel i)
    (hfit : ∀ i, 2*(PCJ38fbfed565f64139_Row.Frame.fields printer (RowsRowLevel.rowDatum a F g layout facts j) i).length+1
      ≤ caps.copyCap)
    (hhdr : PCJcc051fd4c1bd4540_Header.budget a F g layout (PCJ38fbfed565f64139_Family.rowAt F j).val ≤
      caps.headerFuel) :
    Step (RowsRowLevel.rowLevelMachine printer (rowsWork NI) (rowsPorts NI)) (c1Cost a F g layout caps facts j)
      (RowsRowLevel.entryH printer (rowsWork NI) a F g layout j out)
      (RowsRowLevel.entryA printer (rowsWork NI) (rowsPorts NI) a F g layout caps (reserveOf caps) base j out)
      (PCJ45bee56da9f34d5a_RowState.headBank printer (rowsWork NI) a F g (j.val+1) out)
      (RowsRowLevel.rowLevelOut printer (rowsWork NI) (rowsPorts NI) a F g layout caps (reserveOf caps) base facts
        j out) := by
  have hcopy := RowsRowLevel.field_fits printer (RowsRowLevel.rowDatum a F g layout facts j) caps.copyCap hfit
  have h1 : 1 ≤ PCJcc051fd4c1bd4540_Header.budget a F g layout (PCJ38fbfed565f64139_Family.rowAt F j).val := by
    unfold PCJcc051fd4c1bd4540_Header.budget CompactColdFamily.budget
    omega
  have hn : RowsRowLevel.rowN F = Packets.residual F := by
    unfold RowsRowLevel.rowN
    omega
  refine RowsRowLevel.rowLevel_step printer (rowsWork NI) (rowsPorts NI) a F g layout caps (reserveOf caps) base facts
    j out (2*caps.headerFuel) (3*caps.copyCap+2) (34*caps.copyCap+2) 0 0 hcopy (reserveOf_mutable caps)
    (by change PCJcc051fd4c1bd4540_Header.budget a F g layout _+1 ≤ _; omega)
    (by
      have := RowsRowLevel.ticks_le_cap (RowsRowLevel.rowDatum a F g layout facts j).row caps.copyCap (hcopy 2)
      omega)
    (by
      have := raw_le a F g layout caps facts j hcopy
      omega)
    ?_ ((hrowp 3).trans rfl) ?_ ((hrowp 5).trans rfl) ((hrowp 6).trans rfl) ((hrowp 7).trans rfl)
  · refine (hrowp 2).trans ?_
    rw [ZeroPadding.pad_zero]
    change UnaryTemplate.tape (2*((RowsRowLevel.rowN F+1)/2)-(decide (RowsRowLevel.rowN F%2=1)).toNat+2) =
      UnaryTemplate.tape (2*((Packets.residual F+1)/2)-(decide (Packets.residual F%2=1)).toNat+2)
    rw [hn]
  · refine (hrowp 4).trans ?_
    rw [ZeroPadding.pad_zero]
    rfl

end RowLevel

/-! ## 4. The resident C5 / mode words (`C5Ready`, supplied by RX's initializer) and the uniform fuel -/

def ThrC5Ready (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target NI : Nat) (init : Fin NI → List Bool) (iMode : Fin NI)
    (ini : Fin 40 → Fin NI) (ix : Fin 4 → Fin NI) (ib : Fin 82 → Fin NI) (iOne : Fin NI) (Rp : Nat) : Prop :=
  init iMode = [true] ∧ Function.Injective ini ∧
  (∀ m, init (ini m) = ThrKey.psInit (KeyTop.wT a r four L target) Rp (Rp+1) m) ∧
  Function.Injective ib ∧ ib 9 ≠ iOne ∧
  (∀ c, init (ix c) = KeyStep.fb (ThrWidth.T a r four L target) (ThrSel.bnd a r c)) ∧
  (∀ k : Fin 82, ¬ (73 ≤ k.val ∧ k.val < 77) → init (ib k) = ThrSelBase.baseInit a r four L target k) ∧
  init iOne = ZeroPadding.pad (ThrSelBase.bU (ThrWidth.T a r four L target)) (KeyStep.fb (KeyTop.wT a r four L target) 1)

/-- The SYM `init` words: the mode flag and RC5's `symInit`. -/
def SymC5Ready (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target NI : Nat) (init : Fin NI → List Bool) (iMode : Fin NI)
    (iniS : Fin 9 → Fin NI) : Prop :=
  init iMode = [false] ∧
  ∀ m, init (iniS m) = SymC5.symInit (SymC5.sw a r four L target) r.circuits.length (SymC5.sbnd r) m

/-- **The resident words `complete` reads, per request** (terminal: nothing; its family is empty). -/
def C5Ready (a : DecompositionAlgorithm) (NI : Nat) (init : Fin NI → List Bool) (iMode : Fin NI)
    (ini : Fin 40 → Fin NI) (ix : Fin 4 → Fin NI) (ib : Fin 82 → Fin NI) (iOne : Fin NI) (iniS : Fin 9 → Fin NI)
    (Rp : Nat) : Request → Prop
  | .terminal => True
  | .thr r four L target => ThrC5Ready a r four L target NI init iMode ini ix ib iOne Rp
  | .sym r four L target => SymC5Ready a r four L target NI init iMode iniS

/-- The uniform THR `complete` fuel (request constants and the two caps only). -/
def thrFuel (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target Rp cC hF : Nat) : Nat :=
  c1Bound cC hF+1+((thrMaskCost a r four L target+2)+1+((4*2^(thrLive r L)ᶜ.card+4)+1+
    (2*2^(thrLive r L)ᶜ.card+4+1+(ThrC5.c5Cost (KeyTop.wT a r four L target) (KeyTop.RT a r four L target)
      (natBitLength (KeyTop.NS a r L target)) (seedScratch (KeyTop.NS a r L target)) Rp
      (ThrWidth.T a r four L target) (ThrSelBase.bF (ThrWidth.T a r four L target))+2))))

/-- The uniform SYM `complete` fuel. -/
def symFuel (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target cC hF : Nat) : Nat :=
  c1Bound cC hF+1+((symMaskCost a r four L target+2)+1+((4*2^(symLive r L)ᶜ.card+4)+1+
    (2*2^(symLive r L)ᶜ.card+4+1+(SymC5.symCost (SymC5.sw a r four L target) (symRes r.q (symT a r four L target))
      (natBitLength (SymC5.sNS r L target)) (seedScratch (SymC5.sNS r L target))+2))))

/-- **`Parts.completeFuel`**: uniform in the row. -/
def fuelOf (a : DecompositionAlgorithm) (Rp : Request → Nat) : Request → RowCaps → Nat
  | .terminal, _ => 0
  | .thr r four L target, caps => thrFuel a r four L target (Rp (.thr r four L target)) caps.copyCap caps.headerFuel
  | .sym r four L target, caps => symFuel a r four L target caps.copyCap caps.headerFuel

/-! ## 5. The per-row step, THR and SYM -/

section Core
variable (printer : WilliamsAlgorithm) (NI : Nat) (a : DecompositionAlgorithm)
  (pub : Fin 2 → List Bool) (init : Fin NI → List Bool) (rcp : Fin 64 → List Bool) (caps : RowCaps)
  (iMode : Fin NI) (ini : Fin 40 → Fin NI) (ix : Fin 4 → Fin NI) (ib : Fin 82 → Fin NI) (iOne : Fin NI)
  (iniS : Fin 9 → Fin NI)

/-- **THR `complete` for row `j`**, from `complete`'s entry bank to the Frame input bank, at the uniform fuel. -/
theorem thr_core (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : Nat) (g : Packets.Geometry (Packets.thrFamily a r L target)) (layout : Packets.Layout a _ g)
    (facts : ∀ row ∈ (Packets.thrFamily a r L target).rows, Packets.PacketFacts a _ g row)
    (hfit : ∀ row (hr : row ∈ (Packets.thrFamily a r L target).rows) i,
      2*(PCJ38fbfed565f64139_Row.Frame.fields printer (Packets.datum a _ g layout row hr (facts row hr)) i).length+1
        ≤ caps.copyCap)
    (hhdr : ∀ row ∈ (Packets.thrFamily a r L target).rows,
      PCJcc051fd4c1bd4540_Header.budget a _ g layout row ≤ caps.headerFuel)
    (Rp : Nat) (hc5 : ThrC5Ready a r four L target NI init iMode ini ix ib iOne Rp)
    (hRp : ∀ p, p ≤ KeySucc.cut a r target →
      RowsConstruction.ThrPrime.psCost (KeyTop.wT a r four L target) (KeySucc.cut a r target) p + 1 ≤ Rp)
    (j : Fin (Packets.thrFamily a r L target).rows.attach.length) (out : List Bool) :
    Step (completeM printer NI (rowsPorts NI) iMode ini ix ib iOne iniS)
      (thrFuel a r four L target Rp caps.copyCap caps.headerFuel)
      (RowsRowLevel.entryH printer (rowsWork NI) a _ g layout j out)
      (RowsRowLevel.entryA printer (rowsWork NI) (rowsPorts NI) a _ g layout caps (reserveOf caps)
        (thrBase a r four L target NI pub init rcp layout.C caps.copyCap caps.headerFuel) j out)
      (PCJ45bee56da9f34d5a_RowState.headBank printer (rowsWork NI) a _ g (j.val+1) out)
      (install (RowsRowLevel.fieldSlot printer (rowWork (rowsWork NI)))
        (PCJ45bee56da9f34d5a_RowState.bank printer (rowsWork NI) a _ g layout caps (reserveOf caps)
          (thrBase a r four L target NI pub init rcp layout.C caps.copyCap caps.headerFuel)
          (rowsPorts NI).drv (rowsPorts NI).lg (j.val+1) out)
        (fun k => ZeroPadding.pad caps.copyCap
          (frame (RowsRowLevel.fieldWord (RowsRowLevel.rowDatum a _ g layout facts j) k)))) := by
  obtain ⟨hmode, hini, hinit, hib, hone, hinitD, hinitB, hinitO⟩ := hc5
  have hj := attach_lt _ j
  have hrc := fun i => (thr_base_rc a r four L target NI pub init rcp layout.C caps.copyCap caps.headerFuel i).2.2.1
  obtain ⟨_, hd, hg⟩ := thr_blank a r four L target NI pub init rcp layout.C caps.copyCap caps.headerFuel j.val hj
  have hcopy := RowsRowLevel.field_fits printer (RowsRowLevel.rowDatum a _ g layout facts j) caps.copyCap
    (hfit _ (PCJ38fbfed565f64139_Family.rowAt _ j).property)
  have hRL := rowLevel_good printer NI a _ g layout caps
    (thrBase a r four L target NI pub init rcp layout.C caps.copyCap caps.headerFuel) facts j out
    (hrc j.val) (hfit _ (PCJ38fbfed565f64139_Family.rowAt _ j).property)
    (hhdr _ (PCJ38fbfed565f64139_Family.rowAt _ j).property)
  have hW1 := thr_w1 a r four L target NI pub init rcp layout.C caps.copyCap caps.headerFuel j.val hj iMode hmode
  have hW2 := thr_w2 a r four L target NI pub init rcp layout.C caps.copyCap caps.headerFuel j.val hj iMode hmode
    ini hini Rp (Rp+1) hinit hRp (le_refl _) ix ib iOne hib hone hinitD hinitB hinitO iniS
  have st := complete_row printer NI (rowsPorts NI) a _ g layout caps (reserveOf caps)
    (thrBase a r four L target NI pub init rcp layout.C caps.copyCap caps.headerFuel) facts j out
    (fun i => (hrc i 0).trans rfl) (fun i => (hrc i 1).trans rfl) iMode ini ix ib iOne iniS
    (thrLive r L)ᶜ.card (thrW a r L target j.val hj)
    (PCJ45bee56da9f34d5a_SelectionWord.gridWord_length _ _ _ _) (thr_hw8 a r L target g layout facts j) hd hg
    _ _ _ hRL hW1 hW2
  refine st.enlarge ?_
  have hc1 := c1_le a _ g layout caps facts j hcopy
  unfold thrFuel
  omega

/-- **SYM `complete` for row `j`**, at the uniform fuel. -/
theorem sym_core (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : Nat) (g : Packets.Geometry (Packets.symFamily r L target)) (layout : Packets.Layout a _ g)
    (facts : ∀ row ∈ (Packets.symFamily r L target).rows, Packets.PacketFacts a _ g row)
    (hfit : ∀ row (hr : row ∈ (Packets.symFamily r L target).rows) i,
      2*(PCJ38fbfed565f64139_Row.Frame.fields printer (Packets.datum a _ g layout row hr (facts row hr)) i).length+1
        ≤ caps.copyCap)
    (hhdr : ∀ row ∈ (Packets.symFamily r L target).rows,
      PCJcc051fd4c1bd4540_Header.budget a _ g layout row ≤ caps.headerFuel)
    (hc5 : SymC5Ready a r four L target NI init iMode iniS)
    (j : Fin (Packets.symFamily r L target).rows.attach.length) (out : List Bool) :
    Step (completeM printer NI (rowsPorts NI) iMode ini ix ib iOne iniS)
      (symFuel a r four L target caps.copyCap caps.headerFuel)
      (RowsRowLevel.entryH printer (rowsWork NI) a _ g layout j out)
      (RowsRowLevel.entryA printer (rowsWork NI) (rowsPorts NI) a _ g layout caps (reserveOf caps)
        (symBase a r four L target NI pub init rcp layout.C caps.copyCap caps.headerFuel) j out)
      (PCJ45bee56da9f34d5a_RowState.headBank printer (rowsWork NI) a _ g (j.val+1) out)
      (install (RowsRowLevel.fieldSlot printer (rowWork (rowsWork NI)))
        (PCJ45bee56da9f34d5a_RowState.bank printer (rowsWork NI) a _ g layout caps (reserveOf caps)
          (symBase a r four L target NI pub init rcp layout.C caps.copyCap caps.headerFuel)
          (rowsPorts NI).drv (rowsPorts NI).lg (j.val+1) out)
        (fun k => ZeroPadding.pad caps.copyCap
          (frame (RowsRowLevel.fieldWord (RowsRowLevel.rowDatum a _ g layout facts j) k)))) := by
  obtain ⟨hmode, hinitS⟩ := hc5
  have hj := attach_lt _ j
  have hrc := fun i => (sym_base_rc a r four L target NI pub init rcp layout.C caps.copyCap caps.headerFuel i).2.2.1
  obtain ⟨_, hd, hg⟩ := sym_blank a r four L target NI pub init rcp layout.C caps.copyCap caps.headerFuel j.val hj
  have hcopy := RowsRowLevel.field_fits printer (RowsRowLevel.rowDatum a _ g layout facts j) caps.copyCap
    (hfit _ (PCJ38fbfed565f64139_Family.rowAt _ j).property)
  have hRL := rowLevel_good printer NI a _ g layout caps
    (symBase a r four L target NI pub init rcp layout.C caps.copyCap caps.headerFuel) facts j out
    (hrc j.val) (hfit _ (PCJ38fbfed565f64139_Family.rowAt _ j).property)
    (hhdr _ (PCJ38fbfed565f64139_Family.rowAt _ j).property)
  have hW1 := sym_w1 a r four L target NI pub init rcp layout.C caps.copyCap caps.headerFuel j.val hj iMode hmode
  have hW2 := sym_w2 a r four L target NI pub init rcp layout.C caps.copyCap caps.headerFuel j.val hj iMode hmode
    ini ix ib iOne iniS hinitS
  have st := complete_row printer NI (rowsPorts NI) a _ g layout caps (reserveOf caps)
    (symBase a r four L target NI pub init rcp layout.C caps.copyCap caps.headerFuel) facts j out
    (fun i => (hrc i 0).trans rfl) (fun i => (hrc i 1).trans rfl) iMode ini ix ib iOne iniS
    (symLive r L)ᶜ.card (symW r L target j.val hj)
    (PCJ45bee56da9f34d5a_SelectionWord.gridWord_length _ _ _ _) (sym_hw8 a r L target g layout facts j) hd hg
    _ _ _ hRL hW1 hW2
  refine st.enlarge ?_
  have hc1 := c1_le a _ g layout caps facts j hcopy
  unfold symFuel
  omega

end Core

/-! ## 6. The restatement at `Row.headerOutH/A → Row.frameInH/A` (the `Parts.hstep` shape) -/

/-- Any step from `entryH/entryA` to the Frame input bank of row `j` IS a `Parts.hstep` instance. -/
theorem hstep_form (printer : WilliamsAlgorithm) (NI : Nat) {q Lq : Nat} (a : DecompositionAlgorithm)
    (F : Packets.Family q Lq) (g : Packets.Geometry F) (layout : Packets.Layout a F g)
    (facts : ∀ r ∈ F.rows, Packets.PacketFacts a F g r) (caps : RowCaps) (reserve : Fin 440 → Nat)
    (base : Nat → Fin (rowWork (rowsWork NI)) → List Bool) (completeStates : Nat)
    (complete : Machine (rowTapes printer (rowsWork NI)) completeStates) (completeFuel rowFuel n : Nat)
    (j : Fin F.rows.attach.length) (out : List Bool) (hcap : 1 ≤ caps.copyCap)
    (h : Step complete n
      (RowsRowLevel.entryH printer (rowsWork NI) a F g layout j out)
      (RowsRowLevel.entryA printer (rowsWork NI) (rowsPorts NI) a F g layout caps reserve base j out)
      (PCJ45bee56da9f34d5a_RowState.headBank printer (rowsWork NI) a F g (j.val+1) out)
      (install (RowsRowLevel.fieldSlot printer (rowWork (rowsWork NI)))
        (PCJ45bee56da9f34d5a_RowState.bank printer (rowsWork NI) a F g layout caps reserve base
          (rowsPorts NI).drv (rowsPorts NI).lg (j.val+1) out)
        (fun k => ZeroPadding.pad caps.copyCap
          (frame (RowsRowLevel.fieldWord (RowsRowLevel.rowDatum a F g layout facts j) k))))) :
    Step complete n
      (PCJ38fbfed565f64139_Row.headerOutH printer
        (PCJ38fbfed565f64139_Ready.code
          (PCJ45bee56da9f34d5a_RowReady.prog printer (rowsWork NI) (rowsPorts NI).drv (rowsPorts NI).lg
            completeStates complete))
        a F g layout (PCJ45bee56da9f34d5a_RowReady.rw F j).val
        (PCJ45bee56da9f34d5a_RowReady.bnk printer (rowsWork NI) a F g layout facts caps reserve base
          (rowsPorts NI).drv (rowsPorts NI).lg completeFuel rowFuel j out)
        (PCJ38fbfed565f64139_Family.rawBefore a F g j.val)
        (PCJ38fbfed565f64139_Family.rawAfter a F g j.val))
      (PCJ38fbfed565f64139_Row.headerOutA printer
        (PCJ38fbfed565f64139_Ready.code
          (PCJ45bee56da9f34d5a_RowReady.prog printer (rowsWork NI) (rowsPorts NI).drv (rowsPorts NI).lg
            completeStates complete))
        a F g layout (PCJ45bee56da9f34d5a_RowReady.rw F j).val
        (PCJ45bee56da9f34d5a_RowReady.bnk printer (rowsWork NI) a F g layout facts caps reserve base
          (rowsPorts NI).drv (rowsPorts NI).lg completeFuel rowFuel j out)
        (PCJ38fbfed565f64139_Family.rawBefore a F g j.val)
        (PCJ38fbfed565f64139_Family.rawAfter a F g j.val))
      (PCJ38fbfed565f64139_Row.frameInH printer
        (PCJ38fbfed565f64139_Ready.code
          (PCJ45bee56da9f34d5a_RowReady.prog printer (rowsWork NI) (rowsPorts NI).drv (rowsPorts NI).lg
            completeStates complete))
        (PCJ45bee56da9f34d5a_RowReady.bnk printer (rowsWork NI) a F g layout facts caps reserve base
          (rowsPorts NI).drv (rowsPorts NI).lg completeFuel rowFuel j out) out)
      (PCJ38fbfed565f64139_Row.frameInA printer
        (PCJ38fbfed565f64139_Ready.code
          (PCJ45bee56da9f34d5a_RowReady.prog printer (rowsWork NI) (rowsPorts NI).drv (rowsPorts NI).lg
            completeStates complete))
        a F g layout (PCJ45bee56da9f34d5a_RowReady.rw F j).val (PCJ45bee56da9f34d5a_RowReady.rw F j).property
        (facts (PCJ45bee56da9f34d5a_RowReady.rw F j).val (PCJ45bee56da9f34d5a_RowReady.rw F j).property)
        (PCJ45bee56da9f34d5a_RowReady.bnk printer (rowsWork NI) a F g layout facts caps reserve base
          (rowsPorts NI).drv (rowsPorts NI).lg completeFuel rowFuel j out) out) := by
  have f := RowsRowLevel.rowFrameIn_eq printer a F g layout (rowsWork NI) caps reserve base (rowsPorts NI).drv
    (rowsPorts NI).lg completeFuel rowFuel
    (PCJ45bee56da9f34d5a_RowReady.prog printer (rowsWork NI) (rowsPorts NI).drv (rowsPorts NI).lg completeStates complete)
    facts j out hcap
  exact h.congr f.2.symm f.1.symm

end
end RowsConstruction.PartsStep
