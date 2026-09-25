import Proof.Rows.RowsI2cPoolBase

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

section
/- Copied from source-reuse-20260922/PCJ6e421fabe2aa4155_SourcePoolSeedShape.lean (namespace renamed; see module header). -/
namespace RowsConstruction.I2c.PoolSeedShape
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal RepairSource.VerifierDecoding
noncomputable section

def table {q : Nat} (live : Finset (Fin q)) (B w : Nat) (i : Fin 64) : List Bool:=
  if i=9 then List.replicate w true else
  if i=13 ∨ i=14 then ZeroPadding.pad (ConstantGateReusable.C w) (RepairOrdinary.frame (SignedSortKey.binary w 0)) else
  if i=39 ∨ i=45 then CloseoutRowsGateSupport.gateMembers live else
  if i=40 then List.replicate (ConstantGateReusable.C w) true else
  if i=41 then List.replicate (ConstantGateReusable.C w+1) false else
  if i=42 ∨ i=46 then CompareMachine.word q else
  if i=47 then List.replicate (ConstantGateReusable.E B q) false else
  if i=60 then List.replicate (PoolEntry.logCapacity B q) false else
  if i=0 ∨ i=34 ∨ i=43 ∨ i=44 ∨ (51≤ i.val ∧ i.val≤59) ∨ 61≤ i.val then [] else
  List.replicate (ConstantGateReusable.C w) false

theorem bank_eq {q : Nat} (live : Finset (Fin q)) (B w : Nat) :
    PoolEntryBaseline.bank live B w [] []=table live B w := by
  funext i
  fin_cases i
  · change PoolEntryBaseline.bank live B w [] [] (0 : Fin 64)=table live B w 0
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (0 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [show (0 : Fin 64)=PoolEntry.loadSlots 5 from rfl,install_slot _ PoolEntry.load_inj]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (1 : Fin 64)=table live B w 1
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (1 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (1 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (2 : Fin 64)=table live B w 2
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (2 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (2 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (3 : Fin 64)=table live B w 3
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (3 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (3 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (4 : Fin 64)=table live B w 4
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (4 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (4 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (5 : Fin 64)=table live B w 5
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (5 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (5 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (6 : Fin 64)=table live B w 6
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (6 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (6 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (7 : Fin 64)=table live B w 7
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (7 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (7 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (8 : Fin 64)=table live B w 8
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (8 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (8 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (9 : Fin 64)=table live B w 9
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (9 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (9 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (10 : Fin 64)=table live B w 10
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (10 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (10 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (11 : Fin 64)=table live B w 11
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (11 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (11 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (12 : Fin 64)=table live B w 12
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (12 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (12 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (13 : Fin 64)=table live B w 13
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (13 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (13 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (14 : Fin 64)=table live B w 14
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (14 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (14 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (15 : Fin 64)=table live B w 15
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (15 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (15 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (16 : Fin 64)=table live B w 16
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (16 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (16 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (17 : Fin 64)=table live B w 17
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (17 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (17 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (18 : Fin 64)=table live B w 18
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (18 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (18 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (19 : Fin 64)=table live B w 19
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (19 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (19 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (20 : Fin 64)=table live B w 20
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (20 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (20 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (21 : Fin 64)=table live B w 21
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (21 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (21 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (22 : Fin 64)=table live B w 22
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (22 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (22 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (23 : Fin 64)=table live B w 23
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (23 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (23 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (24 : Fin 64)=table live B w 24
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (24 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (24 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (25 : Fin 64)=table live B w 25
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (25 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (25 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (26 : Fin 64)=table live B w 26
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (26 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (26 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (27 : Fin 64)=table live B w 27
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (27 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (27 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (28 : Fin 64)=table live B w 28
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (28 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (28 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (29 : Fin 64)=table live B w 29
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (29 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (29 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (30 : Fin 64)=table live B w 30
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (30 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (30 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (31 : Fin 64)=table live B w 31
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (31 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (31 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (32 : Fin 64)=table live B w 32
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (32 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (32 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (33 : Fin 64)=table live B w 33
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (33 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (33 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (34 : Fin 64)=table live B w 34
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (34 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (34 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (35 : Fin 64)=table live B w 35
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (35 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (35 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (36 : Fin 64)=table live B w 36
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (36 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (36 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (37 : Fin 64)=table live B w 37
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (37 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (37 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (38 : Fin 64)=table live B w 38
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (38 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (38 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (39 : Fin 64)=table live B w 39
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (39 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (39 : Fin 64) (by decide)]
    change CloseoutRowsPoolWeight.mask (CloseoutRowsPoolMinimum.items (PoolEntryBaseline.seed q).gate live)=CloseoutRowsGateSupport.gateMembers live
    exact CloseoutRowsPoolMinimum.items_mask _ live
  · change PoolEntryBaseline.bank live B w [] [] (40 : Fin 64)=table live B w 40
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (40 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (40 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (41 : Fin 64)=table live B w 41
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (41 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (41 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (42 : Fin 64)=table live B w 42
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (42 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [show (42 : Fin 64)=PoolEntry.loadSlots 6 from rfl,install_slot _ PoolEntry.load_inj]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (43 : Fin 64)=table live B w 43
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (43 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (43 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (44 : Fin 64)=table live B w 44
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (44 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (44 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (45 : Fin 64)=table live B w 45
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (45 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (45 : Fin 64) (by decide)]
    change CloseoutRowsPoolWeight.mask (CloseoutRowsPoolMinimum.items (PoolEntryBaseline.seed q).gate live)=CloseoutRowsGateSupport.gateMembers live
    exact CloseoutRowsPoolMinimum.items_mask _ live
  · change PoolEntryBaseline.bank live B w [] [] (46 : Fin 64)=table live B w 46
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (46 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (46 : Fin 64) (by decide)]
    change CompareMachine.word (CloseoutRowsPoolMinimum.items (PoolEntryBaseline.seed q).gate live).length=CompareMachine.word q
    rw [CloseoutRowsPoolMinimum.items_length]
  · change PoolEntryBaseline.bank live B w [] [] (47 : Fin 64)=table live B w 47
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (47 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (47 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (48 : Fin 64)=table live B w 48
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (48 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [show (48 : Fin 64)=PoolEntry.loadSlots 2 from rfl,install_slot _ PoolEntry.load_inj]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (49 : Fin 64)=table live B w 49
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (49 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (49 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (50 : Fin 64)=table live B w 50
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (50 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (50 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (51 : Fin 64)=table live B w 51
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (51 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (51 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (52 : Fin 64)=table live B w 52
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (52 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (52 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (53 : Fin 64)=table live B w 53
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (53 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (53 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (54 : Fin 64)=table live B w 54
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (54 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (54 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (55 : Fin 64)=table live B w 55
    rw [PoolEntryBaseline.bank_source]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (56 : Fin 64)=table live B w 56
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (56 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [show (56 : Fin 64)=PoolEntry.loadSlots 1 from rfl,install_slot _ PoolEntry.load_inj]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (57 : Fin 64)=table live B w 57
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (57 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [show (57 : Fin 64)=PoolEntry.loadSlots 3 from rfl,install_slot _ PoolEntry.load_inj]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (58 : Fin 64)=table live B w 58
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (58 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [show (58 : Fin 64)=PoolEntry.loadSlots 4 from rfl,install_slot _ PoolEntry.load_inj]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (59 : Fin 64)=table live B w 59
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (59 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [show (59 : Fin 64)=PoolEntry.loadSlots 7 from rfl,install_slot _ PoolEntry.load_inj]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (60 : Fin 64)=table live B w 60
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (60 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [show (60 : Fin 64)=PoolEntry.loadSlots 8 from rfl,install_slot _ PoolEntry.load_inj]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (61 : Fin 64)=table live B w 61
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (61 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (61 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (62 : Fin 64)=table live B w 62
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (62 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (62 : Fin 64) (by decide)]
    rfl
  · change PoolEntryBaseline.bank live B w [] [] (63 : Fin 64)=table live B w 63
    rw [PoolEntryBaseline.bank,Function.update_of_ne (by decide : (63 : Fin 64)≠55)]
    unfold PoolEntry.input PoolEntry.initial
    rw [install_other PoolEntry.loadSlots _ _ (63 : Fin 64) (by decide)]
    rfl

end
end RowsConstruction.I2c.PoolSeedShape
end

section
/- Copied from source-reuse-20260922/PCJ6e421fabe2aa4155_SourcePoolSeedFanout.lean (namespace renamed; see module header). -/
namespace RowsConstruction.I2c.PoolSeedFanout
open NearCubicWires LocalBitMultitape ExtDecompositionBatch ExtIncidence RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound P1Closure RepairSource RepairSource.VerifierDecoding
noncomputable section

def masters {q : Nat} (live : Finset (Fin q)) (w : Nat) : Fin 5→List Bool:=
  ![List.replicate w true,RepairOrdinary.frame (SignedSortKey.binary w 0),
    CloseoutRowsGateSupport.gateMembers live,List.replicate (ConstantGateReusable.C w) true,
    CompareMachine.word q]
def select (i : Fin 64) : Option (Fin 5):=
  if i=9 then some 0 else if i=13 ∨ i=14 then some 1 else
  if i=39 ∨ i=45 then some 2 else if i=40 then some 3 else
  if i=42 ∨ i=46 then some 4 else none

theorem pad_pad (C D : Nat) (bits : List Bool) (h:C≤D) :
    ZeroPadding.pad D (ZeroPadding.pad C bits)=ZeroPadding.pad D bits := by
  simp only [ZeroPadding.pad,List.length_append,List.length_replicate,List.append_assoc]
  rw [←List.replicate_add]
  congr 2
  omega

theorem padded_table {q : Nat} (live : Finset (Fin q)) (B w P : Nat)
    (hc:ConstantGateReusable.C w+1≤P) (he:ConstantGateReusable.E B q≤P)
    (hl:PoolEntry.logCapacity B q≤P) (i : Fin 64) :
    ZeroPadding.pad P (RowsConstruction.I2c.PoolSeedShape.table live B w i)=
    ZeroPadding.pad P (NativeFanout.word select (masters live w) i) := by
  fin_cases i <;> first | rfl | exact pad_pad _ _ _ (by omega) |
    exact (pad_replicate_false _ _ (by omega))

theorem scalar_bounds (B q : Nat) :
    ConstantGateReusable.C (B+q+1)+1≤RowsConstruction.I2c.PoolCapacity.value B q ∧
    ConstantGateReusable.E B q≤RowsConstruction.I2c.PoolCapacity.value B q ∧
    PoolEntry.logCapacity B q≤RowsConstruction.I2c.PoolCapacity.value B q := by
  have hw:1≤B+q+1:=by omega
  have h2:B+q+1≤(B+q+1)^2:=by nlinarith
  have h3:(B+q+1)^2≤(B+q+1)^3:=by
    have h:=Nat.mul_le_mul_right ((B+q+1)^2) hw
    simpa only [one_mul,pow_succ,Nat.mul_comm] using h
  unfold ConstantGateReusable.C ConstantGateReusable.E PoolEntry.logCapacity
    RowsConstruction.I2c.PoolCapacity.value
  constructor
  · nlinarith
  constructor <;>nlinarith

end
end RowsConstruction.I2c.PoolSeedFanout
end

