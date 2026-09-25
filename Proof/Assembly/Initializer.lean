import Proof.Assembly.BankFamilyBankInitializer
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false
set_option linter.unusedSimpArgs false
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RecoveryExecution RepairSource.VerifierDecoding
open RepairRepresentation SourceInterfaces
open PCJ1fef9807c6954e94_Native
namespace PCJ34388a2fbfa9464b_
attribute [local irreducible] P1TopDownPaidPayload.tapes

noncomputable def machine (a : WilliamsAlgorithm) : Machine (PCJ515eaa990d75455b_FamilyInit.initTapes a) 39 := by
 unfold PCJ515eaa990d75455b_FamilyInit.initTapes
 exact Bank.machine (P1TopDownPaidPayload.tapes a)

theorem entry_heads (a : WilliamsAlgorithm) :
 PCJ515eaa990d75455b_FamilyInit.entryH a=
  (by unfold PCJ515eaa990d75455b_FamilyInit.initTapes; exact Bank.inputH (P1TopDownPaidPayload.tapes a)) := by
 unfold PCJ515eaa990d75455b_FamilyInit.entryH PCJ515eaa990d75455b_FamilyInit.initTapes
 apply funext; apply Bank.all (P1TopDownPaidPayload.tapes a)
 · intro i; simp [Bank.inputH,Bank.layout,Bank.pay]
 all_goals intro i; fin_cases i <;>
  simp [Bank.inputH,Bank.layout,Bank.cap,Bank.row,Bank.body,Bank.count,Bank.extra,Bank.source]

theorem entry_tapes (a : WilliamsAlgorithm) (m : PCJ515eaa990d75455b_FamilyInit.Scalars) (D : List Bool) :
 PCJ515eaa990d75455b_FamilyInit.entry a m D=
  (by unfold PCJ515eaa990d75455b_FamilyInit.initTapes; exact Bank.input (P1TopDownPaidPayload.tapes a) m D) := by
 unfold PCJ515eaa990d75455b_FamilyInit.entry PCJ515eaa990d75455b_FamilyInit.initTapes
 apply funext; apply Bank.all (P1TopDownPaidPayload.tapes a)
 · intro i
   have hn : i.val≠P1TopDownPaidPayload.tapes a+3 := by have hi:=i.isLt;omega
   simp [Bank.input,Bank.layout,Bank.pay,PCJ515eaa990d75455b_FamilyInit.sourcePort,Fin.ext_iff,hn]
 all_goals intro i; fin_cases i <;>
  simp [Bank.input,Bank.layout,Bank.cap,Bank.row,Bank.body,Bank.count,Bank.extra,Bank.source,
    PCJ515eaa990d75455b_FamilyInit.sourcePort,PCJ515eaa990d75455b_FamilyInit.drivers,Bank.values,Fin.ext_iff,Nat.add_assoc]

theorem exit_heads (a : WilliamsAlgorithm) :
 PCJ515eaa990d75455b_FamilyInit.exitH a=
  (by unfold PCJ515eaa990d75455b_FamilyInit.initTapes; exact Bank.finalH (P1TopDownPaidPayload.tapes a)) := by
 unfold PCJ515eaa990d75455b_FamilyInit.exitH PCJ515eaa990d75455b_FamilyInit.initTapes
 apply funext; apply Bank.all (P1TopDownPaidPayload.tapes a)
 · intro i
   simp [r_inputH,f_entry,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
    P1TopDownPaidReusable.source,P1TopDownPaidReusable.heads,P1TopDownPaidReusableBody.heads,
    P1Closure.RawRowJoin.heads,Bank.finalH,Bank.layout,Bank.pay]
 all_goals intro i; fin_cases i <;>
  simp [r_inputH,f_entry,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
    P1TopDownPaidReusable.source,P1TopDownPaidReusable.heads,P1TopDownPaidReusableBody.heads,
    P1Closure.RawRowJoin.heads,Bank.finalH,Bank.layout,
    Bank.cap,Bank.row,Bank.body,Bank.count,Bank.extra,Bank.source]

theorem exit_tapes (a : WilliamsAlgorithm) (m : PCJ515eaa990d75455b_FamilyInit.Scalars) (D : List Bool) :
 PCJ515eaa990d75455b_FamilyInit.exitT a m D=
  (by unfold PCJ515eaa990d75455b_FamilyInit.initTapes; exact Bank.bank (P1TopDownPaidPayload.tapes a) m D 7) := by
 unfold PCJ515eaa990d75455b_FamilyInit.exitT PCJ515eaa990d75455b_FamilyInit.initTapes
 apply funext; apply Bank.all (P1TopDownPaidPayload.tapes a)
 · intro i
   simp [PCJ515eaa990d75455b_FamilyInit.familyBank,P1TopDownPaidReusable.bank,P1TopDownPaidReusableBody.bank,
     P1Closure.RawRowJoin.bank,Bank.bank,Bank.layout,Bank.pay]
 all_goals intro i; fin_cases i <;>
  simp [PCJ515eaa990d75455b_FamilyInit.familyBank,P1TopDownPaidReusable.bank,P1TopDownPaidReusableBody.bank,
    P1Closure.RawRowJoin.bank,P1TopDownPaidFamilySum.extra,PCJ515eaa990d75455b_FamilyInit.drivers,Bank.values,
    Bank.bank,Bank.layout,Bank.cap,Bank.row,Bank.body,Bank.count,Bank.extra,Bank.source]

attribute [local irreducible] Step Bank.machine

theorem run (a : WilliamsAlgorithm) (m : PCJ515eaa990d75455b_FamilyInit.Scalars) (D : List Bool) :
 Step (machine a) (PCJ515eaa990d75455b_FamilyInit.initFuel a m) (PCJ515eaa990d75455b_FamilyInit.entryH a) (PCJ515eaa990d75455b_FamilyInit.entry a m D) (PCJ515eaa990d75455b_FamilyInit.exitH a) (PCJ515eaa990d75455b_FamilyInit.exitT a m D) := by
 unfold machine PCJ515eaa990d75455b_FamilyInit.initTapes
 rw [entry_heads,entry_tapes,exit_heads,exit_tapes]
 dsimp only [id,PCJ515eaa990d75455b_FamilyInit.initTapes]
 have h:=Bank.run (P1TopDownPaidPayload.tapes a) m D
 apply h.enlarge
 unfold PCJ515eaa990d75455b_FamilyInit.initFuel
 have hsmall : 4*(m.S+m.R+m.B+m.b+m.v+m.N+m.N*m.b)+24≤
   1000*(m.S+m.R+m.B+m.b+m.v+m.N+m.N*m.b+1) := by omega
 exact hsmall.trans (Nat.mul_le_mul_right _ (by omega : 1000≤1000*(r_tapes a+1)))

end PCJ34388a2fbfa9464b_
