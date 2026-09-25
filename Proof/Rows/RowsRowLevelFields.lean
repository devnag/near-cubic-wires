import Proof.Rows.RowState

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsRowLevel
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.P1Closure
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimator
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open CompetitorCrossScheduler (producer)
attribute [local irreducible] CompetitorCrossScheduler.producer
noncomputable section

variable (printer : WilliamsAlgorithm)

/-! ## 1. The thirteen field ports of the Frame payload -/

/-- Prepare port `m` (the 64 scanned Prepare ports open the payload). -/
def prepPort (m : Fin 64) : Fin (P1TopDownPaidPayload.tapes printer) :=
  P1TopDownPaidReloadCore.scanSlots printer m

/-- `Scanned.extra` port `e` (payload ports 64..69). -/
def extraPort (e : Fin 6) : Fin (P1TopDownPaidPayload.tapes printer) :=
  Paid.old printer (producer printer) (WarmPrepare.old (producer printer)
    ((e.natAdd 64).castAdd (CloseoutRowsRawRecord.tapes (producer printer))))

/-- Warm field port `k` (`WarmFields.words … k`). -/
def warmPort (k : Fin 7) : Fin (P1TopDownPaidPayload.tapes printer) :=
  Paid.old printer (producer printer) (WarmPrepare.source (producer printer) k)

/-- The thirteen payload ports whose datum field is not blank, in the order
`1^d, 1^p, Header.stream, [odd], 1^C, 0^C` then the seven warm fields. -/
def fieldPort : Fin 13 → Fin (P1TopDownPaidPayload.tapes printer) :=
  ![prepPort printer 0,prepPort printer 17,prepPort printer 52,prepPort printer 54,
    extraPort printer 4,extraPort printer 5,
    warmPort printer 0,warmPort printer 1,warmPort printer 2,warmPort printer 3,
    warmPort printer 4,warmPort printer 5,warmPort printer 6]

/-- The thirteen field words of a datum, in `fieldPort` order. -/
def fieldWord (d : P1TopDownPaidReusable.Datum) : Fin 13 → List Bool :=
  ![List.replicate d.row.d true,List.replicate d.row.p true,Header.stream d.row,[d.row.odd],
    List.replicate d.C true,List.replicate d.C false,
    WarmFields.words d.row d.Q P1TopDownPaidPayload.estimate 1 d.select 0,
    WarmFields.words d.row d.Q P1TopDownPaidPayload.estimate 1 d.select 1,
    WarmFields.words d.row d.Q P1TopDownPaidPayload.estimate 1 d.select 2,
    WarmFields.words d.row d.Q P1TopDownPaidPayload.estimate 1 d.select 3,
    WarmFields.words d.row d.Q P1TopDownPaidPayload.estimate 1 d.select 4,
    WarmFields.words d.row d.Q P1TopDownPaidPayload.estimate 1 d.select 5,
    WarmFields.words d.row d.Q P1TopDownPaidPayload.estimate 1 d.select 6]

/-- Offset of the seven warm ports. -/
abbrev warmBase : Nat := Reuse.tapes (producer printer)

theorem warmBase_ge : 73 ≤ warmBase printer := by
  unfold warmBase Reuse.tapes WholePrefix.tapes
  omega

theorem fieldPort_val (k : Fin 13) :
    (fieldPort printer k).val =
      (![0,17,52,54,68,69,warmBase printer,warmBase printer+1,warmBase printer+2,
        warmBase printer+3,warmBase printer+4,warmBase printer+5,warmBase printer+6] : Fin 13 → Nat) k := by
  fin_cases k <;> rfl

theorem fieldPort_injective : Function.Injective (fieldPort printer) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [fieldPort_val,fieldPort_val] at hv
  have hb := warmBase_ge printer
  fin_cases i <;> fin_cases j <;> simp at hv ⊢ <;> omega

/-! ## 2. `datumFields` at every payload port -/

variable (d : P1TopDownPaidReusable.Datum)

theorem datum_prep (m : Fin 64) :
    PCJeb9c0f0306e9481c_FramingSpec.datumFields printer d (prepPort printer m)=Prepare.input d.row m := by
  change P1TopDownPaidReloadCore.bank printer (Prepare.input d.row) d.C
    (WarmFields.words d.row d.Q P1TopDownPaidPayload.estimate 1 d.select)
    (P1TopDownPaidReloadCore.scanSlots printer m)=_
  exact P1TopDownPaidReloadCore.bank_scan printer _ _ _ m

theorem datum_extra (e : Fin 6) :
    PCJeb9c0f0306e9481c_FramingSpec.datumFields printer d (extraPort printer e)=Scanned.extra d.C e := by
  change P1TopDownPaidReloadCore.bank printer (Prepare.input d.row) d.C
    (WarmFields.words d.row d.Q P1TopDownPaidPayload.estimate 1 d.select) (extraPort printer e)=_
  simp only [P1TopDownPaidReloadCore.bank,extraPort,Paid.old,WarmPrepare.old,WarmPrepare.data,
    WarmPrepare.bank,Reuse.old,Fin.addCases_left,Fin.addCases_right]

theorem datum_warm (k : Fin 7) :
    PCJeb9c0f0306e9481c_FramingSpec.datumFields printer d (warmPort printer k)=
      WarmFields.words d.row d.Q P1TopDownPaidPayload.estimate 1 d.select k := by
  change P1TopDownPaidReloadCore.bank printer (Prepare.input d.row) d.C
    (WarmFields.words d.row d.Q P1TopDownPaidPayload.estimate 1 d.select) (warmPort printer k)=_
  simp only [P1TopDownPaidReloadCore.bank,warmPort,Paid.old,WarmPrepare.source,WarmPrepare.data,
    Fin.addCases_left,Fin.addCases_right]

theorem datum_field (k : Fin 13) :
    PCJeb9c0f0306e9481c_FramingSpec.datumFields printer d (fieldPort printer k) = fieldWord d k := by
  fin_cases k
  · exact (datum_prep printer d 0).trans rfl
  · exact (datum_prep printer d 17).trans rfl
  · exact (datum_prep printer d 52).trans rfl
  · exact (datum_prep printer d 54).trans rfl
  · exact (datum_extra printer d 4).trans rfl
  · exact (datum_extra printer d 5).trans rfl
  · exact datum_warm printer d 0
  · exact datum_warm printer d 1
  · exact datum_warm printer d 2
  · exact datum_warm printer d 3
  · exact datum_warm printer d 4
  · exact datum_warm printer d 5
  · exact datum_warm printer d 6

/-- Every payload port off `fieldPort` carries the empty datum field. -/
theorem datum_blank (i : Fin (P1TopDownPaidPayload.tapes printer))
    (hi : ∀ k,fieldPort printer k≠i) :
    PCJeb9c0f0306e9481c_FramingSpec.datumFields printer d i=[] := by
  change P1TopDownPaidReloadCore.bank printer (Prepare.input d.row) d.C
    (WarmFields.words d.row d.Q P1TopDownPaidPayload.estimate 1 d.select) i=[]
  revert hi
  refine Fin.addCases (m:=WarmPrepare.tapes (producer printer)) (n:=ScannedClean.tapes printer)
    (motive:=fun i=>(∀ k,fieldPort printer k≠i) →
      P1TopDownPaidReloadCore.bank printer (Prepare.input d.row) d.C
        (WarmFields.words d.row d.Q P1TopDownPaidPayload.estimate 1 d.select) i=[])
    (fun j hj=>?_) (fun j _=>?_) i
  · rw [P1TopDownPaidReloadCore.bank,Fin.addCases_left]
    revert hj
    refine Fin.addCases (m:=Reuse.tapes (producer printer)) (n:=7)
      (motive:=fun j=>(∀ k,fieldPort printer k≠
          (j.castAdd (ScannedClean.tapes printer) : Fin (P1TopDownPaidPayload.tapes printer))) →
        WarmPrepare.data (producer printer) _ 0 0 _ j=[])
      (fun j hj=>?_) (fun k hk=>?_) j
    · rw [WarmPrepare.data,Fin.addCases_left]
      revert hj
      refine Fin.addCases (m:=WholePrefix.tapes (producer printer)+1) (n:=2)
        (motive:=fun j=>(∀ k,fieldPort printer k≠
            (((j.castAdd 7).castAdd (ScannedClean.tapes printer)) : Fin (P1TopDownPaidPayload.tapes printer))) →
          WarmPrepare.bank (producer printer) _ 0 0 j=[])
        (fun j hj=>?_) (fun k _=>?_) j
      · rw [WarmPrepare.bank,Fin.addCases_left]
        revert hj
        refine Fin.addCases (m:=WholePrefix.tapes (producer printer)) (n:=1)
          (motive:=fun j=>(∀ k,fieldPort printer k≠
              ((((j.castAdd 2).castAdd 7).castAdd (ScannedClean.tapes printer)) :
                Fin (P1TopDownPaidPayload.tapes printer))) →
            Fin.addCases (m:=WholePrefix.tapes (producer printer)) (n:=1)
              (motive:=fun _=>List Bool) _ (fun _ : Fin 1=>List.replicate 0 false) j=[])
          (fun j hj=>?_) (fun k _=>?_) j
        · rw [Fin.addCases_left]
          revert hj
          refine Fin.addCases (m:=70) (n:=CloseoutRowsRawRecord.tapes (producer printer))
            (motive:=fun j=>(∀ k,fieldPort printer k≠
                (((((j.castAdd 1).castAdd 2).castAdd 7).castAdd (ScannedClean.tapes printer)) :
                  Fin (P1TopDownPaidPayload.tapes printer))) →
              Fin.addCases (m:=70) (n:=CloseoutRowsRawRecord.tapes (producer printer))
                (motive:=fun _=>List Bool) _ (fun _=>[]) j=[])
            (fun j hj=>?_) (fun k _=>?_) j
          · rw [Fin.addCases_left]
            revert hj
            refine Fin.addCases (m:=64) (n:=6)
              (motive:=fun j=>(∀ k,fieldPort printer k≠
                  ((((((j.castAdd (CloseoutRowsRawRecord.tapes (producer printer))).castAdd 1).castAdd 2).castAdd 7).castAdd
                    (ScannedClean.tapes printer)) : Fin (P1TopDownPaidPayload.tapes printer))) →
                Fin.addCases (m:=64) (n:=6) (motive:=fun _=>List Bool) (Prepare.input d.row)
                  (Scanned.extra d.C) j=[])
              (fun m hm=>?_) (fun e he=>?_) j
            · rw [Fin.addCases_left]
              have h0 : m≠0 := by
                rintro rfl
                exact hm 0 rfl
              have h17 : m≠17 := by
                rintro rfl
                exact hm 1 rfl
              have h52 : m≠52 := by
                rintro rfl
                exact hm 2 rfl
              have h54 : m≠54 := by
                rintro rfl
                exact hm 3 rfl
              simp only [Prepare.input,if_neg h0,if_neg h17,if_neg h52,if_neg h54]
            · rw [Fin.addCases_right]
              fin_cases e
              · rfl
              · rfl
              · rfl
              · rfl
              · exact (he 4 rfl).elim
              · exact (he 5 rfl).elim
          · rw [Fin.addCases_right]
        · rw [Fin.addCases_right]
          rfl
      · rw [WarmPrepare.bank,Fin.addCases_right]
        fin_cases k <;> rfl
    · exfalso
      fin_cases k
      · exact hk 6 rfl
      · exact hk 7 rfl
      · exact hk 8 rfl
      · exact hk 9 rfl
      · exact hk 10 rfl
      · exact hk 11 rfl
      · exact hk 12 rfl
  · rw [P1TopDownPaidReloadCore.bank,Fin.addCases_right]

/-! ## 3. The Frame input bank of `complete`'s exit -/

attribute [local irreducible] P1TopDownPaidPayload.tapes

/-- The row-bank slot of payload port `i`. -/
def payloadSlot (t : Nat) (i : Fin (P1TopDownPaidPayload.tapes printer)) :
    Fin (PCJ38fbfed565f64139_Ready.tapes printer t) :=
  PCJ38fbfed565f64139_Ready.frameSlots printer t (i.castAdd 2)

/-- The row-bank slot of field `k`. -/
def fieldSlot (t : Nat) (k : Fin 13) : Fin (PCJ38fbfed565f64139_Ready.tapes printer t) :=
  payloadSlot printer t (fieldPort printer k)

theorem payloadSlot_val (t : Nat) (i : Fin (P1TopDownPaidPayload.tapes printer)) :
    (payloadSlot printer t i).val=440+i.val := rfl

theorem payloadSlot_injective (t : Nat) : Function.Injective (payloadSlot printer t) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [payloadSlot_val,payloadSlot_val] at hv
  exact Fin.ext (by omega)

theorem fieldSlot_injective (t : Nat) : Function.Injective (fieldSlot printer t) :=
  fun _ _ h=>fieldPort_injective printer (payloadSlot_injective printer t h)

theorem frame_blank (cap : Nat) (h : 1 ≤ cap) :
    ZeroPadding.pad cap (frame [])=List.replicate cap false := by
  have hf : frame ([] : List Bool)=[false] := rfl
  rw [hf,ZeroPadding.pad]
  obtain ⟨c,rfl⟩ : ∃ c,cap=c+1 := ⟨cap-1,by omega⟩
  simp [List.replicate_succ]

variable {q Lq : Nat} (a : DecompositionAlgorithm) (F : PCJ9eff70d512234a4c_Fixed.Packets.Family q Lq)
  (g : PCJ9eff70d512234a4c_Fixed.Packets.Geometry F) (layout : PCJ9eff70d512234a4c_Fixed.Packets.Layout a F g)

/-- **C7.** `frameInA` is the ambient Frame bank with exactly the thirteen framed fields
installed, whenever the ambient holds the RowState's cleared Frame block. -/
theorem frameIn_eq {t : Nat} (p : PCJ38fbfed565f64139_Ready.Program printer t)
    (r : PCJ9eff70d512234a4c_Fixed.Packets.Row F.occurrences Lq) (hr : r∈F.rows)
    (facts : PCJ9eff70d512234a4c_Fixed.Packets.PacketFacts a F g r)
    (b : PCJ38fbfed565f64139_Row.Banks printer (PCJ38fbfed565f64139_Ready.tapes printer t))
    (out : List Bool)
    (hres : ∀ i,b.fieldReserve i=b.copyCap) (hcap : 1 ≤ b.copyCap)
    (hpay : ∀ i,b.frameA (payloadSlot printer t i)=List.replicate b.copyCap false)
    (hdesc : b.frameA (PCJ38fbfed565f64139_Ready.descriptor printer t)=
      ZeroPadding.pad b.descriptorReserve out)
    (hctr : b.frameA (PCJ38fbfed565f64139_Ready.frameSlots printer t
      (PCJeb9c0f0306e9481c_FramingSpec.counter (P1TopDownPaidPayload.tapes printer)))=
      List.replicate b.copyCap false) :
    PCJ38fbfed565f64139_Row.frameInA printer (PCJ38fbfed565f64139_Ready.code p) a F g layout r hr facts b out=
      install (fieldSlot printer t) b.frameA
        (fun k=>ZeroPadding.pad b.copyCap
          (frame (fieldWord (PCJ9eff70d512234a4c_Fixed.Packets.datum a F g layout r hr facts) k))) := by
  classical
  funext x
  by_cases hx : ∃ i,PCJ38fbfed565f64139_Ready.frameSlots printer t i=x
  · obtain ⟨i,rfl⟩ := hx
    change install (PCJ38fbfed565f64139_Ready.frameSlots printer t) b.frameA _
      (PCJ38fbfed565f64139_Ready.frameSlots printer t i)=_
    rw [install_slot _ (PCJ38fbfed565f64139_Ready.frame_injective printer t)]
    refine Fin.addCases (m:=P1TopDownPaidPayload.tapes printer) (n:=2)
      (motive:=fun i=>ZeroPadding.pad (PCJ38fbfed565f64139_Row.Frame.targetReserve
          (P1TopDownPaidPayload.tapes printer) b.descriptorReserve i)
        (PCJ38fbfed565f64139_Row.Frame.bank b.fieldReserve
          (PCJ38fbfed565f64139_Row.Frame.fields printer
            (PCJ9eff70d512234a4c_Fixed.Packets.datum a F g layout r hr facts)) out b.copyCap i)=
        install (fieldSlot printer t) b.frameA
          (fun k=>ZeroPadding.pad b.copyCap
            (frame (fieldWord (PCJ9eff70d512234a4c_Fixed.Packets.datum a F g layout r hr facts) k)))
          (PCJ38fbfed565f64139_Ready.frameSlots printer t i))
      (fun m=>?_) (fun e=>?_) i
    · have hz : PCJ38fbfed565f64139_Row.Frame.targetReserve (P1TopDownPaidPayload.tapes printer)
          b.descriptorReserve (m.castAdd 2)=0 := by
        simp only [PCJ38fbfed565f64139_Row.Frame.targetReserve,Fin.val_castAdd]
        rw [if_neg (Nat.ne_of_lt m.isLt)]
      rw [hz,ZeroPadding.pad_zero]
      simp only [PCJ38fbfed565f64139_Row.Frame.bank,PCJeb9c0f0306e9481c_FramingSpec.paddedBank,
        Fin.addCases_left,hres]
      by_cases hm : ∃ k,fieldPort printer k=m
      · obtain ⟨k,rfl⟩ := hm
        rw [show PCJ38fbfed565f64139_Ready.frameSlots printer t ((fieldPort printer k).castAdd 2)=
            fieldSlot printer t k from rfl,install_slot _ (fieldSlot_injective printer t)]
        rw [PCJ38fbfed565f64139_Row.Frame.fields,datum_field]
      · have hk : ∀ k,fieldPort printer k≠m := fun k he=>hm ⟨k,he⟩
        rw [install_other (fieldSlot printer t) _ _ _ (fun k he=>hk k
          (Fin.castAdd_injective _ _ (PCJ38fbfed565f64139_Ready.frame_injective printer t he)))]
        rw [PCJ38fbfed565f64139_Row.Frame.fields,datum_blank printer _ m hk,frame_blank _ hcap]
        exact (hpay m).symm
    · have hne : ∀ k,fieldSlot printer t k≠
          PCJ38fbfed565f64139_Ready.frameSlots printer t (e.natAdd (P1TopDownPaidPayload.tapes printer)) := by
        intro k he
        have hv := congrArg Fin.val he
        simp only [fieldSlot,payloadSlot,PCJ38fbfed565f64139_Ready.frameSlots,Fin.val_castAdd,
          Fin.val_natAdd] at hv
        have := (fieldPort printer k).isLt
        omega
      rw [install_other (fieldSlot printer t) _ _ _ hne]
      obtain rfl | rfl : e=0 ∨ e=1 := by
        rcases e with ⟨v,hv⟩
        rcases v with _ | _ | v
        · exact Or.inl rfl
        · exact Or.inr rfl
        · omega
      · have hv : (Fin.natAdd (P1TopDownPaidPayload.tapes printer) (0 : Fin 2)).val=
            P1TopDownPaidPayload.tapes printer := by
          simp only [Fin.val_natAdd,Fin.val_zero,Nat.add_zero]
        simp only [PCJ38fbfed565f64139_Row.Frame.targetReserve,PCJ38fbfed565f64139_Row.Frame.bank,
          PCJeb9c0f0306e9481c_FramingSpec.paddedBank,Fin.addCases_right,hv,if_true]
        exact hdesc.symm
      · have hv : (Fin.natAdd (P1TopDownPaidPayload.tapes printer) (1 : Fin 2)).val≠
            P1TopDownPaidPayload.tapes printer := by
          simp only [Fin.val_natAdd]
          omega
        simp only [PCJ38fbfed565f64139_Row.Frame.targetReserve,PCJ38fbfed565f64139_Row.Frame.bank,
          PCJeb9c0f0306e9481c_FramingSpec.paddedBank,Fin.addCases_right,if_neg hv,ZeroPadding.pad_zero]
        exact hctr.symm
  · have hn : ∀ i,PCJ38fbfed565f64139_Ready.frameSlots printer t i≠x := fun i he=>hx ⟨i,he⟩
    change install (PCJ38fbfed565f64139_Ready.frameSlots printer t) b.frameA _ x=_
    rw [install_other _ _ _ _ hn,install_other (fieldSlot printer t) _ _ _ (fun k=>hn _)]

/-- The exit heads of `complete` are the ambient Frame heads whenever the ambient already
carries `Frame.heads out` on the Frame block. -/
theorem frameInH_eq {t : Nat} (p : PCJ38fbfed565f64139_Ready.Program printer t)
    (b : PCJ38fbfed565f64139_Row.Banks printer (PCJ38fbfed565f64139_Ready.tapes printer t))
    (out : List Bool)
    (hH : ∀ i,b.frameH (PCJ38fbfed565f64139_Ready.frameSlots printer t i)=
      PCJ38fbfed565f64139_Row.Frame.heads (P1TopDownPaidPayload.tapes printer) out i) :
    PCJ38fbfed565f64139_Row.frameInH printer (PCJ38fbfed565f64139_Ready.code p) b out=b.frameH :=
  dockH_existing _ _ _ hH

open PCJd4d1d9d7d1fa4313_Production in
/-- **C7 at the Core's own state.** For the RowState banks of row `j`, `complete` must end at the
next row's head bank and at the next row's bank with the thirteen framed fields installed. -/
theorem rowFrameIn_eq (work : Nat) (caps : RowCaps) (reserve : Fin 440 → Nat)
    (base : Nat → Fin (rowWork work) → List Bool) (drv lg : Fin (rowWork work))
    (completeFuel rowFuel : Nat) (p : PCJ38fbfed565f64139_Ready.Program printer (rowWork work))
    (facts : ∀ r∈F.rows,PCJ9eff70d512234a4c_Fixed.Packets.PacketFacts a F g r)
    (j : Fin F.rows.attach.length) (out : List Bool) (hcap : 1 ≤ caps.copyCap) :
    PCJ38fbfed565f64139_Row.frameInA printer (PCJ38fbfed565f64139_Ready.code p) a F g layout
        (PCJ38fbfed565f64139_Family.rowAt F j).val (PCJ38fbfed565f64139_Family.rowAt F j).property
        (facts (PCJ38fbfed565f64139_Family.rowAt F j).val (PCJ38fbfed565f64139_Family.rowAt F j).property)
        (PCJ38fbfed565f64139_Family.rowBanks printer a F g layout facts
          (PCJ45bee56da9f34d5a_RowState.rowState printer work a F g layout caps reserve base drv lg
            completeFuel rowFuel) j.val out) out=
      install (fieldSlot printer (rowWork work))
        (PCJ45bee56da9f34d5a_RowState.bank printer work a F g layout caps reserve base drv lg (j.val+1) out)
        (fun k=>ZeroPadding.pad caps.copyCap
          (frame (fieldWord (PCJ9eff70d512234a4c_Fixed.Packets.datum a F g layout
            (PCJ38fbfed565f64139_Family.rowAt F j).val (PCJ38fbfed565f64139_Family.rowAt F j).property
            (facts (PCJ38fbfed565f64139_Family.rowAt F j).val
              (PCJ38fbfed565f64139_Family.rowAt F j).property)) k))) ∧
    PCJ38fbfed565f64139_Row.frameInH printer (PCJ38fbfed565f64139_Ready.code p)
        (PCJ38fbfed565f64139_Family.rowBanks printer a F g layout facts
          (PCJ45bee56da9f34d5a_RowState.rowState printer work a F g layout caps reserve base drv lg
            completeFuel rowFuel) j.val out) out=
      PCJ45bee56da9f34d5a_RowState.headBank printer work a F g (j.val+1) out := by
  refine ⟨frameIn_eq printer a F g layout p _ _ _ _ out (fun _=>rfl) hcap ?_ ?_ ?_,
    frameInH_eq printer p _ out ?_⟩
  · intro i
    exact PCJ45bee56da9f34d5a_RowState.payload_entry printer work a F g layout caps reserve base drv lg
      (j.val+1) out i
  · exact PCJ45bee56da9f34d5a_RowState.descriptor_tapes printer work a F g layout caps reserve base drv lg
      (j.val+1) out
  · exact PCJ45bee56da9f34d5a_RowState.counter_entry printer work a F g layout caps reserve base drv lg
      (j.val+1) out
  · intro i
    change PCJ45bee56da9f34d5a_RowState.headBank printer work a F g (j.val+1) out _=_
    rw [PCJ45bee56da9f34d5a_RowState.headBank,PCJ45bee56da9f34d5a_RowState.portCases_frame]

/-- The thirteen field lengths are bounded by the copy capacity, from `RowCaps.Good`'s second
clause (as `Row.Ready`'s framing premise states it). -/
theorem field_fits (d : P1TopDownPaidReusable.Datum) (cap : Nat)
    (hcap : ∀ i,2*(PCJ38fbfed565f64139_Row.Frame.fields printer d i).length+1 ≤ cap) (k : Fin 13) :
    2*(fieldWord d k).length+1 ≤ cap := by
  have h := hcap (fieldPort printer k)
  rwa [PCJ38fbfed565f64139_Row.Frame.fields,datum_field] at h


end
end RowsRowLevel
