import Proof.Packets.MaskProductOuter
import Proof.Packets.PhysicalParityScan

/-! Exact byte-format bridge from the Cartesian producer to the normalizer's
existing framed three-field records. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskProduct
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource.ProjectionNormalization

def unions (left right : List (List Bool)) :=
  left.flatMap (fun mask=>right.map (fun bits=>values (mask.zip bits)))

theorem record_eq (mask bits : List Bool) :
    record mask bits=ClauseEquality.stream (PhysicalParityScan.supportRecord (values (mask.zip bits))) := by
  simp [record,ClauseEquality.stream,PhysicalParityScan.supportRecord,RepairOrdinary.frame,List.append_assoc]

theorem records_stream (mask : List Bool) (right : List (List Bool)) :
    records mask right=PhysicalParityScan.stream
      ((right.map (fun bits=>values (mask.zip bits))).map PhysicalParityScan.supportRecord) := by
  induction right with
  | nil => rfl
  | cons bits right ih =>
    change record mask bits++records mask right=_
    simp only [List.map_cons,PhysicalParityScan.stream_cons,←record_eq,←ih]

theorem stream_append (left right : List PhysicalParityScan.Clause) :
    PhysicalParityScan.stream (left++right)=PhysicalParityScan.stream left++PhysicalParityScan.stream right := by
  induction left with
  | nil => rfl
  | cons row left ih => simp only [List.cons_append,PhysicalParityScan.stream_cons,ih,List.append_assoc]

theorem products_stream (left right : List (List Bool)) :
    products left right=PhysicalParityScan.stream ((unions left right).map PhysicalParityScan.supportRecord) := by
  induction left with
  | nil => rfl
  | cons mask left ih =>
    change records mask right++products left right=_
    simp only [unions,List.flatMap_cons,List.map_append,stream_append,←records_stream]
    rw [ih]
    rfl

theorem unions_length (left right : List (List Bool)) :
    (unions left right).length=left.length*right.length := by
  induction left with
  | nil => simp [unions]
  | cons mask left ih =>
    change ((right.map (fun bits=>values (mask.zip bits)))++unions left right).length=_
    rw [List.length_append,List.length_map,ih,List.length_cons]
    ring

theorem support_union {B : Nat} (left right : Finset (Fin B)) :
    values ((PhysicalSupportUnion.supportMask left).zip (PhysicalSupportUnion.supportMask right))=
      PhysicalSupportUnion.supportMask (left∪right) := by
  let pairs:=List.ofFn (fun i : Fin B=>(decide (i∈left),decide (i∈right)))
  have hl : pairs.map Prod.fst=PhysicalSupportUnion.supportMask left := by
    simp only [pairs,PhysicalSupportUnion.supportMask,List.map_ofFn]
    rfl
  have hr : pairs.map Prod.snd=PhysicalSupportUnion.supportMask right := by
    simp only [pairs,PhysicalSupportUnion.supportMask,List.map_ofFn]
    rfl
  rw [←List.zip_of_prod hl hr]
  simp only [values,PhysicalSupportUnion.values,pairs,PhysicalSupportUnion.supportMask,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  by_cases hl : i∈left <;> by_cases hr : i∈right <;> simp [hl,hr]

end PCJ9eff70d512234a4c_Fixed.Materializer.MaskProduct
