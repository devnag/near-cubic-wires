import Proof.Packets.MaskFrameLoop
import Proof.Packets.PhysicalParityScan

set_option autoImplicit false
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskFrame
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource.ProjectionNormalization

theorem record_eq (bits : List Bool) :
    record bits=ClauseEquality.stream (PhysicalParityScan.supportRecord bits) := by
  simp [record,ClauseEquality.stream,PhysicalParityScan.supportRecord,RepairOrdinary.frame,List.append_assoc]

theorem records_stream (rows : List (List Bool)) :
    records rows=PhysicalParityScan.stream (rows.map PhysicalParityScan.supportRecord) := by
  induction rows with
  | nil => rfl
  | cons bits rows ih =>
    change record bits++records rows=_
    simp only [List.map_cons,PhysicalParityScan.stream_cons,←record_eq,←ih]

theorem records_append (left right : List (List Bool)) :
    records (left++right)=records left++records right := by
  simp [records,List.flatMap_append]

end PCJ9eff70d512234a4c_Fixed.Materializer.MaskFrame
