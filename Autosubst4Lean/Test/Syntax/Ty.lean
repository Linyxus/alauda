import Autosubst4Lean.Test.Debruijn
import Autosubst4Lean.Test.Syntax.CaptureSet
import Autosubst4Lean.Test.Syntax.CaptureBound

namespace CC

inductive Ty : TySort -> Sig -> Type where
| top : Ty .shape s
| tvar : BVar s .tvar -> Ty .shape s
| arrow : Ty .capt s -> Ty .exi (s,x) -> Ty .shape s
| poly : Ty .shape s -> Ty .exi (s,X) -> Ty .shape s
| cpoly : CaptureBound s -> Ty .exi (s,C) -> Ty .shape s
| unit : Ty .shape s
| cap : Ty .shape s
| bool : Ty .shape s
| cell : Ty .shape s
| capt : CaptureSet s -> Ty .shape s -> Ty .capt s
| exi : Ty .capt (s,C) -> Ty .exi s
| typ : Ty .capt s -> Ty .exi s

def Ty.rename {tySort : TySort} : Ty tySort s1 -> Rename s1 s2 -> Ty tySort s2
| .top, _ => .top
| .tvar x0, f => .tvar (f.var x0)
| .arrow a0 a1, f => .arrow (a0.rename f) (a1.rename f.lift)
| .poly a0 a1, f => .poly (a0.rename f) (a1.rename f.lift)
| .cpoly a0 a1, f => .cpoly (a0.rename f) (a1.rename f.lift)
| .unit, _ => .unit
| .cap, _ => .cap
| .bool, _ => .bool
| .cell, _ => .cell
| .capt a0 a1, f => .capt (a0.rename f) (a1.rename f)
| .exi a0, f => .exi (a0.rename f.lift)
| .typ a0, f => .typ (a0.rename f)

theorem Ty.rename_id {tySort : TySort} {t : Ty tySort s} :
    t.rename (Rename.id) = t := by
  induction t
  case top => rfl
  case tvar => rfl
  case arrow =>
    simp_all [Ty.rename, Rename.lift_id]
  case poly =>
    simp_all [Ty.rename, Rename.lift_id]
  case cpoly =>
    simp_all [Ty.rename, CaptureBound.rename_id, Rename.lift_id]
  case unit => rfl
  case cap => rfl
  case bool => rfl
  case cell => rfl
  case capt =>
    simp_all [Ty.rename, CaptureSet.rename_id]
  case exi =>
    simp_all [Ty.rename, Rename.lift_id]
  case typ =>
    simp_all [Ty.rename]

theorem Ty.rename_comp {tySort : TySort} {t : Ty tySort s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (t.rename f).rename g = t.rename (f.comp g) := by
  induction t generalizing s2 s3
  case top => rfl
  case tvar => rfl
  case arrow =>
    simp_all [Ty.rename, Rename.lift_comp]
  case poly =>
    simp_all [Ty.rename, Rename.lift_comp]
  case cpoly =>
    simp_all [Ty.rename, CaptureBound.rename_comp, Rename.lift_comp]
  case unit => rfl
  case cap => rfl
  case bool => rfl
  case cell => rfl
  case capt =>
    simp_all [Ty.rename, CaptureSet.rename_comp]
  case exi =>
    simp_all [Ty.rename, Rename.lift_comp]
  case typ =>
    simp_all [Ty.rename]

end CC
