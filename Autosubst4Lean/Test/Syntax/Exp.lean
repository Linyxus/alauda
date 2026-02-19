import Autosubst4Lean.Test.Debruijn
import Autosubst4Lean.Test.Syntax.Var
import Autosubst4Lean.Test.Syntax.CaptureSet
import Autosubst4Lean.Test.Syntax.CaptureBound
import Autosubst4Lean.Test.Syntax.Ty

namespace CC

inductive Exp : Sig -> Type where
| var : Var .var s -> Exp s
| abs : CaptureSet s -> Ty .capt s -> Exp (s,x) -> Exp s
| tabs : CaptureSet s -> Ty .shape s -> Exp (s,X) -> Exp s
| cabs : CaptureSet s -> CaptureBound s -> Exp (s,C) -> Exp s
| pack : CaptureSet s -> Var .var s -> Exp s
| app : Var .var s -> Var .var s -> Exp s
| tapp : Var .var s -> Ty .shape s -> Exp s
| capp : Var .var s -> CaptureSet s -> Exp s
| letin : Exp s -> Exp (s,x) -> Exp s
| unpack : Exp s -> Exp ((s,C),x) -> Exp s
| unit : Exp s
| btrue : Exp s
| bfalse : Exp s
| read : Var .var s -> Exp s
| write : Var .var s -> Var .var s -> Exp s
| cond : Var .var s -> Exp s -> Exp s -> Exp s

def Exp.rename : Exp s1 -> Rename s1 s2 -> Exp s2
| .var x0, f => .var (x0.rename f)
| .abs a0 a1 a2, f => .abs (a0.rename f) (a1.rename f) (a2.rename f.lift)
| .tabs a0 a1 a2, f => .tabs (a0.rename f) (a1.rename f) (a2.rename f.lift)
| .cabs a0 a1 a2, f => .cabs (a0.rename f) (a1.rename f) (a2.rename f.lift)
| .pack a0 x1, f => .pack (a0.rename f) (x1.rename f)
| .app x0 x1, f => .app (x0.rename f) (x1.rename f)
| .tapp x0 a1, f => .tapp (x0.rename f) (a1.rename f)
| .capp x0 a1, f => .capp (x0.rename f) (a1.rename f)
| .letin a0 a1, f => .letin (a0.rename f) (a1.rename f.lift)
| .unpack a0 a1, f => .unpack (a0.rename f) (a1.rename f.lift.lift)
| .unit, _ => .unit
| .btrue, _ => .btrue
| .bfalse, _ => .bfalse
| .read x0, f => .read (x0.rename f)
| .write x0 x1, f => .write (x0.rename f) (x1.rename f)
| .cond x0 a1 a2, f => .cond (x0.rename f) (a1.rename f) (a2.rename f)

theorem Exp.rename_id {t : Exp s} :
    t.rename (Rename.id) = t := by
  induction t
  case var =>
    simp_all [Exp.rename, Var.rename_id]
  case abs =>
    simp_all [Exp.rename, CaptureSet.rename_id, Ty.rename_id, Rename.lift_id]
  case tabs =>
    simp_all [Exp.rename, CaptureSet.rename_id, Ty.rename_id, Rename.lift_id]
  case cabs =>
    simp_all [Exp.rename, CaptureSet.rename_id, CaptureBound.rename_id, Rename.lift_id]
  case pack =>
    simp_all [Exp.rename, CaptureSet.rename_id, Var.rename_id]
  case app =>
    simp_all [Exp.rename, Var.rename_id]
  case tapp =>
    simp_all [Exp.rename, Var.rename_id, Ty.rename_id]
  case capp =>
    simp_all [Exp.rename, Var.rename_id, CaptureSet.rename_id]
  case letin =>
    simp_all [Exp.rename, Rename.lift_id]
  case unpack =>
    simp_all [Exp.rename, Rename.lift_id]
  case unit => rfl
  case btrue => rfl
  case bfalse => rfl
  case read =>
    simp_all [Exp.rename, Var.rename_id]
  case write =>
    simp_all [Exp.rename, Var.rename_id]
  case cond =>
    simp_all [Exp.rename, Var.rename_id]

theorem Exp.rename_comp {t : Exp s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (t.rename f).rename g = t.rename (f.comp g) := by
  induction t generalizing s2 s3
  case var =>
    simp_all [Exp.rename, Var.rename_comp]
  case abs =>
    simp_all [Exp.rename, CaptureSet.rename_comp, Ty.rename_comp, Rename.lift_comp]
  case tabs =>
    simp_all [Exp.rename, CaptureSet.rename_comp, Ty.rename_comp, Rename.lift_comp]
  case cabs =>
    simp_all [Exp.rename, CaptureSet.rename_comp, CaptureBound.rename_comp, Rename.lift_comp]
  case pack =>
    simp_all [Exp.rename, CaptureSet.rename_comp, Var.rename_comp]
  case app =>
    simp_all [Exp.rename, Var.rename_comp]
  case tapp =>
    simp_all [Exp.rename, Var.rename_comp, Ty.rename_comp]
  case capp =>
    simp_all [Exp.rename, Var.rename_comp, CaptureSet.rename_comp]
  case letin =>
    simp_all [Exp.rename, Rename.lift_comp]
  case unpack =>
    simp_all [Exp.rename, Rename.lift_comp]
  case unit => rfl
  case btrue => rfl
  case bfalse => rfl
  case read =>
    simp_all [Exp.rename, Var.rename_comp]
  case write =>
    simp_all [Exp.rename, Var.rename_comp]
  case cond =>
    simp_all [Exp.rename, Var.rename_comp]

end CC
