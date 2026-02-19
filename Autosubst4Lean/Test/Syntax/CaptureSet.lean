import Autosubst4Lean.Test.Debruijn
import Autosubst4Lean.Test.Syntax.Var

namespace CC

inductive CaptureSet : Sig -> Type where
| empty : CaptureSet s
| union : CaptureSet s -> CaptureSet s -> CaptureSet s
| var : Var .var s -> CaptureSet s
| cvar : BVar s .cvar -> CaptureSet s

def CaptureSet.rename : CaptureSet s1 -> Rename s1 s2 -> CaptureSet s2
| .empty, _ => .empty
| .union a0 a1, f => .union (a0.rename f) (a1.rename f)
| .var x0, f => .var (x0.rename f)
| .cvar x0, f => .cvar (f.var x0)

theorem CaptureSet.rename_id {t : CaptureSet s} :
    t.rename (Rename.id) = t := by
  induction t
  case empty => rfl
  case union =>
    simp_all [CaptureSet.rename]
  case var =>
    simp_all [CaptureSet.rename, Var.rename_id]
  case cvar => rfl

theorem CaptureSet.rename_comp {t : CaptureSet s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (t.rename f).rename g = t.rename (f.comp g) := by
  induction t generalizing s2 s3
  case empty => rfl
  case union =>
    simp_all [CaptureSet.rename]
  case var =>
    simp_all [CaptureSet.rename, Var.rename_comp]
  case cvar => rfl

end CC
