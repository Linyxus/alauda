import Autosubst4Lean.Test.Debruijn
import Autosubst4Lean.Test.Syntax.CaptureSet

namespace CC

inductive CaptureBound : Sig -> Type where
| unbound : CaptureBound s
| bound : CaptureSet s -> CaptureBound s

def CaptureBound.rename : CaptureBound s1 -> Rename s1 s2 -> CaptureBound s2
| .unbound, _ => .unbound
| .bound a0, f => .bound (a0.rename f)

theorem CaptureBound.rename_id {t : CaptureBound s} :
    t.rename (Rename.id) = t := by
  induction t
  case unbound => rfl
  case bound =>
    simp_all [CaptureBound.rename, CaptureSet.rename_id]

theorem CaptureBound.rename_comp {t : CaptureBound s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (t.rename f).rename g = t.rename (f.comp g) := by
  induction t generalizing s2 s3
  case unbound => rfl
  case bound =>
    simp_all [CaptureBound.rename, CaptureSet.rename_comp]

end CC
