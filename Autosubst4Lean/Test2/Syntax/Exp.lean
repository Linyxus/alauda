import Autosubst4Lean.Test2.Debruijn
import Autosubst4Lean.Test2.Syntax.Ty

namespace Fsub

inductive Exp : Sig -> Type where
| var : BVar s .var -> Exp s
| abs : Ty s -> Exp (s,x) -> Exp s
| app : Exp s -> Exp s -> Exp s
| tabs : Ty s -> Exp (s,X) -> Exp s
| tapp : Exp s -> Ty s -> Exp s

def Exp.rename : Exp s1 -> Rename s1 s2 -> Exp s2
| .var x0, f => .var (f.var x0)
| .abs a0 a1, f => .abs (a0.rename f) (a1.rename f.lift)
| .app a0 a1, f => .app (a0.rename f) (a1.rename f)
| .tabs a0 a1, f => .tabs (a0.rename f) (a1.rename f.lift)
| .tapp a0 a1, f => .tapp (a0.rename f) (a1.rename f)

theorem Exp.rename_id {t : Exp s} :
    t.rename (Rename.id) = t := by
  induction t
  case var => rfl
  case abs =>
    simp_all [Exp.rename, Ty.rename_id, Rename.lift_id]
  case app =>
    simp_all [Exp.rename]
  case tabs =>
    simp_all [Exp.rename, Ty.rename_id, Rename.lift_id]
  case tapp =>
    simp_all [Exp.rename, Ty.rename_id]

theorem Exp.rename_comp {t : Exp s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (t.rename f).rename g = t.rename (f.comp g) := by
  induction t generalizing s2 s3
  case var => rfl
  case abs =>
    simp_all [Exp.rename, Ty.rename_comp, Rename.lift_comp]
  case app =>
    simp_all [Exp.rename]
  case tabs =>
    simp_all [Exp.rename, Ty.rename_comp, Rename.lift_comp]
  case tapp =>
    simp_all [Exp.rename, Ty.rename_comp]

end Fsub
