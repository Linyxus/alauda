import Autosubst4Lean.Test7.Debruijn
import Autosubst4Lean.Test7.Syntax.VTy
import Autosubst4Lean.Test7.Syntax.Comp

namespace RefCalc

inductive Val : Sig -> Type where
| var : BVar s .var -> Val s
| unit : Val s
| pair : Val s -> Val s -> Val s
| abs : VTy s -> Comp (s,x) -> Val s
| labs : Comp (s,l) -> Val s

def Val.rename : Val s1 -> Rename s1 s2 -> Val s2
| .var x0, f => .var (f.var x0)
| .unit, _ => .unit
| .pair a0 a1, f => .pair (a0.rename f) (a1.rename f)
| .abs a0 a1, f => .abs (a0.rename f) (a1.rename f.lift)
| .labs a0, f => .labs (a0.rename f.lift)

theorem Val.rename_id {t : Val s} :
    t.rename (Rename.id) = t := by
  induction t
  case var => rfl
  case unit => rfl
  case pair =>
    simp_all [Val.rename]
  case abs =>
    simp_all [Val.rename, VTy.rename_id, Comp.rename_id, Rename.lift_id]
  case labs =>
    simp_all [Val.rename, Comp.rename_id, Rename.lift_id]

theorem Val.rename_comp {t : Val s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (t.rename f).rename g = t.rename (f.comp g) := by
  induction t generalizing s2 s3
  case var => rfl
  case unit => rfl
  case pair =>
    simp_all [Val.rename]
  case abs =>
    simp_all [Val.rename, VTy.rename_comp, Comp.rename_comp, Rename.lift_comp]
  case labs =>
    simp_all [Val.rename, Comp.rename_comp, Rename.lift_comp]

end RefCalc
