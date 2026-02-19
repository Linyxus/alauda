import Autosubst4Lean.Test7.Debruijn
import Autosubst4Lean.Test7.Syntax.CTy

namespace RefCalc

inductive VTy : Sig -> Type where
| unit : VTy s
| arrow : VTy s -> CTy s -> VTy s
| prod : VTy s -> VTy s -> VTy s
| ref : BVar s .lvar -> VTy s -> VTy s
| forallL : VTy (s,l) -> VTy s

def VTy.rename : VTy s1 -> Rename s1 s2 -> VTy s2
| .unit, _ => .unit
| .arrow a0 a1, f => .arrow (a0.rename f) (a1.rename f)
| .prod a0 a1, f => .prod (a0.rename f) (a1.rename f)
| .ref x0 a1, f => .ref (f.var x0) (a1.rename f)
| .forallL a0, f => .forallL (a0.rename f.lift)

theorem VTy.rename_id {t : VTy s} :
    t.rename (Rename.id) = t := by
  induction t
  case unit => rfl
  case arrow =>
    simp_all [VTy.rename, CTy.rename_id]
  case prod =>
    simp_all [VTy.rename]
  case ref =>
    simp_all [VTy.rename]
  case forallL =>
    simp_all [VTy.rename, Rename.lift_id]

theorem VTy.rename_comp {t : VTy s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (t.rename f).rename g = t.rename (f.comp g) := by
  induction t generalizing s2 s3
  case unit => rfl
  case arrow =>
    simp_all [VTy.rename, CTy.rename_comp]
  case prod =>
    simp_all [VTy.rename]
  case ref =>
    simp_all [VTy.rename]
  case forallL =>
    simp_all [VTy.rename, Rename.lift_comp]

end RefCalc
