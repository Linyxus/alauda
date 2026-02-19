import Autosubst4Lean.Test4.Debruijn

namespace RegionCalc

inductive Ty : Sig -> Type where
| tvar : BVar s .tvar -> Ty s
| arrow : Ty s -> Ty s -> Ty s
| ref : BVar s .rvar -> Ty s -> Ty s
| forallTy : Ty (s,X) -> Ty s
| forallRgn : Ty (s,r) -> Ty s
| unit : Ty s

def Ty.rename : Ty s1 -> Rename s1 s2 -> Ty s2
| .tvar x0, f => .tvar (f.var x0)
| .arrow a0 a1, f => .arrow (a0.rename f) (a1.rename f)
| .ref x0 a1, f => .ref (f.var x0) (a1.rename f)
| .forallTy a0, f => .forallTy (a0.rename f.lift)
| .forallRgn a0, f => .forallRgn (a0.rename f.lift)
| .unit, _ => .unit

theorem Ty.rename_id {t : Ty s} :
    t.rename (Rename.id) = t := by
  induction t
  case tvar => rfl
  case arrow =>
    simp_all [Ty.rename]
  case ref =>
    simp_all [Ty.rename]
  case forallTy =>
    simp_all [Ty.rename, Rename.lift_id]
  case forallRgn =>
    simp_all [Ty.rename, Rename.lift_id]
  case unit => rfl

theorem Ty.rename_comp {t : Ty s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (t.rename f).rename g = t.rename (f.comp g) := by
  induction t generalizing s2 s3
  case tvar => rfl
  case arrow =>
    simp_all [Ty.rename]
  case ref =>
    simp_all [Ty.rename]
  case forallTy =>
    simp_all [Ty.rename, Rename.lift_comp]
  case forallRgn =>
    simp_all [Ty.rename, Rename.lift_comp]
  case unit => rfl

end RegionCalc
