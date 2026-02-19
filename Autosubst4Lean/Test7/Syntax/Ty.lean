import Autosubst4Lean.Test7.Debruijn

namespace FExist

inductive Ty : Sig -> Type where
| tvar : BVar s .tvar -> Ty s
| arrow : Ty s -> Ty s -> Ty s
| forall_ : Ty (s,X) -> Ty s
| exists_ : Ty (s,X) -> Ty s
| prod : Ty s -> Ty s -> Ty s
| unit : Ty s

def Ty.rename : Ty s1 -> Rename s1 s2 -> Ty s2
| .tvar x0, f => .tvar (f.var x0)
| .arrow a0 a1, f => .arrow (a0.rename f) (a1.rename f)
| .forall_ a0, f => .forall_ (a0.rename f.lift)
| .exists_ a0, f => .exists_ (a0.rename f.lift)
| .prod a0 a1, f => .prod (a0.rename f) (a1.rename f)
| .unit, _ => .unit

theorem Ty.rename_id {t : Ty s} :
    t.rename (Rename.id) = t := by
  induction t
  case tvar => rfl
  case arrow =>
    simp_all [Ty.rename]
  case forall_ =>
    simp_all [Ty.rename, Rename.lift_id]
  case exists_ =>
    simp_all [Ty.rename, Rename.lift_id]
  case prod =>
    simp_all [Ty.rename]
  case unit => rfl

theorem Ty.rename_comp {t : Ty s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (t.rename f).rename g = t.rename (f.comp g) := by
  induction t generalizing s2 s3
  case tvar => rfl
  case arrow =>
    simp_all [Ty.rename]
  case forall_ =>
    simp_all [Ty.rename, Rename.lift_comp]
  case exists_ =>
    simp_all [Ty.rename, Rename.lift_comp]
  case prod =>
    simp_all [Ty.rename]
  case unit => rfl

end FExist
