import Autosubst4Lean.Test2.Debruijn

namespace Fsub

inductive Ty : Sig -> Type where
| top : Ty s
| tvar : BVar s .tvar -> Ty s
| arrow : Ty s -> Ty s -> Ty s
| forall_ : Ty s -> Ty (s,X) -> Ty s

def Ty.rename : Ty s1 -> Rename s1 s2 -> Ty s2
| .top, _ => .top
| .tvar x0, f => .tvar (f.var x0)
| .arrow a0 a1, f => .arrow (a0.rename f) (a1.rename f)
| .forall_ a0 a1, f => .forall_ (a0.rename f) (a1.rename f.lift)

theorem Ty.rename_id {t : Ty s} :
    t.rename (Rename.id) = t := by
  induction t
  case top => rfl
  case tvar => rfl
  case arrow =>
    simp_all [Ty.rename]
  case forall_ =>
    simp_all [Ty.rename, Rename.lift_id]

theorem Ty.rename_comp {t : Ty s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (t.rename f).rename g = t.rename (f.comp g) := by
  induction t generalizing s2 s3
  case top => rfl
  case tvar => rfl
  case arrow =>
    simp_all [Ty.rename]
  case forall_ =>
    simp_all [Ty.rename, Rename.lift_comp]

end Fsub
