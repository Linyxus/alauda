import LeanTests.Test9.Debruijn
import LeanTests.Test9.Syntax.Eff

namespace Effect

inductive Ty : Sig -> Type where
| tvar : BVar s .tvar -> Ty s
| arrow : Ty s -> Eff s -> Ty s -> Ty s
| forall_ : Ty (s,X) -> Ty s
| eforall : Ty (s,e) -> Ty s
| prod : Ty s -> Ty s -> Ty s
| unit : Ty s

def Ty.rename : Ty s1 -> Rename s1 s2 -> Ty s2
| .tvar x0, f => .tvar (f.var x0)
| .arrow a0 a1 a2, f => .arrow (a0.rename f) (a1.rename f) (a2.rename f)
| .forall_ a0, f => .forall_ (a0.rename f.lift)
| .eforall a0, f => .eforall (a0.rename f.lift)
| .prod a0 a1, f => .prod (a0.rename f) (a1.rename f)
| .unit, _ => .unit

theorem Ty.rename_id {t : Ty s} :
    t.rename (Rename.id) = t := by
  induction t
  case tvar => rfl
  case arrow =>
    simp_all [Ty.rename, Eff.rename_id]
  case forall_ =>
    simp_all [Ty.rename, Rename.lift_id]
  case eforall =>
    simp_all [Ty.rename, Rename.lift_id]
  case prod =>
    simp_all [Ty.rename]
  case unit => rfl

theorem Ty.rename_comp {t : Ty s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (t.rename f).rename g = t.rename (f.comp g) := by
  induction t generalizing s2 s3
  case tvar => rfl
  case arrow =>
    simp_all [Ty.rename, Eff.rename_comp]
  case forall_ =>
    simp_all [Ty.rename, Rename.lift_comp]
  case eforall =>
    simp_all [Ty.rename, Rename.lift_comp]
  case prod =>
    simp_all [Ty.rename]
  case unit => rfl

end Effect
