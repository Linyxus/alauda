import Autosubst4Lean.Test8.Debruijn

namespace FOmega

inductive Kind : Sig -> Type where
| kvar : BVar s .kvar -> Kind s
| star : Kind s
| karrow : Kind s -> Kind s -> Kind s

def Kind.rename : Kind s1 -> Rename s1 s2 -> Kind s2
| .kvar x0, f => .kvar (f.var x0)
| .star, _ => .star
| .karrow a0 a1, f => .karrow (a0.rename f) (a1.rename f)

theorem Kind.rename_id {t : Kind s} :
    t.rename (Rename.id) = t := by
  induction t
  case kvar => rfl
  case star => rfl
  case karrow =>
    simp_all [Kind.rename]

theorem Kind.rename_comp {t : Kind s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (t.rename f).rename g = t.rename (f.comp g) := by
  induction t generalizing s2 s3
  case kvar => rfl
  case star => rfl
  case karrow =>
    simp_all [Kind.rename]

end FOmega
