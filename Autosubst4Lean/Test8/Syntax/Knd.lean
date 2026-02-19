import Autosubst4Lean.Test8.Debruijn

namespace FOmega

inductive Knd : Sig -> Type where
| kvar : BVar s .kvar -> Knd s
| star : Knd s
| karrow : Knd s -> Knd s -> Knd s

def Knd.rename : Knd s1 -> Rename s1 s2 -> Knd s2
| .kvar x0, f => .kvar (f.var x0)
| .star, _ => .star
| .karrow a0 a1, f => .karrow (a0.rename f) (a1.rename f)

theorem Knd.rename_id {t : Knd s} :
    t.rename (Rename.id) = t := by
  induction t
  case kvar => rfl
  case star => rfl
  case karrow =>
    simp_all [Knd.rename]

theorem Knd.rename_comp {t : Knd s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (t.rename f).rename g = t.rename (f.comp g) := by
  induction t generalizing s2 s3
  case kvar => rfl
  case star => rfl
  case karrow =>
    simp_all [Knd.rename]

end FOmega
