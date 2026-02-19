import Autosubst4Lean.Test6.Debruijn

namespace MiniML

inductive Ty : Sig -> Type where
| base : Ty s
| arrow : Ty s -> Ty s -> Ty s
| prod : Ty s -> Ty s -> Ty s
| sum : Ty s -> Ty s -> Ty s
| list : Ty s -> Ty s
| unit : Ty s

def Ty.rename : Ty s1 -> Rename s1 s2 -> Ty s2
| .base, _ => .base
| .arrow a0 a1, f => .arrow (a0.rename f) (a1.rename f)
| .prod a0 a1, f => .prod (a0.rename f) (a1.rename f)
| .sum a0 a1, f => .sum (a0.rename f) (a1.rename f)
| .list a0, f => .list (a0.rename f)
| .unit, _ => .unit

theorem Ty.rename_id {t : Ty s} :
    t.rename (Rename.id) = t := by
  induction t
  case base => rfl
  case arrow =>
    simp_all [Ty.rename]
  case prod =>
    simp_all [Ty.rename]
  case sum =>
    simp_all [Ty.rename]
  case list =>
    simp_all [Ty.rename]
  case unit => rfl

theorem Ty.rename_comp {t : Ty s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (t.rename f).rename g = t.rename (f.comp g) := by
  induction t generalizing s2 s3
  case base => rfl
  case arrow =>
    simp_all [Ty.rename]
  case prod =>
    simp_all [Ty.rename]
  case sum =>
    simp_all [Ty.rename]
  case list =>
    simp_all [Ty.rename]
  case unit => rfl

end MiniML
