import Autosubst4Lean.Test5.Debruijn

namespace Modal

inductive Ty : Sig -> Type where
| base : Ty s
| arrow : Ty s -> Ty s -> Ty s
| box : Ty s -> Ty s
| prod : Ty s -> Ty s -> Ty s

def Ty.rename : Ty s1 -> Rename s1 s2 -> Ty s2
| .base, _ => .base
| .arrow a0 a1, f => .arrow (a0.rename f) (a1.rename f)
| .box a0, f => .box (a0.rename f)
| .prod a0 a1, f => .prod (a0.rename f) (a1.rename f)

theorem Ty.rename_id {t : Ty s} :
    t.rename (Rename.id) = t := by
  induction t
  case base => rfl
  case arrow =>
    simp_all [Ty.rename]
  case box =>
    simp_all [Ty.rename]
  case prod =>
    simp_all [Ty.rename]

theorem Ty.rename_comp {t : Ty s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (t.rename f).rename g = t.rename (f.comp g) := by
  induction t generalizing s2 s3
  case base => rfl
  case arrow =>
    simp_all [Ty.rename]
  case box =>
    simp_all [Ty.rename]
  case prod =>
    simp_all [Ty.rename]

end Modal
