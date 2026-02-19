import Autosubst4Lean.Test7.Debruijn

namespace RefCalc

inductive CTy : Sig -> Type where
| ret : VTy s -> CTy s
| bind : CTy s -> CTy (s,x) -> CTy s

def CTy.rename : CTy s1 -> Rename s1 s2 -> CTy s2
| .ret a0, f => .ret (a0.rename f)
| .bind a0 a1, f => .bind (a0.rename f) (a1.rename f.lift)

theorem CTy.rename_id {t : CTy s} :
    t.rename (Rename.id) = t := by
  induction t
  case ret =>
    simp_all [CTy.rename, VTy.rename_id]
  case bind =>
    simp_all [CTy.rename, Rename.lift_id]

theorem CTy.rename_comp {t : CTy s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (t.rename f).rename g = t.rename (f.comp g) := by
  induction t generalizing s2 s3
  case ret =>
    simp_all [CTy.rename, VTy.rename_comp]
  case bind =>
    simp_all [CTy.rename, Rename.lift_comp]

end RefCalc
