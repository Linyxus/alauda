import LeanTests.Test9.Debruijn

namespace Effect

inductive Eff : Sig -> Type where
| evar : BVar s .evar -> Eff s
| pure : Eff s
| exn : Eff s
| union : Eff s -> Eff s -> Eff s

def Eff.rename : Eff s1 -> Rename s1 s2 -> Eff s2
| .evar x0, f => .evar (f.var x0)
| .pure, _ => .pure
| .exn, _ => .exn
| .union a0 a1, f => .union (a0.rename f) (a1.rename f)

theorem Eff.rename_id {t : Eff s} :
    t.rename (Rename.id) = t := by
  induction t
  case evar => rfl
  case pure => rfl
  case exn => rfl
  case union =>
    simp_all [Eff.rename]

theorem Eff.rename_comp {t : Eff s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (t.rename f).rename g = t.rename (f.comp g) := by
  induction t generalizing s2 s3
  case evar => rfl
  case pure => rfl
  case exn => rfl
  case union =>
    simp_all [Eff.rename]

end Effect
