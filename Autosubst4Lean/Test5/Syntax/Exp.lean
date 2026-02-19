import Autosubst4Lean.Test5.Debruijn
import Autosubst4Lean.Test5.Syntax.Ty

namespace Modal

inductive Exp : Sig -> Type where
| var : BVar s .var -> Exp s
| mvar : BVar s .mvar -> Exp s
| abs : Ty s -> Exp (s,x) -> Exp s
| app : Exp s -> Exp s -> Exp s
| boxi : Exp (s,m) -> Exp s
| letbox : Exp s -> Exp (s,m) -> Exp s
| pair : Exp s -> Exp s -> Exp s
| fst : Exp s -> Exp s
| snd : Exp s -> Exp s

def Exp.rename : Exp s1 -> Rename s1 s2 -> Exp s2
| .var x0, f => .var (f.var x0)
| .mvar x0, f => .mvar (f.var x0)
| .abs a0 a1, f => .abs (a0.rename f) (a1.rename f.lift)
| .app a0 a1, f => .app (a0.rename f) (a1.rename f)
| .boxi a0, f => .boxi (a0.rename f.lift)
| .letbox a0 a1, f => .letbox (a0.rename f) (a1.rename f.lift)
| .pair a0 a1, f => .pair (a0.rename f) (a1.rename f)
| .fst a0, f => .fst (a0.rename f)
| .snd a0, f => .snd (a0.rename f)

theorem Exp.rename_id {t : Exp s} :
    t.rename (Rename.id) = t := by
  induction t
  case var => rfl
  case mvar => rfl
  case abs =>
    simp_all [Exp.rename, Ty.rename_id, Rename.lift_id]
  case app =>
    simp_all [Exp.rename]
  case boxi =>
    simp_all [Exp.rename, Rename.lift_id]
  case letbox =>
    simp_all [Exp.rename, Rename.lift_id]
  case pair =>
    simp_all [Exp.rename]
  case fst =>
    simp_all [Exp.rename]
  case snd =>
    simp_all [Exp.rename]

theorem Exp.rename_comp {t : Exp s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (t.rename f).rename g = t.rename (f.comp g) := by
  induction t generalizing s2 s3
  case var => rfl
  case mvar => rfl
  case abs =>
    simp_all [Exp.rename, Ty.rename_comp, Rename.lift_comp]
  case app =>
    simp_all [Exp.rename]
  case boxi =>
    simp_all [Exp.rename, Rename.lift_comp]
  case letbox =>
    simp_all [Exp.rename, Rename.lift_comp]
  case pair =>
    simp_all [Exp.rename]
  case fst =>
    simp_all [Exp.rename]
  case snd =>
    simp_all [Exp.rename]

end Modal
