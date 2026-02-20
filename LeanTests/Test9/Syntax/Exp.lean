import LeanTests.Test9.Debruijn
import LeanTests.Test9.Syntax.Eff
import LeanTests.Test9.Syntax.Ty

namespace Effect

inductive Exp : Sig -> Type where
| var : BVar s .var -> Exp s
| abs : Ty s -> Exp (s,x) -> Exp s
| app : Exp s -> Exp s -> Exp s
| tabs : Exp (s,X) -> Exp s
| tapp : Exp s -> Ty s -> Exp s
| eabs : Exp (s,e) -> Exp s
| eapp : Exp s -> Eff s -> Exp s
| pair : Exp s -> Exp s -> Exp s
| fst : Exp s -> Exp s
| snd : Exp s -> Exp s
| throw : Exp s -> Exp s
| trycatch : Exp s -> Exp (s,x) -> Exp s
| letin : Exp s -> Exp (s,x) -> Exp s
| unit : Exp s

def Exp.rename : Exp s1 -> Rename s1 s2 -> Exp s2
| .var x0, f => .var (f.var x0)
| .abs a0 a1, f => .abs (a0.rename f) (a1.rename f.lift)
| .app a0 a1, f => .app (a0.rename f) (a1.rename f)
| .tabs a0, f => .tabs (a0.rename f.lift)
| .tapp a0 a1, f => .tapp (a0.rename f) (a1.rename f)
| .eabs a0, f => .eabs (a0.rename f.lift)
| .eapp a0 a1, f => .eapp (a0.rename f) (a1.rename f)
| .pair a0 a1, f => .pair (a0.rename f) (a1.rename f)
| .fst a0, f => .fst (a0.rename f)
| .snd a0, f => .snd (a0.rename f)
| .throw a0, f => .throw (a0.rename f)
| .trycatch a0 a1, f => .trycatch (a0.rename f) (a1.rename f.lift)
| .letin a0 a1, f => .letin (a0.rename f) (a1.rename f.lift)
| .unit, _ => .unit

theorem Exp.rename_id {t : Exp s} :
    t.rename (Rename.id) = t := by
  induction t
  case var => rfl
  case abs =>
    simp_all [Exp.rename, Ty.rename_id, Rename.lift_id]
  case app =>
    simp_all [Exp.rename]
  case tabs =>
    simp_all [Exp.rename, Rename.lift_id]
  case tapp =>
    simp_all [Exp.rename, Ty.rename_id]
  case eabs =>
    simp_all [Exp.rename, Rename.lift_id]
  case eapp =>
    simp_all [Exp.rename, Eff.rename_id]
  case pair =>
    simp_all [Exp.rename]
  case fst =>
    simp_all [Exp.rename]
  case snd =>
    simp_all [Exp.rename]
  case throw =>
    simp_all [Exp.rename]
  case trycatch =>
    simp_all [Exp.rename, Rename.lift_id]
  case letin =>
    simp_all [Exp.rename, Rename.lift_id]
  case unit => rfl

theorem Exp.rename_comp {t : Exp s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (t.rename f).rename g = t.rename (f.comp g) := by
  induction t generalizing s2 s3
  case var => rfl
  case abs =>
    simp_all [Exp.rename, Ty.rename_comp, Rename.lift_comp]
  case app =>
    simp_all [Exp.rename]
  case tabs =>
    simp_all [Exp.rename, Rename.lift_comp]
  case tapp =>
    simp_all [Exp.rename, Ty.rename_comp]
  case eabs =>
    simp_all [Exp.rename, Rename.lift_comp]
  case eapp =>
    simp_all [Exp.rename, Eff.rename_comp]
  case pair =>
    simp_all [Exp.rename]
  case fst =>
    simp_all [Exp.rename]
  case snd =>
    simp_all [Exp.rename]
  case throw =>
    simp_all [Exp.rename]
  case trycatch =>
    simp_all [Exp.rename, Rename.lift_comp]
  case letin =>
    simp_all [Exp.rename, Rename.lift_comp]
  case unit => rfl

end Effect
