import Autosubst4Lean.Test7.Debruijn
import Autosubst4Lean.Test7.Syntax.Ty

namespace FExist

inductive Exp : Sig -> Type where
| var : BVar s .var -> Exp s
| abs : Ty s -> Exp (s,x) -> Exp s
| app : Exp s -> Exp s -> Exp s
| tabs : Exp (s,X) -> Exp s
| tapp : Exp s -> Ty s -> Exp s
| pack : Ty s -> Exp s -> Ty (s,X) -> Exp s
| unpack : Exp s -> Exp ((s,X),x) -> Exp s
| pair : Exp s -> Exp s -> Exp s
| fst : Exp s -> Exp s
| snd : Exp s -> Exp s
| unit : Exp s

def Exp.rename : Exp s1 -> Rename s1 s2 -> Exp s2
| .var x0, f => .var (f.var x0)
| .abs a0 a1, f => .abs (a0.rename f) (a1.rename f.lift)
| .app a0 a1, f => .app (a0.rename f) (a1.rename f)
| .tabs a0, f => .tabs (a0.rename f.lift)
| .tapp a0 a1, f => .tapp (a0.rename f) (a1.rename f)
| .pack a0 a1 a2, f => .pack (a0.rename f) (a1.rename f) (a2.rename f.lift)
| .unpack a0 a1, f => .unpack (a0.rename f) (a1.rename f.lift.lift)
| .pair a0 a1, f => .pair (a0.rename f) (a1.rename f)
| .fst a0, f => .fst (a0.rename f)
| .snd a0, f => .snd (a0.rename f)
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
  case pack =>
    simp_all [Exp.rename, Ty.rename_id, Rename.lift_id]
  case unpack =>
    simp_all [Exp.rename, Rename.lift_id]
  case pair =>
    simp_all [Exp.rename]
  case fst =>
    simp_all [Exp.rename]
  case snd =>
    simp_all [Exp.rename]
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
  case pack =>
    simp_all [Exp.rename, Ty.rename_comp, Rename.lift_comp]
  case unpack =>
    simp_all [Exp.rename, Rename.lift_comp]
  case pair =>
    simp_all [Exp.rename]
  case fst =>
    simp_all [Exp.rename]
  case snd =>
    simp_all [Exp.rename]
  case unit => rfl

end FExist
