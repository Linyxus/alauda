import Autosubst4Lean.Test4.Debruijn
import Autosubst4Lean.Test4.Syntax.Ty

namespace RegionCalc

inductive Exp : Sig -> Type where
| var : BVar s .var -> Exp s
| abs : Ty s -> Exp (s,x) -> Exp s
| app : Exp s -> Exp s -> Exp s
| tabs : Exp (s,X) -> Exp s
| tapp : Exp s -> Ty s -> Exp s
| rabs : Exp (s,r) -> Exp s
| rapp : Exp s -> BVar s .rvar -> Exp s
| new : BVar s .rvar -> Exp s -> Exp s
| deref : Exp s -> Exp s
| assign : Exp s -> Exp s -> Exp s
| letrgn : Exp (s,r) -> Exp s
| unit : Exp s

def Exp.rename : Exp s1 -> Rename s1 s2 -> Exp s2
| .var x0, f => .var (f.var x0)
| .abs a0 a1, f => .abs (a0.rename f) (a1.rename f.lift)
| .app a0 a1, f => .app (a0.rename f) (a1.rename f)
| .tabs a0, f => .tabs (a0.rename f.lift)
| .tapp a0 a1, f => .tapp (a0.rename f) (a1.rename f)
| .rabs a0, f => .rabs (a0.rename f.lift)
| .rapp a0 x1, f => .rapp (a0.rename f) (f.var x1)
| .new x0 a1, f => .new (f.var x0) (a1.rename f)
| .deref a0, f => .deref (a0.rename f)
| .assign a0 a1, f => .assign (a0.rename f) (a1.rename f)
| .letrgn a0, f => .letrgn (a0.rename f.lift)
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
  case rabs =>
    simp_all [Exp.rename, Rename.lift_id]
  case rapp =>
    simp_all [Exp.rename]
  case new =>
    simp_all [Exp.rename]
  case deref =>
    simp_all [Exp.rename]
  case assign =>
    simp_all [Exp.rename]
  case letrgn =>
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
  case rabs =>
    simp_all [Exp.rename, Rename.lift_comp]
  case rapp =>
    simp_all [Exp.rename]
  case new =>
    simp_all [Exp.rename]
  case deref =>
    simp_all [Exp.rename]
  case assign =>
    simp_all [Exp.rename]
  case letrgn =>
    simp_all [Exp.rename, Rename.lift_comp]
  case unit => rfl

end RegionCalc
