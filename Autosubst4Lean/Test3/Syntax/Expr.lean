import Autosubst4Lean.Test3.Debruijn

namespace CoC

inductive Expr : Sig -> Type where
| var : BVar s .var -> Expr s
| sort : Nat -> Expr s
| pi : Expr s -> Expr (s,x) -> Expr s
| lam : Expr s -> Expr (s,x) -> Expr s
| app : Expr s -> Expr s -> Expr s

def Expr.rename : Expr s1 -> Rename s1 s2 -> Expr s2
| .var x0, f => .var (f.var x0)
| .sort a0, _ => .sort a0
| .pi a0 a1, f => .pi (a0.rename f) (a1.rename f.lift)
| .lam a0 a1, f => .lam (a0.rename f) (a1.rename f.lift)
| .app a0 a1, f => .app (a0.rename f) (a1.rename f)

theorem Expr.rename_id {t : Expr s} :
    t.rename (Rename.id) = t := by
  induction t
  case var => rfl
  case sort => rfl
  case pi =>
    simp_all [Expr.rename, Rename.lift_id]
  case lam =>
    simp_all [Expr.rename, Rename.lift_id]
  case app =>
    simp_all [Expr.rename]

theorem Expr.rename_comp {t : Expr s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (t.rename f).rename g = t.rename (f.comp g) := by
  induction t generalizing s2 s3
  case var => rfl
  case sort => rfl
  case pi =>
    simp_all [Expr.rename, Rename.lift_comp]
  case lam =>
    simp_all [Expr.rename, Rename.lift_comp]
  case app =>
    simp_all [Expr.rename]

end CoC
