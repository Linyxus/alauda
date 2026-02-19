import Autosubst4Lean.Test.Debruijn

namespace CC

inductive Var : Kind -> Sig -> Type where
| bound : BVar s k -> Var k s
| free : Nat -> Var k s

def Var.rename {k : Kind} : Var k s1 -> Rename s1 s2 -> Var k s2
| .bound x0, f => .bound (f.var x0)
| .free a0, _ => .free a0

theorem Var.rename_id {k : Kind} {t : Var k s} :
    t.rename (Rename.id) = t := by
  induction t
  case bound => rfl
  case free => rfl

theorem Var.rename_comp {k : Kind} {t : Var k s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (t.rename f).rename g = t.rename (f.comp g) := by
  induction t generalizing s2 s3
  case bound => rfl
  case free => rfl

end CC
