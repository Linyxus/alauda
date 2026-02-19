import Autosubst4Lean.Test6.Debruijn
import Autosubst4Lean.Test6.Syntax.Ty

namespace MiniML

inductive Exp : Sig -> Type where
| var : BVar s .var -> Exp s
| abs : Ty s -> Exp (s,x) -> Exp s
| app : Exp s -> Exp s -> Exp s
| let_ : Exp s -> Exp (s,x) -> Exp s
| letrec : Ty s -> Exp (s,x) -> Exp (s,x) -> Exp s
| pair : Exp s -> Exp s -> Exp s
| fst : Exp s -> Exp s
| snd : Exp s -> Exp s
| inl : Exp s -> Exp s
| inr : Exp s -> Exp s
| case_ : Exp s -> Exp (s,x) -> Exp (s,x) -> Exp s
| nil : Exp s
| cons : Exp s -> Exp s -> Exp s
| foldr : Exp s -> Exp s -> Exp s -> Exp s
| unit : Exp s
| fix : Exp (s,x) -> Exp s
| num : Nat -> Exp s
| succ : Exp s -> Exp s
| ifz : Exp s -> Exp s -> Exp (s,x) -> Exp s

def Exp.rename : Exp s1 -> Rename s1 s2 -> Exp s2
| .var x0, f => .var (f.var x0)
| .abs a0 a1, f => .abs (a0.rename f) (a1.rename f.lift)
| .app a0 a1, f => .app (a0.rename f) (a1.rename f)
| .let_ a0 a1, f => .let_ (a0.rename f) (a1.rename f.lift)
| .letrec a0 a1 a2, f => .letrec (a0.rename f) (a1.rename f.lift) (a2.rename f.lift)
| .pair a0 a1, f => .pair (a0.rename f) (a1.rename f)
| .fst a0, f => .fst (a0.rename f)
| .snd a0, f => .snd (a0.rename f)
| .inl a0, f => .inl (a0.rename f)
| .inr a0, f => .inr (a0.rename f)
| .case_ a0 a1 a2, f => .case_ (a0.rename f) (a1.rename f.lift) (a2.rename f.lift)
| .nil, _ => .nil
| .cons a0 a1, f => .cons (a0.rename f) (a1.rename f)
| .foldr a0 a1 a2, f => .foldr (a0.rename f) (a1.rename f) (a2.rename f)
| .unit, _ => .unit
| .fix a0, f => .fix (a0.rename f.lift)
| .num a0, _ => .num a0
| .succ a0, f => .succ (a0.rename f)
| .ifz a0 a1 a2, f => .ifz (a0.rename f) (a1.rename f) (a2.rename f.lift)

theorem Exp.rename_id {t : Exp s} :
    t.rename (Rename.id) = t := by
  induction t
  case var => rfl
  case abs =>
    simp_all [Exp.rename, Ty.rename_id, Rename.lift_id]
  case app =>
    simp_all [Exp.rename]
  case let_ =>
    simp_all [Exp.rename, Rename.lift_id]
  case letrec =>
    simp_all [Exp.rename, Ty.rename_id, Rename.lift_id]
  case pair =>
    simp_all [Exp.rename]
  case fst =>
    simp_all [Exp.rename]
  case snd =>
    simp_all [Exp.rename]
  case inl =>
    simp_all [Exp.rename]
  case inr =>
    simp_all [Exp.rename]
  case case_ =>
    simp_all [Exp.rename, Rename.lift_id]
  case nil => rfl
  case cons =>
    simp_all [Exp.rename]
  case foldr =>
    simp_all [Exp.rename]
  case unit => rfl
  case fix =>
    simp_all [Exp.rename, Rename.lift_id]
  case num => rfl
  case succ =>
    simp_all [Exp.rename]
  case ifz =>
    simp_all [Exp.rename, Rename.lift_id]

theorem Exp.rename_comp {t : Exp s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (t.rename f).rename g = t.rename (f.comp g) := by
  induction t generalizing s2 s3
  case var => rfl
  case abs =>
    simp_all [Exp.rename, Ty.rename_comp, Rename.lift_comp]
  case app =>
    simp_all [Exp.rename]
  case let_ =>
    simp_all [Exp.rename, Rename.lift_comp]
  case letrec =>
    simp_all [Exp.rename, Ty.rename_comp, Rename.lift_comp]
  case pair =>
    simp_all [Exp.rename]
  case fst =>
    simp_all [Exp.rename]
  case snd =>
    simp_all [Exp.rename]
  case inl =>
    simp_all [Exp.rename]
  case inr =>
    simp_all [Exp.rename]
  case case_ =>
    simp_all [Exp.rename, Rename.lift_comp]
  case nil => rfl
  case cons =>
    simp_all [Exp.rename]
  case foldr =>
    simp_all [Exp.rename]
  case unit => rfl
  case fix =>
    simp_all [Exp.rename, Rename.lift_comp]
  case num => rfl
  case succ =>
    simp_all [Exp.rename]
  case ifz =>
    simp_all [Exp.rename, Rename.lift_comp]

end MiniML
