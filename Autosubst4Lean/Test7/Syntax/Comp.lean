import Autosubst4Lean.Test7.Debruijn

namespace RefCalc

inductive Comp : Sig -> Type where
| ret : Val s -> Comp s
| bind : Comp s -> Comp (s,x) -> Comp s
| app : Val s -> Val s -> Comp s
| lapp : Val s -> BVar s .lvar -> Comp s
| fst : Val s -> Comp s
| snd : Val s -> Comp s
| newrgn : Comp (s,l) -> Comp s
| read : BVar s .lvar -> Val s -> Comp s
| write : BVar s .lvar -> Val s -> Val s -> Comp s
| alloc : BVar s .lvar -> Val s -> Comp s

def Comp.rename : Comp s1 -> Rename s1 s2 -> Comp s2
| .ret a0, f => .ret (a0.rename f)
| .bind a0 a1, f => .bind (a0.rename f) (a1.rename f.lift)
| .app a0 a1, f => .app (a0.rename f) (a1.rename f)
| .lapp a0 x1, f => .lapp (a0.rename f) (f.var x1)
| .fst a0, f => .fst (a0.rename f)
| .snd a0, f => .snd (a0.rename f)
| .newrgn a0, f => .newrgn (a0.rename f.lift)
| .read x0 a1, f => .read (f.var x0) (a1.rename f)
| .write x0 a1 a2, f => .write (f.var x0) (a1.rename f) (a2.rename f)
| .alloc x0 a1, f => .alloc (f.var x0) (a1.rename f)

theorem Comp.rename_id {t : Comp s} :
    t.rename (Rename.id) = t := by
  induction t
  case ret =>
    simp_all [Comp.rename, Val.rename_id]
  case bind =>
    simp_all [Comp.rename, Rename.lift_id]
  case app =>
    simp_all [Comp.rename, Val.rename_id]
  case lapp =>
    simp_all [Comp.rename, Val.rename_id]
  case fst =>
    simp_all [Comp.rename, Val.rename_id]
  case snd =>
    simp_all [Comp.rename, Val.rename_id]
  case newrgn =>
    simp_all [Comp.rename, Rename.lift_id]
  case read =>
    simp_all [Comp.rename, Val.rename_id]
  case write =>
    simp_all [Comp.rename, Val.rename_id]
  case alloc =>
    simp_all [Comp.rename, Val.rename_id]

theorem Comp.rename_comp {t : Comp s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (t.rename f).rename g = t.rename (f.comp g) := by
  induction t generalizing s2 s3
  case ret =>
    simp_all [Comp.rename, Val.rename_comp]
  case bind =>
    simp_all [Comp.rename, Rename.lift_comp]
  case app =>
    simp_all [Comp.rename, Val.rename_comp]
  case lapp =>
    simp_all [Comp.rename, Val.rename_comp]
  case fst =>
    simp_all [Comp.rename, Val.rename_comp]
  case snd =>
    simp_all [Comp.rename, Val.rename_comp]
  case newrgn =>
    simp_all [Comp.rename, Rename.lift_comp]
  case read =>
    simp_all [Comp.rename, Val.rename_comp]
  case write =>
    simp_all [Comp.rename, Val.rename_comp]
  case alloc =>
    simp_all [Comp.rename, Val.rename_comp]

end RefCalc
