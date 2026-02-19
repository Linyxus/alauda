import Autosubst4Lean.Test3.Syntax

namespace CoC

structure Subst (s1 s2 : Sig) where
  var : BVar s1 .var -> Expr s2

def Subst.lift (σ : Subst s1 s2) : Subst (s1,,k) (s2,,k) where
  var := fun x => by
    cases x
    case here => exact .var .here
    case there x => exact (σ.var x).rename Rename.succ

def Subst.liftMany (σ : Subst s1 s2) (K : Sig) : Subst (s1 ++ K) (s2 ++ K) :=
  match K with
  | [] => σ
  | k :: K => (σ.liftMany K).lift (k:=k)

def Subst.id {s : Sig} : Subst s s where
  var := fun x => .var x

def Expr.subst : Expr s1 -> Subst s1 s2 -> Expr s2
| .var x0, σ => σ.var x0
| .sort a0, _ => .sort a0
| .pi a0 a1, σ => .pi (a0.subst σ) (a1.subst σ.lift)
| .lam a0 a1, σ => .lam (a0.subst σ) (a1.subst σ.lift)
| .app a0 a1, σ => .app (a0.subst σ) (a1.subst σ)

theorem Subst.funext {σ1 σ2 : Subst s1 s2}
  (hvar : ∀ x, σ1.var x = σ2.var x)
  : σ1 = σ2 := by
  cases σ1; cases σ2
  simp only [Subst.mk.injEq]
  funext x; exact hvar x

def Subst.comp (σ1 : Subst s1 s2) (σ2 : Subst s2 s3) : Subst s1 s3 where
  var := fun x => (σ1.var x).subst σ2

theorem Subst.lift_there_var_eq {σ : Subst s1 s2} {x : BVar s1 .var} :
  (σ.lift (k:=k)).var (.there x) = (σ.var x).rename Rename.succ := by
  rfl

theorem Rename.lift_there_var_eq {f : Rename s1 s2} {x : BVar s1 .var} :
  (f.lift (k:=k)).var (.there x) = (f.var x).there := by
  rfl

theorem Expr.weaken_rename_comm {t : Expr s1} {f : Rename s1 s2} :
  (t.rename Rename.succ).rename (f.lift (k:=k0)) = (t.rename f).rename (Rename.succ) := by
  simp [Expr.rename_comp, Rename.succ_lift_comm]

theorem Var.weaken_subst_comm_liftMany {x : BVar (s1 ++ K) .var} {σ : Subst s1 s2} :
  ((σ.liftMany K).var x).rename ((Rename.succ (k:=k0)).liftMany K) =
  (σ.lift (k:=k0).liftMany K).var (((Rename.succ (k:=k0)).liftMany K).var x) := by
  induction K with
  | nil =>
    simp [Subst.liftMany, Rename.liftMany]
    cases x with
    | here => simp [Subst.lift, Rename.succ]
    | there x => rfl
  | cons k K ih =>
    simp [Subst.liftMany, Rename.liftMany]
    cases x with
    | here => rfl
    | there x =>
      simp [Rename.lift_there_var_eq]
      simp [Subst.lift_there_var_eq]
      simp [Expr.weaken_rename_comm]
      grind

theorem Expr.weaken_subst_comm {t : Expr (s1 ++ K)} {σ : Subst s1 s2} :
  (t.subst (σ.liftMany K)).rename ((Rename.succ (k:=k0)).liftMany K) =
  (t.rename ((Rename.succ (k:=k0)).liftMany K)).subst (σ.lift (k:=k0).liftMany K) := by
  match t with
  | .var x =>
    simp [Expr.subst, Expr.rename]
    exact Var.weaken_subst_comm_liftMany
  | .sort _ => rfl
  | .pi f0 f1 =>
    have ih0 := Expr.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := Expr.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K,x) (k0:=k0)
    simp [Expr.subst, Expr.rename, ih0]
    exact ih1
  | .lam f0 f1 =>
    have ih0 := Expr.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := Expr.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K,x) (k0:=k0)
    simp [Expr.subst, Expr.rename, ih0]
    exact ih1
  | .app f0 f1 =>
    have ih0 := Expr.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := Expr.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K) (k0:=k0)
    simp [Expr.subst, Expr.rename, ih0, ih1]

theorem Expr.weaken_subst_comm_base {t : Expr s1} {σ : Subst s1 s2} :
  (t.subst σ).rename (Rename.succ (k:=k0)) = (t.rename Rename.succ).subst (σ.lift (k:=k0)) :=
  Expr.weaken_subst_comm (K:=[])

theorem Subst.comp_lift {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} {k : Kind} :
  (σ1.lift (k := k)).comp (σ2.lift (k := k)) = (σ1.comp σ2).lift (k := k) := by
  apply Subst.funext
  · intro x
    cases x with
    | here => rfl
    | there x0 =>
      conv =>
        lhs; simp only [Subst.comp, Subst.lift_there_var_eq]
      simp only [Subst.lift_there_var_eq]
      simp only [Expr.weaken_subst_comm_base, Subst.comp]

theorem Subst.comp_liftMany {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} {K : Sig} :
  (σ1.liftMany K).comp (σ2.liftMany K) = (σ1.comp σ2).liftMany K := by
  induction K with
  | nil => rfl
  | cons k K ih =>
    simp [Subst.liftMany]
    rw [Subst.comp_lift, ih]

theorem Expr.subst_comp {t : Expr s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (t.subst σ1).subst σ2 = t.subst (σ1.comp σ2) := by
  induction t generalizing s2 s3 with
  | var => simp [Expr.subst, Subst.comp]
  | sort => rfl
  | pi _ _ ih0 ih1 =>
    simp_all [Expr.subst, Subst.comp_lift]
  | lam _ _ ih0 ih1 =>
    simp_all [Expr.subst, Subst.comp_lift]
  | app _ _ ih0 ih1 =>
    simp_all [Expr.subst]

theorem Subst.lift_id :
  (Subst.id (s:=s)).lift (k:=k) = Subst.id := by
  apply Subst.funext
  · intro x
    cases x <;> rfl

theorem Expr.subst_id {t : Expr s} :
  t.subst Subst.id = t := by
  induction t with
  | var => simp [Expr.subst, Subst.id]
  | sort => rfl
  | pi _ _ ih0 ih1 =>
    simp_all [Expr.subst, Subst.lift_id]
  | lam _ _ ih0 ih1 =>
    simp_all [Expr.subst, Subst.lift_id]
  | app _ _ ih0 ih1 =>
    simp_all [Expr.subst]

end CoC
