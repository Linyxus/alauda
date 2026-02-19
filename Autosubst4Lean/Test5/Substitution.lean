import Autosubst4Lean.Test5.Syntax

namespace Modal

structure Subst (s1 s2 : Sig) where
  var : BVar s1 .var -> Exp s2
  mvar : BVar s1 .mvar -> Exp s2

def Subst.lift (σ : Subst s1 s2) : Subst (s1,,k) (s2,,k) where
  var := fun x => by
    cases x
    case here => exact .var .here
    case there x => exact (σ.var x).rename Rename.succ
  mvar := fun x => by
    cases x
    case here => exact .mvar .here
    case there x => exact (σ.mvar x).rename Rename.succ

def Subst.liftMany (σ : Subst s1 s2) (K : Sig) : Subst (s1 ++ K) (s2 ++ K) :=
  match K with
  | [] => σ
  | k :: K => (σ.liftMany K).lift (k:=k)

def Subst.id {s : Sig} : Subst s s where
  var := fun x => .var x
  mvar := fun x => .mvar x

def Ty.subst : Ty s1 -> Subst s1 s2 -> Ty s2
| .base, _ => .base
| .arrow a0 a1, σ => .arrow (a0.subst σ) (a1.subst σ)
| .box a0, σ => .box (a0.subst σ)
| .prod a0 a1, σ => .prod (a0.subst σ) (a1.subst σ)

def Exp.subst : Exp s1 -> Subst s1 s2 -> Exp s2
| .var x0, σ => σ.var x0
| .mvar x0, σ => σ.mvar x0
| .abs a0 a1, σ => .abs (a0.subst σ) (a1.subst σ.lift)
| .app a0 a1, σ => .app (a0.subst σ) (a1.subst σ)
| .boxi a0, σ => .boxi (a0.subst σ.lift)
| .letbox a0 a1, σ => .letbox (a0.subst σ) (a1.subst σ.lift)
| .pair a0 a1, σ => .pair (a0.subst σ) (a1.subst σ)
| .fst a0, σ => .fst (a0.subst σ)
| .snd a0, σ => .snd (a0.subst σ)

theorem Subst.funext {σ1 σ2 : Subst s1 s2}
  (hvar : ∀ x, σ1.var x = σ2.var x)
  (hmvar : ∀ x, σ1.mvar x = σ2.mvar x)
  : σ1 = σ2 := by
  cases σ1; cases σ2
  simp only [Subst.mk.injEq]
  constructor
  · funext x; exact hvar x
  · funext x; exact hmvar x

def Subst.comp (σ1 : Subst s1 s2) (σ2 : Subst s2 s3) : Subst s1 s3 where
  var := fun x => (σ1.var x).subst σ2
  mvar := fun x => (σ1.mvar x).subst σ2

theorem Subst.lift_there_var_eq {σ : Subst s1 s2} {x : BVar s1 .var} :
  (σ.lift (k:=k)).var (.there x) = (σ.var x).rename Rename.succ := by
  rfl

theorem Subst.lift_there_mvar_eq {σ : Subst s1 s2} {x : BVar s1 .mvar} :
  (σ.lift (k:=k)).mvar (.there x) = (σ.mvar x).rename Rename.succ := by
  rfl

theorem Rename.lift_there_var_eq {f : Rename s1 s2} {x : BVar s1 .var} :
  (f.lift (k:=k)).var (.there x) = (f.var x).there := by
  rfl

theorem Rename.lift_there_mvar_eq {f : Rename s1 s2} {x : BVar s1 .mvar} :
  (f.lift (k:=k)).var (.there x) = (f.var x).there := by
  rfl

theorem Exp.weaken_rename_comm {t : Exp s1} {f : Rename s1 s2} :
  (t.rename Rename.succ).rename (f.lift (k:=k0)) = (t.rename f).rename (Rename.succ) := by
  simp [Exp.rename_comp, Rename.succ_lift_comm]

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
      simp [Exp.weaken_rename_comm]
      grind

theorem Mvar.weaken_subst_comm_liftMany {x : BVar (s1 ++ K) .mvar} {σ : Subst s1 s2} :
  ((σ.liftMany K).mvar x).rename ((Rename.succ (k:=k0)).liftMany K) =
  (σ.lift (k:=k0).liftMany K).mvar (((Rename.succ (k:=k0)).liftMany K).var x) := by
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
      simp [Rename.lift_there_mvar_eq]
      simp [Subst.lift_there_mvar_eq]
      simp [Exp.weaken_rename_comm]
      grind

theorem Ty.weaken_subst_comm {t : Ty (s1 ++ K)} {σ : Subst s1 s2} :
  (t.subst (σ.liftMany K)).rename ((Rename.succ (k:=k0)).liftMany K) =
  (t.rename ((Rename.succ (k:=k0)).liftMany K)).subst (σ.lift (k:=k0).liftMany K) := by
  match t with
  | .base => rfl
  | .arrow f0 f1 =>
    have ih0 := Ty.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := Ty.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K) (k0:=k0)
    simp [Ty.subst, Ty.rename, ih0, ih1]
  | .box f0 =>
    have ih0 := Ty.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    simp [Ty.subst, Ty.rename, ih0]
  | .prod f0 f1 =>
    have ih0 := Ty.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := Ty.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K) (k0:=k0)
    simp [Ty.subst, Ty.rename, ih0, ih1]

theorem Ty.weaken_subst_comm_base {t : Ty s1} {σ : Subst s1 s2} :
  (t.subst σ).rename (Rename.succ (k:=k0)) = (t.rename Rename.succ).subst (σ.lift (k:=k0)) :=
  Ty.weaken_subst_comm (K:=[])

theorem Exp.weaken_subst_comm {t : Exp (s1 ++ K)} {σ : Subst s1 s2} :
  (t.subst (σ.liftMany K)).rename ((Rename.succ (k:=k0)).liftMany K) =
  (t.rename ((Rename.succ (k:=k0)).liftMany K)).subst (σ.lift (k:=k0).liftMany K) := by
  match t with
  | .var x =>
    simp [Exp.subst, Exp.rename]
    exact Var.weaken_subst_comm_liftMany
  | .mvar x =>
    simp [Exp.subst, Exp.rename]
    exact Mvar.weaken_subst_comm_liftMany
  | .abs f0 f1 =>
    have ih0 := Ty.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := Exp.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K,x) (k0:=k0)
    simp [Exp.subst, Exp.rename, ih0]
    exact ih1
  | .app f0 f1 =>
    have ih0 := Exp.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := Exp.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K) (k0:=k0)
    simp [Exp.subst, Exp.rename, ih0, ih1]
  | .boxi f0 =>
    have ih0 := Exp.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K,m) (k0:=k0)
    simp [Exp.subst, Exp.rename]
    exact ih0
  | .letbox f0 f1 =>
    have ih0 := Exp.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := Exp.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K,m) (k0:=k0)
    simp [Exp.subst, Exp.rename, ih0]
    exact ih1
  | .pair f0 f1 =>
    have ih0 := Exp.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := Exp.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K) (k0:=k0)
    simp [Exp.subst, Exp.rename, ih0, ih1]
  | .fst f0 =>
    have ih0 := Exp.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    simp [Exp.subst, Exp.rename, ih0]
  | .snd f0 =>
    have ih0 := Exp.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    simp [Exp.subst, Exp.rename, ih0]

theorem Exp.weaken_subst_comm_base {t : Exp s1} {σ : Subst s1 s2} :
  (t.subst σ).rename (Rename.succ (k:=k0)) = (t.rename Rename.succ).subst (σ.lift (k:=k0)) :=
  Exp.weaken_subst_comm (K:=[])

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
      simp only [Exp.weaken_subst_comm_base, Subst.comp]
  · intro x
    cases x with
    | here => rfl
    | there x0 =>
      conv =>
        lhs; simp only [Subst.comp, Subst.lift_there_mvar_eq]
      simp only [Subst.lift_there_mvar_eq]
      simp only [Exp.weaken_subst_comm_base, Subst.comp]

theorem Subst.comp_liftMany {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} {K : Sig} :
  (σ1.liftMany K).comp (σ2.liftMany K) = (σ1.comp σ2).liftMany K := by
  induction K with
  | nil => rfl
  | cons k K ih =>
    simp [Subst.liftMany]
    rw [Subst.comp_lift, ih]

theorem Ty.subst_comp {t : Ty s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (t.subst σ1).subst σ2 = t.subst (σ1.comp σ2) := by
  induction t generalizing s2 s3 with
  | base => rfl
  | arrow _ _ ih0 ih1 =>
    simp_all [Ty.subst]
  | box _ ih0 =>
    simp_all [Ty.subst]
  | prod _ _ ih0 ih1 =>
    simp_all [Ty.subst]

theorem Exp.subst_comp {t : Exp s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (t.subst σ1).subst σ2 = t.subst (σ1.comp σ2) := by
  induction t generalizing s2 s3 with
  | var => simp [Exp.subst, Subst.comp]
  | mvar => simp [Exp.subst, Subst.comp]
  | abs _ _ ih0 =>
    simp_all [Exp.subst, Ty.subst_comp, Subst.comp_lift]
  | app _ _ ih0 ih1 =>
    simp_all [Exp.subst]
  | boxi _ ih0 =>
    simp_all [Exp.subst, Subst.comp_lift]
  | letbox _ _ ih0 ih1 =>
    simp_all [Exp.subst, Subst.comp_lift]
  | pair _ _ ih0 ih1 =>
    simp_all [Exp.subst]
  | fst _ ih0 =>
    simp_all [Exp.subst]
  | snd _ ih0 =>
    simp_all [Exp.subst]

theorem Subst.lift_id :
  (Subst.id (s:=s)).lift (k:=k) = Subst.id := by
  apply Subst.funext
  · intro x
    cases x <;> rfl
  · intro x
    cases x <;> rfl

theorem Ty.subst_id {t : Ty s} :
  t.subst Subst.id = t := by
  induction t with
  | base => rfl
  | arrow _ _ ih0 ih1 =>
    simp_all [Ty.subst]
  | box _ ih0 =>
    simp_all [Ty.subst]
  | prod _ _ ih0 ih1 =>
    simp_all [Ty.subst]

theorem Exp.subst_id {t : Exp s} :
  t.subst Subst.id = t := by
  induction t with
  | var => simp [Exp.subst, Subst.id]
  | mvar => simp [Exp.subst, Subst.id]
  | abs _ _ ih0 =>
    simp_all [Exp.subst, Ty.subst_id, Subst.lift_id]
  | app _ _ ih0 ih1 =>
    simp_all [Exp.subst]
  | boxi _ ih0 =>
    simp_all [Exp.subst, Subst.lift_id]
  | letbox _ _ ih0 ih1 =>
    simp_all [Exp.subst, Subst.lift_id]
  | pair _ _ ih0 ih1 =>
    simp_all [Exp.subst]
  | fst _ ih0 =>
    simp_all [Exp.subst]
  | snd _ ih0 =>
    simp_all [Exp.subst]

end Modal
