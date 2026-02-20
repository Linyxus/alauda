import LeanTests.Test9.Syntax

namespace Effect

structure Subst (s1 s2 : Sig) where
  var : BVar s1 .var -> Exp s2
  tvar : BVar s1 .tvar -> Ty s2
  evar : BVar s1 .evar -> Eff s2

def Subst.lift (σ : Subst s1 s2) : Subst (s1,,k) (s2,,k) where
  var := fun x => by
    cases x
    case here => exact .var .here
    case there x => exact (σ.var x).rename Rename.succ
  tvar := fun x => by
    cases x
    case here => exact .tvar .here
    case there x => exact (σ.tvar x).rename Rename.succ
  evar := fun x => by
    cases x
    case here => exact .evar .here
    case there x => exact (σ.evar x).rename Rename.succ

def Subst.liftMany (σ : Subst s1 s2) (K : Sig) : Subst (s1 ++ K) (s2 ++ K) :=
  match K with
  | [] => σ
  | k :: K => (σ.liftMany K).lift (k:=k)

def Subst.id {s : Sig} : Subst s s where
  var := fun x => .var x
  tvar := fun x => .tvar x
  evar := fun x => .evar x

def Eff.subst : Eff s1 -> Subst s1 s2 -> Eff s2
| .evar x0, σ => σ.evar x0
| .pure, _ => .pure
| .exn, _ => .exn
| .union a0 a1, σ => .union (a0.subst σ) (a1.subst σ)

def Ty.subst : Ty s1 -> Subst s1 s2 -> Ty s2
| .tvar x0, σ => σ.tvar x0
| .arrow a0 a1 a2, σ => .arrow (a0.subst σ) (a1.subst σ) (a2.subst σ)
| .forall_ a0, σ => .forall_ (a0.subst σ.lift)
| .eforall a0, σ => .eforall (a0.subst σ.lift)
| .prod a0 a1, σ => .prod (a0.subst σ) (a1.subst σ)
| .unit, _ => .unit

def Exp.subst : Exp s1 -> Subst s1 s2 -> Exp s2
| .var x0, σ => σ.var x0
| .abs a0 a1, σ => .abs (a0.subst σ) (a1.subst σ.lift)
| .app a0 a1, σ => .app (a0.subst σ) (a1.subst σ)
| .tabs a0, σ => .tabs (a0.subst σ.lift)
| .tapp a0 a1, σ => .tapp (a0.subst σ) (a1.subst σ)
| .eabs a0, σ => .eabs (a0.subst σ.lift)
| .eapp a0 a1, σ => .eapp (a0.subst σ) (a1.subst σ)
| .pair a0 a1, σ => .pair (a0.subst σ) (a1.subst σ)
| .fst a0, σ => .fst (a0.subst σ)
| .snd a0, σ => .snd (a0.subst σ)
| .throw a0, σ => .throw (a0.subst σ)
| .trycatch a0 a1, σ => .trycatch (a0.subst σ) (a1.subst σ.lift)
| .letin a0 a1, σ => .letin (a0.subst σ) (a1.subst σ.lift)
| .unit, _ => .unit

theorem Subst.funext {σ1 σ2 : Subst s1 s2}
  (hvar : ∀ x, σ1.var x = σ2.var x)
  (htvar : ∀ x, σ1.tvar x = σ2.tvar x)
  (hevar : ∀ x, σ1.evar x = σ2.evar x)
  : σ1 = σ2 := by
  cases σ1; cases σ2
  simp only [Subst.mk.injEq]
  constructor
  · funext x; exact hvar x
  constructor
  · funext x; exact htvar x
  · funext x; exact hevar x

def Subst.comp (σ1 : Subst s1 s2) (σ2 : Subst s2 s3) : Subst s1 s3 where
  var := fun x => (σ1.var x).subst σ2
  tvar := fun x => (σ1.tvar x).subst σ2
  evar := fun x => (σ1.evar x).subst σ2

theorem Subst.lift_there_var_eq {σ : Subst s1 s2} {x : BVar s1 .var} :
  (σ.lift (k:=k)).var (.there x) = (σ.var x).rename Rename.succ := by
  rfl

theorem Subst.lift_there_tvar_eq {σ : Subst s1 s2} {x : BVar s1 .tvar} :
  (σ.lift (k:=k)).tvar (.there x) = (σ.tvar x).rename Rename.succ := by
  rfl

theorem Subst.lift_there_evar_eq {σ : Subst s1 s2} {x : BVar s1 .evar} :
  (σ.lift (k:=k)).evar (.there x) = (σ.evar x).rename Rename.succ := by
  rfl

theorem Rename.lift_there_var_eq {f : Rename s1 s2} {x : BVar s1 .var} :
  (f.lift (k:=k)).var (.there x) = (f.var x).there := by
  rfl

theorem Rename.lift_there_tvar_eq {f : Rename s1 s2} {x : BVar s1 .tvar} :
  (f.lift (k:=k)).var (.there x) = (f.var x).there := by
  rfl

theorem Rename.lift_there_evar_eq {f : Rename s1 s2} {x : BVar s1 .evar} :
  (f.lift (k:=k)).var (.there x) = (f.var x).there := by
  rfl

theorem Exp.weaken_rename_comm {t : Exp s1} {f : Rename s1 s2} :
  (t.rename Rename.succ).rename (f.lift (k:=k0)) = (t.rename f).rename (Rename.succ) := by
  simp [Exp.rename_comp, Rename.succ_lift_comm]

theorem Ty.weaken_rename_comm {t : Ty s1} {f : Rename s1 s2} :
  (t.rename Rename.succ).rename (f.lift (k:=k0)) = (t.rename f).rename (Rename.succ) := by
  simp [Ty.rename_comp, Rename.succ_lift_comm]

theorem Eff.weaken_rename_comm {t : Eff s1} {f : Rename s1 s2} :
  (t.rename Rename.succ).rename (f.lift (k:=k0)) = (t.rename f).rename (Rename.succ) := by
  simp [Eff.rename_comp, Rename.succ_lift_comm]

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

theorem Tvar.weaken_subst_comm_liftMany {x : BVar (s1 ++ K) .tvar} {σ : Subst s1 s2} :
  ((σ.liftMany K).tvar x).rename ((Rename.succ (k:=k0)).liftMany K) =
  (σ.lift (k:=k0).liftMany K).tvar (((Rename.succ (k:=k0)).liftMany K).var x) := by
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
      simp [Rename.lift_there_tvar_eq]
      simp [Subst.lift_there_tvar_eq]
      simp [Ty.weaken_rename_comm]
      grind

theorem Evar.weaken_subst_comm_liftMany {x : BVar (s1 ++ K) .evar} {σ : Subst s1 s2} :
  ((σ.liftMany K).evar x).rename ((Rename.succ (k:=k0)).liftMany K) =
  (σ.lift (k:=k0).liftMany K).evar (((Rename.succ (k:=k0)).liftMany K).var x) := by
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
      simp [Rename.lift_there_evar_eq]
      simp [Subst.lift_there_evar_eq]
      simp [Eff.weaken_rename_comm]
      grind

theorem Eff.weaken_subst_comm {t : Eff (s1 ++ K)} {σ : Subst s1 s2} :
  (t.subst (σ.liftMany K)).rename ((Rename.succ (k:=k0)).liftMany K) =
  (t.rename ((Rename.succ (k:=k0)).liftMany K)).subst (σ.lift (k:=k0).liftMany K) := by
  match t with
  | .evar x =>
    simp [Eff.subst, Eff.rename]
    exact Evar.weaken_subst_comm_liftMany
  | .pure => rfl
  | .exn => rfl
  | .union f0 f1 =>
    have ih0 := Eff.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := Eff.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K) (k0:=k0)
    simp [Eff.subst, Eff.rename, ih0, ih1]

theorem Eff.weaken_subst_comm_base {t : Eff s1} {σ : Subst s1 s2} :
  (t.subst σ).rename (Rename.succ (k:=k0)) = (t.rename Rename.succ).subst (σ.lift (k:=k0)) :=
  Eff.weaken_subst_comm (K:=[])

theorem Ty.weaken_subst_comm {t : Ty (s1 ++ K)} {σ : Subst s1 s2} :
  (t.subst (σ.liftMany K)).rename ((Rename.succ (k:=k0)).liftMany K) =
  (t.rename ((Rename.succ (k:=k0)).liftMany K)).subst (σ.lift (k:=k0).liftMany K) := by
  match t with
  | .tvar x =>
    simp [Ty.subst, Ty.rename]
    exact Tvar.weaken_subst_comm_liftMany
  | .arrow f0 f1 f2 =>
    have ih0 := Ty.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := Eff.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K) (k0:=k0)
    have ih2 := Ty.weaken_subst_comm (t:=f2) (σ:=σ) (K:=K) (k0:=k0)
    simp [Ty.subst, Ty.rename, ih0, ih1, ih2]
  | .forall_ f0 =>
    have ih0 := Ty.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K,X) (k0:=k0)
    simp [Ty.subst, Ty.rename]
    exact ih0
  | .eforall f0 =>
    have ih0 := Ty.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K,e) (k0:=k0)
    simp [Ty.subst, Ty.rename]
    exact ih0
  | .prod f0 f1 =>
    have ih0 := Ty.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := Ty.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K) (k0:=k0)
    simp [Ty.subst, Ty.rename, ih0, ih1]
  | .unit => rfl

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
  | .abs f0 f1 =>
    have ih0 := Ty.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := Exp.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K,x) (k0:=k0)
    simp [Exp.subst, Exp.rename, ih0]
    exact ih1
  | .app f0 f1 =>
    have ih0 := Exp.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := Exp.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K) (k0:=k0)
    simp [Exp.subst, Exp.rename, ih0, ih1]
  | .tabs f0 =>
    have ih0 := Exp.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K,X) (k0:=k0)
    simp [Exp.subst, Exp.rename]
    exact ih0
  | .tapp f0 f1 =>
    have ih0 := Exp.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := Ty.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K) (k0:=k0)
    simp [Exp.subst, Exp.rename, ih0, ih1]
  | .eabs f0 =>
    have ih0 := Exp.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K,e) (k0:=k0)
    simp [Exp.subst, Exp.rename]
    exact ih0
  | .eapp f0 f1 =>
    have ih0 := Exp.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := Eff.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K) (k0:=k0)
    simp [Exp.subst, Exp.rename, ih0, ih1]
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
  | .throw f0 =>
    have ih0 := Exp.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    simp [Exp.subst, Exp.rename, ih0]
  | .trycatch f0 f1 =>
    have ih0 := Exp.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := Exp.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K,x) (k0:=k0)
    simp [Exp.subst, Exp.rename, ih0]
    exact ih1
  | .letin f0 f1 =>
    have ih0 := Exp.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := Exp.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K,x) (k0:=k0)
    simp [Exp.subst, Exp.rename, ih0]
    exact ih1
  | .unit => rfl

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
        lhs; simp only [Subst.comp, Subst.lift_there_tvar_eq]
      simp only [Subst.lift_there_tvar_eq]
      simp only [Ty.weaken_subst_comm_base, Subst.comp]
  · intro x
    cases x with
    | here => rfl
    | there x0 =>
      conv =>
        lhs; simp only [Subst.comp, Subst.lift_there_evar_eq]
      simp only [Subst.lift_there_evar_eq]
      simp only [Eff.weaken_subst_comm_base, Subst.comp]

theorem Subst.comp_liftMany {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} {K : Sig} :
  (σ1.liftMany K).comp (σ2.liftMany K) = (σ1.comp σ2).liftMany K := by
  induction K with
  | nil => rfl
  | cons k K ih =>
    simp [Subst.liftMany]
    rw [Subst.comp_lift, ih]

theorem Eff.subst_comp {t : Eff s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (t.subst σ1).subst σ2 = t.subst (σ1.comp σ2) := by
  induction t generalizing s2 s3 with
  | evar => simp [Eff.subst, Subst.comp]
  | pure => rfl
  | exn => rfl
  | union _ _ ih0 ih1 =>
    simp_all [Eff.subst]

theorem Ty.subst_comp {t : Ty s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (t.subst σ1).subst σ2 = t.subst (σ1.comp σ2) := by
  induction t generalizing s2 s3 with
  | tvar => simp [Ty.subst, Subst.comp]
  | arrow _ _ _ ih0 ih1 =>
    simp_all [Ty.subst, Eff.subst_comp]
  | forall_ _ ih0 =>
    simp_all [Ty.subst, Subst.comp_lift]
  | eforall _ ih0 =>
    simp_all [Ty.subst, Subst.comp_lift]
  | prod _ _ ih0 ih1 =>
    simp_all [Ty.subst]
  | unit => rfl

theorem Exp.subst_comp {t : Exp s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (t.subst σ1).subst σ2 = t.subst (σ1.comp σ2) := by
  induction t generalizing s2 s3 with
  | var => simp [Exp.subst, Subst.comp]
  | abs _ _ ih0 =>
    simp_all [Exp.subst, Ty.subst_comp, Subst.comp_lift]
  | app _ _ ih0 ih1 =>
    simp_all [Exp.subst]
  | tabs _ ih0 =>
    simp_all [Exp.subst, Subst.comp_lift]
  | tapp _ _ ih0 =>
    simp_all [Exp.subst, Ty.subst_comp]
  | eabs _ ih0 =>
    simp_all [Exp.subst, Subst.comp_lift]
  | eapp _ _ ih0 =>
    simp_all [Exp.subst, Eff.subst_comp]
  | pair _ _ ih0 ih1 =>
    simp_all [Exp.subst]
  | fst _ ih0 =>
    simp_all [Exp.subst]
  | snd _ ih0 =>
    simp_all [Exp.subst]
  | throw _ ih0 =>
    simp_all [Exp.subst]
  | trycatch _ _ ih0 ih1 =>
    simp_all [Exp.subst, Subst.comp_lift]
  | letin _ _ ih0 ih1 =>
    simp_all [Exp.subst, Subst.comp_lift]
  | unit => rfl

theorem Subst.lift_id :
  (Subst.id (s:=s)).lift (k:=k) = Subst.id := by
  apply Subst.funext
  · intro x
    cases x <;> rfl
  · intro x
    cases x <;> rfl
  · intro x
    cases x <;> rfl

theorem Eff.subst_id {t : Eff s} :
  t.subst Subst.id = t := by
  induction t with
  | evar => simp [Eff.subst, Subst.id]
  | pure => rfl
  | exn => rfl
  | union _ _ ih0 ih1 =>
    simp_all [Eff.subst]

theorem Ty.subst_id {t : Ty s} :
  t.subst Subst.id = t := by
  induction t with
  | tvar => simp [Ty.subst, Subst.id]
  | arrow _ _ _ ih0 ih1 =>
    simp_all [Ty.subst, Eff.subst_id]
  | forall_ _ ih0 =>
    simp_all [Ty.subst, Subst.lift_id]
  | eforall _ ih0 =>
    simp_all [Ty.subst, Subst.lift_id]
  | prod _ _ ih0 ih1 =>
    simp_all [Ty.subst]
  | unit => rfl

theorem Exp.subst_id {t : Exp s} :
  t.subst Subst.id = t := by
  induction t with
  | var => simp [Exp.subst, Subst.id]
  | abs _ _ ih0 =>
    simp_all [Exp.subst, Ty.subst_id, Subst.lift_id]
  | app _ _ ih0 ih1 =>
    simp_all [Exp.subst]
  | tabs _ ih0 =>
    simp_all [Exp.subst, Subst.lift_id]
  | tapp _ _ ih0 =>
    simp_all [Exp.subst, Ty.subst_id]
  | eabs _ ih0 =>
    simp_all [Exp.subst, Subst.lift_id]
  | eapp _ _ ih0 =>
    simp_all [Exp.subst, Eff.subst_id]
  | pair _ _ ih0 ih1 =>
    simp_all [Exp.subst]
  | fst _ ih0 =>
    simp_all [Exp.subst]
  | snd _ ih0 =>
    simp_all [Exp.subst]
  | throw _ ih0 =>
    simp_all [Exp.subst]
  | trycatch _ _ ih0 ih1 =>
    simp_all [Exp.subst, Subst.lift_id]
  | letin _ _ ih0 ih1 =>
    simp_all [Exp.subst, Subst.lift_id]
  | unit => rfl

end Effect
