import Autosubst4Lean.Test.Syntax

namespace CC

structure Subst (s1 s2 : Sig) where
  var : BVar s1 .var -> Var .var s2
  tvar : BVar s1 .tvar -> Ty .shape s2
  cvar : BVar s1 .cvar -> CaptureSet s2

def Subst.lift (σ : Subst s1 s2) : Subst (s1,,k) (s2,,k) where
  var := fun x => by
    cases x
    case here => exact .bound .here
    case there x => exact (σ.var x).rename Rename.succ
  tvar := fun x => by
    cases x
    case here => exact .tvar .here
    case there x => exact (σ.tvar x).rename Rename.succ
  cvar := fun x => by
    cases x
    case here => exact .cvar .here
    case there x => exact (σ.cvar x).rename Rename.succ

def Subst.liftMany (σ : Subst s1 s2) (K : Sig) : Subst (s1 ++ K) (s2 ++ K) :=
  match K with
  | [] => σ
  | k :: K => (σ.liftMany K).lift (k:=k)

def Subst.id {s : Sig} : Subst s s where
  var := fun x => .bound x
  tvar := fun x => .tvar x
  cvar := fun x => .cvar x

def Var.subst : Var .var s1 -> Subst s1 s2 -> Var .var s2
| .bound x0, σ => σ.var x0
| .free a0, _ => .free a0

def CaptureSet.subst : CaptureSet s1 -> Subst s1 s2 -> CaptureSet s2
| .empty, _ => .empty
| .union a0 a1, σ => .union (a0.subst σ) (a1.subst σ)
| .var x0, σ => .var (x0.subst σ)
| .cvar x0, σ => σ.cvar x0

def CaptureBound.subst : CaptureBound s1 -> Subst s1 s2 -> CaptureBound s2
| .unbound, _ => .unbound
| .bound a0, σ => .bound (a0.subst σ)

def Ty.subst {tySort : TySort} : Ty tySort s1 -> Subst s1 s2 -> Ty tySort s2
| .top, _ => .top
| .tvar x0, σ => σ.tvar x0
| .arrow a0 a1, σ => .arrow (a0.subst σ) (a1.subst σ.lift)
| .poly a0 a1, σ => .poly (a0.subst σ) (a1.subst σ.lift)
| .cpoly a0 a1, σ => .cpoly (a0.subst σ) (a1.subst σ.lift)
| .unit, _ => .unit
| .cap, _ => .cap
| .bool, _ => .bool
| .cell, _ => .cell
| .capt a0 a1, σ => .capt (a0.subst σ) (a1.subst σ)
| .exi a0, σ => .exi (a0.subst σ.lift)
| .typ a0, σ => .typ (a0.subst σ)

def Exp.subst : Exp s1 -> Subst s1 s2 -> Exp s2
| .var x0, σ => .var (x0.subst σ)
| .abs a0 a1 a2, σ => .abs (a0.subst σ) (a1.subst σ) (a2.subst σ.lift)
| .tabs a0 a1 a2, σ => .tabs (a0.subst σ) (a1.subst σ) (a2.subst σ.lift)
| .cabs a0 a1 a2, σ => .cabs (a0.subst σ) (a1.subst σ) (a2.subst σ.lift)
| .pack a0 x1, σ => .pack (a0.subst σ) (x1.subst σ)
| .app x0 x1, σ => .app (x0.subst σ) (x1.subst σ)
| .tapp x0 a1, σ => .tapp (x0.subst σ) (a1.subst σ)
| .capp x0 a1, σ => .capp (x0.subst σ) (a1.subst σ)
| .letin a0 a1, σ => .letin (a0.subst σ) (a1.subst σ.lift)
| .unpack a0 a1, σ => .unpack (a0.subst σ) (a1.subst σ.lift.lift)
| .unit, _ => .unit
| .btrue, _ => .btrue
| .bfalse, _ => .bfalse
| .read x0, σ => .read (x0.subst σ)
| .write x0 x1, σ => .write (x0.subst σ) (x1.subst σ)
| .cond x0 a1 a2, σ => .cond (x0.subst σ) (a1.subst σ) (a2.subst σ)

theorem Subst.funext {σ1 σ2 : Subst s1 s2}
  (hvar : ∀ x, σ1.var x = σ2.var x)
  (htvar : ∀ x, σ1.tvar x = σ2.tvar x)
  (hcvar : ∀ x, σ1.cvar x = σ2.cvar x)
  : σ1 = σ2 := by
  cases σ1; cases σ2
  simp only [Subst.mk.injEq]
  constructor
  · funext x; exact hvar x
  constructor
  · funext x; exact htvar x
  · funext x; exact hcvar x

def Subst.comp (σ1 : Subst s1 s2) (σ2 : Subst s2 s3) : Subst s1 s3 where
  var := fun x => (σ1.var x).subst σ2
  tvar := fun x => (σ1.tvar x).subst σ2
  cvar := fun x => (σ1.cvar x).subst σ2

theorem Subst.lift_there_var_eq {σ : Subst s1 s2} {x : BVar s1 .var} :
  (σ.lift (k:=k)).var (.there x) = (σ.var x).rename Rename.succ := by
  rfl

theorem Subst.lift_there_tvar_eq {σ : Subst s1 s2} {x : BVar s1 .tvar} :
  (σ.lift (k:=k)).tvar (.there x) = (σ.tvar x).rename Rename.succ := by
  rfl

theorem Subst.lift_there_cvar_eq {σ : Subst s1 s2} {x : BVar s1 .cvar} :
  (σ.lift (k:=k)).cvar (.there x) = (σ.cvar x).rename Rename.succ := by
  rfl

theorem Rename.lift_there_var_eq {f : Rename s1 s2} {x : BVar s1 .var} :
  (f.lift (k:=k)).var (.there x) = (f.var x).there := by
  rfl

theorem Rename.lift_there_tvar_eq {f : Rename s1 s2} {x : BVar s1 .tvar} :
  (f.lift (k:=k)).var (.there x) = (f.var x).there := by
  rfl

theorem Rename.lift_there_cvar_eq {f : Rename s1 s2} {x : BVar s1 .cvar} :
  (f.lift (k:=k)).var (.there x) = (f.var x).there := by
  rfl

theorem Var.weaken_rename_comm {t : Var .var s1} {f : Rename s1 s2} :
  (t.rename Rename.succ).rename (f.lift (k:=k0)) = (t.rename f).rename (Rename.succ) := by
  simp [Var.rename_comp, Rename.succ_lift_comm]

theorem Ty.weaken_rename_comm {tySort : TySort} {t : Ty tySort s1} {f : Rename s1 s2} :
  (t.rename Rename.succ).rename (f.lift (k:=k0)) = (t.rename f).rename (Rename.succ) := by
  simp [Ty.rename_comp, Rename.succ_lift_comm]

theorem CaptureSet.weaken_rename_comm {t : CaptureSet s1} {f : Rename s1 s2} :
  (t.rename Rename.succ).rename (f.lift (k:=k0)) = (t.rename f).rename (Rename.succ) := by
  simp [CaptureSet.rename_comp, Rename.succ_lift_comm]

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
      simp [Var.weaken_rename_comm]
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

theorem Cvar.weaken_subst_comm_liftMany {x : BVar (s1 ++ K) .cvar} {σ : Subst s1 s2} :
  ((σ.liftMany K).cvar x).rename ((Rename.succ (k:=k0)).liftMany K) =
  (σ.lift (k:=k0).liftMany K).cvar (((Rename.succ (k:=k0)).liftMany K).var x) := by
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
      simp [Rename.lift_there_cvar_eq]
      simp [Subst.lift_there_cvar_eq]
      simp [CaptureSet.weaken_rename_comm]
      grind

theorem Var.weaken_subst_comm {t : Var .var (s1 ++ K)} {σ : Subst s1 s2} :
  (t.subst (σ.liftMany K)).rename ((Rename.succ (k:=k0)).liftMany K) =
  (t.rename ((Rename.succ (k:=k0)).liftMany K)).subst (σ.lift (k:=k0).liftMany K) := by
  match t with
  | .bound x =>
    simp [Var.subst, Var.rename]
    exact Var.weaken_subst_comm_liftMany
  | .free _ => rfl

theorem Var.weaken_subst_comm_base {t : Var .var s1} {σ : Subst s1 s2} :
  (t.subst σ).rename (Rename.succ (k:=k0)) = (t.rename Rename.succ).subst (σ.lift (k:=k0)) :=
  Var.weaken_subst_comm (K:=[])

theorem CaptureSet.weaken_subst_comm {t : CaptureSet (s1 ++ K)} {σ : Subst s1 s2} :
  (t.subst (σ.liftMany K)).rename ((Rename.succ (k:=k0)).liftMany K) =
  (t.rename ((Rename.succ (k:=k0)).liftMany K)).subst (σ.lift (k:=k0).liftMany K) := by
  match t with
  | .empty => rfl
  | .union f0 f1 =>
    have ih0 := CaptureSet.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := CaptureSet.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K) (k0:=k0)
    simp [CaptureSet.subst, CaptureSet.rename, ih0, ih1]
  | .var f0 =>
    have ih0 := Var.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    simp [CaptureSet.subst, CaptureSet.rename, ih0]
  | .cvar x =>
    simp [CaptureSet.subst, CaptureSet.rename]
    exact Cvar.weaken_subst_comm_liftMany

theorem CaptureSet.weaken_subst_comm_base {t : CaptureSet s1} {σ : Subst s1 s2} :
  (t.subst σ).rename (Rename.succ (k:=k0)) = (t.rename Rename.succ).subst (σ.lift (k:=k0)) :=
  CaptureSet.weaken_subst_comm (K:=[])

theorem CaptureBound.weaken_subst_comm {t : CaptureBound (s1 ++ K)} {σ : Subst s1 s2} :
  (t.subst (σ.liftMany K)).rename ((Rename.succ (k:=k0)).liftMany K) =
  (t.rename ((Rename.succ (k:=k0)).liftMany K)).subst (σ.lift (k:=k0).liftMany K) := by
  match t with
  | .unbound => rfl
  | .bound f0 =>
    have ih0 := CaptureSet.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    simp [CaptureBound.subst, CaptureBound.rename, ih0]

theorem CaptureBound.weaken_subst_comm_base {t : CaptureBound s1} {σ : Subst s1 s2} :
  (t.subst σ).rename (Rename.succ (k:=k0)) = (t.rename Rename.succ).subst (σ.lift (k:=k0)) :=
  CaptureBound.weaken_subst_comm (K:=[])

theorem Ty.weaken_subst_comm {tySort : TySort} {t : Ty tySort (s1 ++ K)} {σ : Subst s1 s2} :
  (t.subst (σ.liftMany K)).rename ((Rename.succ (k:=k0)).liftMany K) =
  (t.rename ((Rename.succ (k:=k0)).liftMany K)).subst (σ.lift (k:=k0).liftMany K) := by
  match t with
  | .top => rfl
  | .tvar x =>
    simp [Ty.subst, Ty.rename]
    exact Tvar.weaken_subst_comm_liftMany
  | .arrow f0 f1 =>
    have ih0 := Ty.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := Ty.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K,x) (k0:=k0)
    simp [Ty.subst, Ty.rename, ih0]
    exact ih1
  | .poly f0 f1 =>
    have ih0 := Ty.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := Ty.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K,X) (k0:=k0)
    simp [Ty.subst, Ty.rename, ih0]
    exact ih1
  | .cpoly f0 f1 =>
    have ih0 := CaptureBound.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := Ty.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K,C) (k0:=k0)
    simp [Ty.subst, Ty.rename, ih0]
    exact ih1
  | .unit => rfl
  | .cap => rfl
  | .bool => rfl
  | .cell => rfl
  | .capt f0 f1 =>
    have ih0 := CaptureSet.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := Ty.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K) (k0:=k0)
    simp [Ty.subst, Ty.rename, ih0, ih1]
  | .exi f0 =>
    have ih0 := Ty.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K,C) (k0:=k0)
    simp [Ty.subst, Ty.rename]
    exact ih0
  | .typ f0 =>
    have ih0 := Ty.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    simp [Ty.subst, Ty.rename, ih0]

theorem Ty.weaken_subst_comm_base {tySort : TySort} {t : Ty tySort s1} {σ : Subst s1 s2} :
  (t.subst σ).rename (Rename.succ (k:=k0)) = (t.rename Rename.succ).subst (σ.lift (k:=k0)) :=
  Ty.weaken_subst_comm (K:=[])

theorem Exp.weaken_subst_comm {t : Exp (s1 ++ K)} {σ : Subst s1 s2} :
  (t.subst (σ.liftMany K)).rename ((Rename.succ (k:=k0)).liftMany K) =
  (t.rename ((Rename.succ (k:=k0)).liftMany K)).subst (σ.lift (k:=k0).liftMany K) := by
  match t with
  | .var f0 =>
    have ih0 := Var.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    simp [Exp.subst, Exp.rename, ih0]
  | .abs f0 f1 f2 =>
    have ih0 := CaptureSet.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := Ty.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K) (k0:=k0)
    have ih2 := Exp.weaken_subst_comm (t:=f2) (σ:=σ) (K:=K,x) (k0:=k0)
    simp [Exp.subst, Exp.rename, ih0, ih1]
    exact ih2
  | .tabs f0 f1 f2 =>
    have ih0 := CaptureSet.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := Ty.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K) (k0:=k0)
    have ih2 := Exp.weaken_subst_comm (t:=f2) (σ:=σ) (K:=K,X) (k0:=k0)
    simp [Exp.subst, Exp.rename, ih0, ih1]
    exact ih2
  | .cabs f0 f1 f2 =>
    have ih0 := CaptureSet.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := CaptureBound.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K) (k0:=k0)
    have ih2 := Exp.weaken_subst_comm (t:=f2) (σ:=σ) (K:=K,C) (k0:=k0)
    simp [Exp.subst, Exp.rename, ih0, ih1]
    exact ih2
  | .pack f0 f1 =>
    have ih0 := CaptureSet.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := Var.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K) (k0:=k0)
    simp [Exp.subst, Exp.rename, ih0, ih1]
  | .app f0 f1 =>
    have ih0 := Var.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := Var.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K) (k0:=k0)
    simp [Exp.subst, Exp.rename, ih0, ih1]
  | .tapp f0 f1 =>
    have ih0 := Var.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := Ty.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K) (k0:=k0)
    simp [Exp.subst, Exp.rename, ih0, ih1]
  | .capp f0 f1 =>
    have ih0 := Var.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := CaptureSet.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K) (k0:=k0)
    simp [Exp.subst, Exp.rename, ih0, ih1]
  | .letin f0 f1 =>
    have ih0 := Exp.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := Exp.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K,x) (k0:=k0)
    simp [Exp.subst, Exp.rename, ih0]
    exact ih1
  | .unpack f0 f1 =>
    have ih0 := Exp.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := Exp.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K,C,x) (k0:=k0)
    simp [Exp.subst, Exp.rename, ih0]
    exact ih1
  | .unit => rfl
  | .btrue => rfl
  | .bfalse => rfl
  | .read f0 =>
    have ih0 := Var.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    simp [Exp.subst, Exp.rename, ih0]
  | .write f0 f1 =>
    have ih0 := Var.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := Var.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K) (k0:=k0)
    simp [Exp.subst, Exp.rename, ih0, ih1]
  | .cond f0 f1 f2 =>
    have ih0 := Var.weaken_subst_comm (t:=f0) (σ:=σ) (K:=K) (k0:=k0)
    have ih1 := Exp.weaken_subst_comm (t:=f1) (σ:=σ) (K:=K) (k0:=k0)
    have ih2 := Exp.weaken_subst_comm (t:=f2) (σ:=σ) (K:=K) (k0:=k0)
    simp [Exp.subst, Exp.rename, ih0, ih1, ih2]

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
      simp only [Var.weaken_subst_comm_base, Subst.comp]
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
        lhs; simp only [Subst.comp, Subst.lift_there_cvar_eq]
      simp only [Subst.lift_there_cvar_eq]
      simp only [CaptureSet.weaken_subst_comm_base, Subst.comp]

theorem Subst.comp_liftMany {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} {K : Sig} :
  (σ1.liftMany K).comp (σ2.liftMany K) = (σ1.comp σ2).liftMany K := by
  induction K with
  | nil => rfl
  | cons k K ih =>
    simp [Subst.liftMany]
    rw [Subst.comp_lift, ih]

theorem Var.subst_comp {t : Var .var s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (t.subst σ1).subst σ2 = t.subst (σ1.comp σ2) := by
  cases t with
  | bound => simp [Var.subst, Subst.comp]
  | free => rfl

theorem CaptureSet.subst_comp {t : CaptureSet s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (t.subst σ1).subst σ2 = t.subst (σ1.comp σ2) := by
  induction t generalizing s2 s3 with
  | empty => rfl
  | union _ _ ih0 ih1 =>
    simp_all [CaptureSet.subst]
  | var _ =>
    simp [CaptureSet.subst, Var.subst_comp]
  | cvar => simp [CaptureSet.subst, Subst.comp]

theorem CaptureBound.subst_comp {t : CaptureBound s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (t.subst σ1).subst σ2 = t.subst (σ1.comp σ2) := by
  induction t generalizing s2 s3 with
  | unbound => rfl
  | bound _ =>
    simp [CaptureBound.subst, CaptureSet.subst_comp]

theorem Ty.subst_comp {tySort : TySort} {t : Ty tySort s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (t.subst σ1).subst σ2 = t.subst (σ1.comp σ2) := by
  induction t generalizing s2 s3 with
  | top => rfl
  | tvar => simp [Ty.subst, Subst.comp]
  | arrow _ _ ih0 ih1 =>
    simp_all [Ty.subst, Subst.comp_lift]
  | poly _ _ ih0 ih1 =>
    simp_all [Ty.subst, Subst.comp_lift]
  | cpoly _ _ ih0 =>
    simp_all [Ty.subst, CaptureBound.subst_comp, Subst.comp_lift]
  | unit => rfl
  | cap => rfl
  | bool => rfl
  | cell => rfl
  | capt _ _ ih0 =>
    simp_all [Ty.subst, CaptureSet.subst_comp]
  | exi _ ih0 =>
    simp_all [Ty.subst, Subst.comp_lift]
  | typ _ ih0 =>
    simp_all [Ty.subst]

theorem Exp.subst_comp {t : Exp s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (t.subst σ1).subst σ2 = t.subst (σ1.comp σ2) := by
  induction t generalizing s2 s3 with
  | var _ =>
    simp [Exp.subst, Var.subst_comp]
  | abs _ _ _ ih0 =>
    simp_all [Exp.subst, CaptureSet.subst_comp, Ty.subst_comp, Subst.comp_lift]
  | tabs _ _ _ ih0 =>
    simp_all [Exp.subst, CaptureSet.subst_comp, Ty.subst_comp, Subst.comp_lift]
  | cabs _ _ _ ih0 =>
    simp_all [Exp.subst, CaptureSet.subst_comp, CaptureBound.subst_comp, Subst.comp_lift]
  | pack _ _ =>
    simp [Exp.subst, CaptureSet.subst_comp, Var.subst_comp]
  | app _ _ =>
    simp [Exp.subst, Var.subst_comp]
  | tapp _ _ =>
    simp [Exp.subst, Var.subst_comp, Ty.subst_comp]
  | capp _ _ =>
    simp [Exp.subst, Var.subst_comp, CaptureSet.subst_comp]
  | letin _ _ ih0 ih1 =>
    simp_all [Exp.subst, Subst.comp_lift]
  | unpack _ _ ih0 ih1 =>
    simp_all [Exp.subst, Subst.comp_lift]
  | unit => rfl
  | btrue => rfl
  | bfalse => rfl
  | read _ =>
    simp [Exp.subst, Var.subst_comp]
  | write _ _ =>
    simp [Exp.subst, Var.subst_comp]
  | cond _ _ _ ih0 ih1 =>
    simp_all [Exp.subst, Var.subst_comp]

theorem Subst.lift_id :
  (Subst.id (s:=s)).lift (k:=k) = Subst.id := by
  apply Subst.funext
  · intro x
    cases x <;> rfl
  · intro x
    cases x <;> rfl
  · intro x
    cases x <;> rfl

theorem Var.subst_id {t : Var .var s} :
  t.subst Subst.id = t := by
  cases t with
  | bound => simp [Var.subst, Subst.id]
  | free => rfl

theorem CaptureSet.subst_id {t : CaptureSet s} :
  t.subst Subst.id = t := by
  induction t with
  | empty => rfl
  | union _ _ ih0 ih1 =>
    simp_all [CaptureSet.subst]
  | var _ =>
    simp [CaptureSet.subst, Var.subst_id]
  | cvar => simp [CaptureSet.subst, Subst.id]

theorem CaptureBound.subst_id {t : CaptureBound s} :
  t.subst Subst.id = t := by
  induction t with
  | unbound => rfl
  | bound _ =>
    simp [CaptureBound.subst, CaptureSet.subst_id]

theorem Ty.subst_id {tySort : TySort} {t : Ty tySort s} :
  t.subst Subst.id = t := by
  induction t with
  | top => rfl
  | tvar => simp [Ty.subst, Subst.id]
  | arrow _ _ ih0 ih1 =>
    simp_all [Ty.subst, Subst.lift_id]
  | poly _ _ ih0 ih1 =>
    simp_all [Ty.subst, Subst.lift_id]
  | cpoly _ _ ih0 =>
    simp_all [Ty.subst, CaptureBound.subst_id, Subst.lift_id]
  | unit => rfl
  | cap => rfl
  | bool => rfl
  | cell => rfl
  | capt _ _ ih0 =>
    simp_all [Ty.subst, CaptureSet.subst_id]
  | exi _ ih0 =>
    simp_all [Ty.subst, Subst.lift_id]
  | typ _ ih0 =>
    simp_all [Ty.subst]

theorem Exp.subst_id {t : Exp s} :
  t.subst Subst.id = t := by
  induction t with
  | var _ =>
    simp [Exp.subst, Var.subst_id]
  | abs _ _ _ ih0 =>
    simp_all [Exp.subst, CaptureSet.subst_id, Ty.subst_id, Subst.lift_id]
  | tabs _ _ _ ih0 =>
    simp_all [Exp.subst, CaptureSet.subst_id, Ty.subst_id, Subst.lift_id]
  | cabs _ _ _ ih0 =>
    simp_all [Exp.subst, CaptureSet.subst_id, CaptureBound.subst_id, Subst.lift_id]
  | pack _ _ =>
    simp [Exp.subst, CaptureSet.subst_id, Var.subst_id]
  | app _ _ =>
    simp [Exp.subst, Var.subst_id]
  | tapp _ _ =>
    simp [Exp.subst, Var.subst_id, Ty.subst_id]
  | capp _ _ =>
    simp [Exp.subst, Var.subst_id, CaptureSet.subst_id]
  | letin _ _ ih0 ih1 =>
    simp_all [Exp.subst, Subst.lift_id]
  | unpack _ _ ih0 ih1 =>
    simp_all [Exp.subst, Subst.lift_id]
  | unit => rfl
  | btrue => rfl
  | bfalse => rfl
  | read _ =>
    simp [Exp.subst, Var.subst_id]
  | write _ _ =>
    simp [Exp.subst, Var.subst_id]
  | cond _ _ _ ih0 ih1 =>
    simp_all [Exp.subst, Var.subst_id]

end CC
