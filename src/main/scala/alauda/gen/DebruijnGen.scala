package alauda.gen

import alauda.dsl.*

object DebruijnGen:
  def generate(spec: LangSpec): String =
    val ns = spec.name
    val kinds = spec.kinds
    val sb = new StringBuilder

    sb ++= s"import Mathlib.Tactic\n\n"
    sb ++= s"namespace $ns\n\n"

    // Enums
    for e <- spec.enums do
      sb ++= s"inductive ${e.name} : Type where\n"
      for v <- e.variants do
        sb ++= s"| $v : ${e.name}\n"
      sb ++= "\n"

    // Kind inductive
    sb ++= s"inductive Kind : Type where\n"
    for k <- kinds do
      sb ++= s"| ${k.name} : Kind\n"
    sb ++= "\n"

    // Sig
    sb ++= "@[reducible]\ndef Sig : Type := List Kind\n\n"
    sb ++= "instance Sig.instEmptyCollection : EmptyCollection Sig where\n"
    sb ++= "  emptyCollection := []\n\n"

    for k <- kinds do
      sb ++= s"def Sig.extend_${k.name} : Sig -> Sig := fun s => .${k.name} :: s\n"
    sb ++= s"def Sig.extend : Sig -> Kind -> Sig := fun s k => k :: s\n\n"

    sb ++= s"def Sig.extendMany : Sig -> Sig -> Sig\n"
    sb ++= s"| s, [] => s\n"
    sb ++= s"| s, k :: K => (s.extendMany K).extend k\n\n"

    // Postfix notations
    for k <- kinds do
      sb ++= s"""postfix:80 ",${k.postfix}" => Sig.extend_${k.name}\n"""
    sb ++= s"""infixl:65 ",," => Sig.extend\n\n"""

    sb ++= "instance Sig.instAppend : Append Sig where\n"
    sb ++= "  append := Sig.extendMany\n\n"

    // BVar
    sb ++= "inductive BVar : Sig -> Kind -> Type where\n"
    sb ++= "| here : BVar (s,,k) k\n"
    sb ++= "| there :\n"
    sb ++= "  BVar s k ->\n"
    sb ++= "  BVar (s,,k0) k\n\n"

    // Rename
    sb ++= "structure Rename (s1 s2 : Sig) where\n"
    sb ++= "  var : BVar s1 k -> BVar s2 k\n\n"

    sb ++= "def Rename.id {s : Sig} : Rename s s where\n"
    sb ++= "  var := fun x => x\n\n"

    sb ++= "def Rename.comp {s1 s2 s3 : Sig} (f1 : Rename s1 s2) (f2 : Rename s2 s3) : Rename s1 s3 where\n"
    sb ++= "  var := fun x => f2.var (f1.var x)\n\n"

    sb ++= "def Rename.lift (f : Rename s1 s2) : Rename (s1,,k) (s2,,k) where\n"
    sb ++= "  var := fun\n"
    sb ++= "    | .here => .here\n"
    sb ++= "    | .there x => .there (f.var x)\n\n"

    sb ++= "def Rename.liftMany (f : Rename s1 s2) (K : Sig) : Rename (s1 ++ K) (s2 ++ K) :=\n"
    sb ++= "  match K with\n"
    sb ++= "  | [] => f\n"
    sb ++= "  | k :: K => (f.liftMany K).lift (k:=k)\n\n"

    sb ++= "def Rename.succ : Rename s (s,,k) where\n"
    sb ++= "  var := fun x => x.there\n\n"

    // Theorems
    sb ++= "theorem Rename.funext {f1 f2 : Rename s1 s2}\n"
    sb ++= "  (hvar : ∀ {k} (x : BVar s1 k), f1.var x = f2.var x) :\n"
    sb ++= "  f1 = f2 := by\n"
    sb ++= "  cases f1; cases f2\n"
    sb ++= "  aesop\n\n"

    sb ++= "theorem Rename.succ_lift_comm {f : Rename s1 s2} :\n"
    sb ++= "  (Rename.succ (k:=k0)).comp f.lift = f.comp (Rename.succ (k:=k0)) := by\n"
    sb ++= "  apply Rename.funext\n"
    sb ++= "  intro k x\n"
    sb ++= "  cases x <;> rfl\n\n"

    sb ++= "theorem Rename.lift_id :\n"
    sb ++= "  (Rename.id (s:=s)).lift (k:=k0) = Rename.id := by\n"
    sb ++= "  apply Rename.funext\n"
    sb ++= "  intro k x\n"
    sb ++= "  cases x <;> rfl\n\n"

    sb ++= "theorem Rename.lift_comp {f1 : Rename s1 s2} {f2 : Rename s2 s3} :\n"
    sb ++= "  (f1.comp f2).lift (k:=k0) = f1.lift.comp f2.lift := by\n"
    sb ++= "  apply Rename.funext\n"
    sb ++= "  intro k x\n"
    sb ++= "  cases x <;> rfl\n\n"

    sb ++= s"end $ns\n"
    sb.toString
