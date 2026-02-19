package alauda.gen

import alauda.dsl.*

object SyntaxGen:

  /** Generate the full Lean file for a single sort. */
  def generate(spec: LangSpec, sort: SortDef, imports: List[String]): String =
    val ns = spec.name
    val sb = new StringBuilder

    for imp <- imports do
      sb ++= s"import $imp\n"
    sb ++= "\n"
    sb ++= s"namespace $ns\n\n"

    sb ++= genInductive(spec, sort)
    sb ++= "\n"

    if hasRename(spec, sort) then
      sb ++= genRename(spec, sort)
      sb ++= "\n"
      sb ++= genRenameId(spec, sort)
      sb ++= "\n"
      sb ++= genRenameComp(spec, sort)
      sb ++= "\n"

    sb ++= s"end $ns\n"
    sb.toString

  /** Whether this sort needs a rename function (has Sig-indexed fields). */
  private def hasRename(spec: LangSpec, sort: SortDef): Boolean =
    sort.constructors.exists(c =>
      c.fields.exists(f => f.fieldType match
        case FieldType.BVarRef(_) => true
        case FieldType.SortRef(s, _) => true
        case FieldType.VarRef(_) => true
        case FieldType.Plain(_) => false
      )
    )

  // ---- Inductive generation ----

  private def genInductive(spec: LangSpec, sort: SortDef): String =
    val sb = new StringBuilder
    val indexParam = sort.index match
      case Some(idx) => s"$idx -> "
      case None => ""
    sb ++= s"inductive ${sort.name} : ${indexParam}Sig -> Type where\n"

    for ctor <- sort.constructors do
      sb ++= s"| ${ctor.name}"
      if ctor.fields.nonEmpty then
        val fieldStrs = ctor.fields.map(f => fieldTypeStr(spec, sort, f))
        val retStr = returnTypeStr(spec, sort, ctor)
        sb ++= s" : ${fieldStrs.mkString(" -> ")} -> $retStr"
      else
        val retStr = returnTypeStr(spec, sort, ctor)
        sb ++= s" : $retStr"
      sb ++= "\n"

    sb.toString

  private def fieldTypeStr(spec: LangSpec, sort: SortDef, field: Field): String =
    val sigStr = bindersToSig(spec, field.binders)
    field.fieldType match
      case FieldType.BVarRef(kind) =>
        val kindStr = if kind == "_index" then "k" else s".$kind"
        s"BVar $sigStr $kindStr"
      case FieldType.SortRef(s, Some(idx)) =>
        s"$s .$idx $sigStr"
      case FieldType.SortRef(s, None) =>
        s"$s $sigStr"
      case FieldType.VarRef(kind) =>
        val kindStr = if kind == "_index" then "k" else s".$kind"
        s"Var $kindStr $sigStr"
      case FieldType.Plain(name) =>
        name

  private def bindersToSig(spec: LangSpec, binders: List[String]): String =
    binders match
      case Nil => "s"
      case _ =>
        val inner = binders.foldLeft("s") { (acc, b) => s"($acc,$b)" }
        inner

  private def returnTypeStr(spec: LangSpec, sort: SortDef, ctor: Constructor): String =
    val idxStr = ctor.resultIndex match
      case Some(idx) => s" .$idx"
      case None =>
        sort.index match
          case Some("Kind") => " k"
          case _ => ""
    s"${sort.name}$idxStr s"

  // ---- Rename generation ----

  private def genRename(spec: LangSpec, sort: SortDef): String =
    val sb = new StringBuilder
    val indexBinder = sort.index match
      case Some(idx) if idx != "Kind" => s" {$idx : $idx}"
      case _ => ""
    val indexVar = sort.index match
      case Some(idx) if idx != "Kind" => s" $idx"  // will be lowercased
      case _ => ""

    // For indexed sorts, we need the sort parameter
    val sortParam = sort.index match
      case Some("Kind") => " {k : Kind}"
      case Some(idx) =>
        val lc = idx.take(1).toLowerCase + idx.drop(1)
        s" {$lc : $idx}"
      case None => ""

    sb ++= s"def ${sort.name}.rename$sortParam : ${sort.name}${indexVarStr(sort)} s1 -> Rename s1 s2 -> ${sort.name}${indexVarStr(sort)} s2\n"

    for (ctor, i) <- sort.constructors.zipWithIndex do
      if ctor.fields.isEmpty then
        sb ++= s"| .${ctor.name}, _ => .${ctor.name}\n"
      else
        // Check if all fields are plain (no renaming needed)
        val allPlain = ctor.fields.forall(_.fieldType.isInstanceOf[FieldType.Plain])
        if allPlain then
          sb ++= s"| .${ctor.name} ${ctor.fields.indices.map(j => s"a$j").mkString(" ")}, _ => .${ctor.name} ${ctor.fields.indices.map(j => s"a$j").mkString(" ")}\n"
        else
          val fieldNames = ctor.fields.zipWithIndex.map { (f, j) => fieldVarName(f, j) }
          val renameExprs = ctor.fields.zipWithIndex.map { (f, j) =>
            renameFieldExpr(spec, f, j)
          }
          sb ++= s"| .${ctor.name} ${fieldNames.mkString(" ")}, f => .${ctor.name} ${renameExprs.mkString(" ")}\n"

    sb.toString

  private def indexVarStr(sort: SortDef): String =
    sort.index match
      case Some("Kind") => " k"
      case Some(idx) =>
        val lc = idx.take(1).toLowerCase + idx.drop(1)
        s" $lc"
      case None => ""

  private def fieldVarName(field: Field, idx: Int): String =
    field.fieldType match
      case FieldType.BVarRef(_) => s"x$idx"
      case FieldType.SortRef(_, _) => s"a$idx"
      case FieldType.VarRef(_) => s"x$idx"
      case FieldType.Plain(_) => s"p$idx"

  private def renameFieldExpr(spec: LangSpec, field: Field, idx: Int): String =
    val name = fieldVarName(field, idx)
    val liftedF = field.binders.foldLeft("f") { (acc, _) => s"$acc.lift" }
    field.fieldType match
      case FieldType.BVarRef(_) =>
        s"($liftedF.var $name)"
      case FieldType.SortRef(_, _) =>
        s"($name.rename $liftedF)"
      case FieldType.VarRef(_) =>
        s"($name.rename $liftedF)"
      case FieldType.Plain(_) =>
        name

  // ---- rename_id theorem ----

  private def genRenameId(spec: LangSpec, sort: SortDef): String =
    val sb = new StringBuilder
    val sortParam = sortParamStr(sort)

    sb ++= s"theorem ${sort.name}.rename_id$sortParam {t : ${sort.name}${indexVarStr(sort)} s} :\n"
    sb ++= s"    t.rename (Rename.id) = t := by\n"
    sb ++= s"  induction t\n"

    for ctor <- sort.constructors do
      sb ++= genCtorCase(spec, sort, ctor, "rename_id")

    sb.toString

  // ---- rename_comp theorem ----

  private def genRenameComp(spec: LangSpec, sort: SortDef): String =
    val sb = new StringBuilder
    val sortParam = sortParamStr(sort)

    sb ++= s"theorem ${sort.name}.rename_comp$sortParam {t : ${sort.name}${indexVarStr(sort)} s1} {f : Rename s1 s2} {g : Rename s2 s3} :\n"
    sb ++= s"    (t.rename f).rename g = t.rename (f.comp g) := by\n"
    sb ++= s"  induction t generalizing s2 s3\n"

    for ctor <- sort.constructors do
      sb ++= genCtorCase(spec, sort, ctor, "rename_comp")

    sb.toString

  private def sortParamStr(sort: SortDef): String =
    sort.index match
      case Some("Kind") => " {k : Kind}"
      case Some(idx) =>
        val lc = idx.take(1).toLowerCase + idx.drop(1)
        s" {$lc : $idx}"
      case None => ""

  /** Generate a single case in a rename_id or rename_comp proof. */
  private def genCtorCase(spec: LangSpec, sort: SortDef, ctor: Constructor, theorem: String): String =
    val onlyBVarAndPlain = ctor.fields.forall(f => f.fieldType match
      case FieldType.BVarRef(_) | FieldType.Plain(_) => true
      case _ => false
    )

    if ctor.fields.isEmpty || ctor.fields.forall(_.fieldType.isInstanceOf[FieldType.Plain]) then
      s"  case ${ctor.name} => rfl\n"
    else if onlyBVarAndPlain then
      // BVar fields: Rename.id.var x = x and Rename.comp are definitional, so rfl works
      s"  case ${ctor.name} => rfl\n"
    else
      // Collect per-constructor simp lemmas
      val lemmas = scala.collection.mutable.ListBuffer(s"${sort.name}.rename")
      val hasBinders = ctor.fields.exists(_.binders.nonEmpty)

      val hasBVar = ctor.fields.exists(_.fieldType.isInstanceOf[FieldType.BVarRef])
      val hasVarRef = ctor.fields.exists(_.fieldType.isInstanceOf[FieldType.VarRef])

      // Add dependency lemmas for sorts/vars referenced in THIS constructor
      for f <- ctor.fields do
        f.fieldType match
          case FieldType.SortRef(s, _) if s != sort.name =>
            lemmas += s"$s.$theorem"
          case FieldType.VarRef(_) =>
            lemmas += s"Var.$theorem"
          case _ => ()

      // For BVar fields mixed with non-VarRef sorts, include Rename.id/Rename.comp
      // (safe because VarRef is the only case that conflicts with Rename.id unfolding)
      if hasBVar && !hasVarRef then
        theorem match
          case "rename_id" => lemmas += "Rename.id"
          case "rename_comp" => lemmas += "Rename.comp"

      // For binders
      if hasBinders then
        theorem match
          case "rename_id" => lemmas += "Rename.lift_id"
          case "rename_comp" => lemmas += "Rename.lift_comp"

      val uniqueLemmas = lemmas.distinct.toList
      // If there are both BVar and VarRef fields in the same constructor,
      // simp_all may leave BVar goals unsolved; add <;> rfl as fallback
      val fallback = if hasBVar && hasVarRef then "\n    <;> rfl" else ""
      s"  case ${ctor.name} =>\n    simp_all [${uniqueLemmas.mkString(", ")}]$fallback\n"
