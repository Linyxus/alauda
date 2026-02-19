package autosubst.gen

import autosubst.dsl.*

object SubstitutionGen:

  /** Generate the full Substitution.lean content. */
  def generate(spec: LangSpec, modulePrefix: String): String =
    val ns = spec.name
    val sb = new StringBuilder
    val kindsWithSubst = spec.kinds.filter(_.substImage.isDefined)
    val sortOrder = topoSortForSubst(spec)
    val sortsWithSubst = sortOrder.filter(s => hasSubst(spec, s))

    sb ++= s"import $modulePrefix.Syntax\n\n"
    sb ++= s"namespace $ns\n\n"

    // 1. Subst structure
    sb ++= genSubstStructure(spec, kindsWithSubst)
    sb ++= "\n"

    // 2-4. lift, liftMany, id
    sb ++= genSubstLift(spec, kindsWithSubst)
    sb ++= "\n"
    sb ++= genSubstLiftMany(spec)
    sb ++= "\n"
    sb ++= genSubstId(spec, kindsWithSubst)
    sb ++= "\n"

    // 5. Per-sort .subst
    for sort <- sortsWithSubst do
      sb ++= genSortSubst(spec, sort, kindsWithSubst)
      sb ++= "\n"

    // 6. funext
    sb ++= genFunext(spec, kindsWithSubst)
    sb ++= "\n"

    // 7. comp
    sb ++= genSubstComp(spec, kindsWithSubst)
    sb ++= "\n"

    // 8. Subst.lift_there_*_eq
    for kind <- kindsWithSubst do
      sb ++= genSubstLiftThereEq(spec, kind)
      sb ++= "\n"

    // 9. Rename.lift_there_*_eq
    for kind <- kindsWithSubst do
      sb ++= genRenameLiftThereEq(spec, kind)
      sb ++= "\n"

    // 10. Sort.weaken_rename_comm (per subst image sort)
    val imageSorts = kindsWithSubst.map(_.substImage.get.sortName).distinct
    for sortName <- imageSorts do
      val sort = spec.sorts.find(_.name == sortName).get
      sb ++= genWeakenRenameComm(spec, sort)
      sb ++= "\n"

    // 11. Kind.weaken_subst_comm_liftMany (BVar-level, per kind)
    for kind <- kindsWithSubst do
      sb ++= genBVarWeakenLiftMany(spec, kind)
      sb ++= "\n"

    // 12-13. Sort.weaken_subst_comm + _base (per sort with .subst)
    for sort <- sortsWithSubst do
      sb ++= genSortWeakenSubstComm(spec, sort, kindsWithSubst)
      sb ++= "\n"
      sb ++= genSortWeakenSubstCommBase(spec, sort)
      sb ++= "\n"

    // 14. comp_lift
    sb ++= genCompLift(spec, kindsWithSubst)
    sb ++= "\n"

    // 15. comp_liftMany
    sb ++= genCompLiftMany(spec)
    sb ++= "\n"

    // 16. Per-sort subst_comp
    for sort <- sortsWithSubst do
      sb ++= genSortSubstComp(spec, sort, kindsWithSubst)
      sb ++= "\n"

    // 17. lift_id
    sb ++= genLiftId(spec, kindsWithSubst)
    sb ++= "\n"

    // 18. Per-sort subst_id
    for sort <- sortsWithSubst do
      sb ++= genSortSubstId(spec, sort, kindsWithSubst)
      sb ++= "\n"

    sb ++= s"end $ns\n"
    sb.toString

  // ===== Helpers =====

  private def hasSubst(spec: LangSpec, sort: SortDef): Boolean =
    sort.constructors.exists(c =>
      c.fields.exists(f => f.fieldType match
        case FieldType.BVarRef(kind) => spec.kinds.exists(k => k.name == kind && k.substImage.isDefined)
        case FieldType.SortRef(_, _) => true
        case FieldType.VarRef(_) => true
        case FieldType.Plain(_) => false
      )
    )

  /** Find the constructor in the image sort that is the "variable constructor" for this kind. */
  private def findVarCtor(spec: LangSpec, kind: VarKind): (String, String) =
    val img = kind.substImage.get
    val sort = spec.sorts.find(_.name == img.sortName).getOrElse(
      throw new RuntimeException(s"Substitution image sort ${img.sortName} not found")
    )
    val ctor = sort.constructors.find { c =>
      c.fields.length == 1 &&
      c.fields.head.binders.isEmpty &&
      (c.fields.head.fieldType match
        case FieldType.BVarRef(k) => k == kind.name
        case _ => false
      ) &&
      c.resultIndex == img.index
    }.getOrElse(
      throw new RuntimeException(s"No variable constructor found for kind ${kind.name} in sort ${img.sortName}")
    )
    (img.sortName, ctor.name)

  /** Whether this constructor is a "variable constructor" (single BVarRef of a kind with substImage). */
  private def isVarCtor(spec: LangSpec, ctor: Constructor): Option[VarKind] =
    if ctor.fields.length == 1 && ctor.fields.head.binders.isEmpty then
      ctor.fields.head.fieldType match
        case FieldType.BVarRef(kindName) =>
          spec.kinds.find(k => k.name == kindName && k.substImage.isDefined)
        case _ => None
    else None

  private def imageTypeStr(kind: VarKind, sigVar: String = "s2"): String =
    val img = kind.substImage.get
    val idxStr = img.index.map(i => s" .$i").getOrElse("")
    s"${img.sortName}$idxStr $sigVar"

  /** Capitalize kind name: "var" -> "Var", "tvar" -> "TVar" */
  private def capitalizeKind(kind: VarKind): String =
    kind.name.take(1).toUpperCase + kind.name.drop(1)

  private def sortParamStr(sort: SortDef): String =
    sort.index match
      case Some("Kind") => " {k : Kind}"
      case Some(idx) =>
        val lc = idx.take(1).toLowerCase + idx.drop(1)
        s" {$lc : $idx}"
      case None => ""

  private def indexVarStr(sort: SortDef): String =
    sort.index match
      case Some("Kind") => " k"
      case Some(idx) =>
        val lc = idx.take(1).toLowerCase + idx.drop(1)
        s" $lc"
      case None => ""

  private def topoSortForSubst(spec: LangSpec): List[SortDef] =
    val sortMap = spec.sorts.map(s => s.name -> s).toMap
    var visited = Set.empty[String]
    var result = List.empty[SortDef]

    def sortDeps(sort: SortDef): Set[String] =
      sort.constructors.flatMap(_.fields).flatMap { f =>
        f.fieldType match
          case FieldType.SortRef(s, _) if s != sort.name => Some(s)
          case FieldType.VarRef(_) => Some("Var")
          case _ => None
      }.toSet

    def visit(name: String): Unit =
      if !visited.contains(name) && sortMap.contains(name) then
        visited += name
        val s = sortMap(name)
        for dep <- sortDeps(s) do visit(dep)
        result = result :+ s

    for s <- spec.sorts do visit(s.name)
    result

  // ===== 1. Subst structure =====

  private def genSubstStructure(spec: LangSpec, kinds: List[VarKind]): String =
    val sb = new StringBuilder
    sb ++= "structure Subst (s1 s2 : Sig) where\n"
    for kind <- kinds do
      sb ++= s"  ${kind.name} : BVar s1 .${kind.name} -> ${imageTypeStr(kind)}\n"
    sb.toString

  // ===== 2. Subst.lift =====

  private def genSubstLift(spec: LangSpec, kinds: List[VarKind]): String =
    val sb = new StringBuilder
    sb ++= "def Subst.lift (σ : Subst s1 s2) : Subst (s1,,k) (s2,,k) where\n"
    for kind <- kinds do
      val (_, ctorName) = findVarCtor(spec, kind)
      sb ++= s"  ${kind.name} := fun x => by\n"
      sb ++= s"    cases x\n"
      sb ++= s"    case here => exact .$ctorName .here\n"
      sb ++= s"    case there x => exact (σ.${kind.name} x).rename Rename.succ\n"
    sb.toString

  // ===== 3. Subst.liftMany =====

  private def genSubstLiftMany(spec: LangSpec): String =
    "def Subst.liftMany (σ : Subst s1 s2) (K : Sig) : Subst (s1 ++ K) (s2 ++ K) :=\n" +
    "  match K with\n" +
    "  | [] => σ\n" +
    "  | k :: K => (σ.liftMany K).lift (k:=k)\n"

  // ===== 4. Subst.id =====

  private def genSubstId(spec: LangSpec, kinds: List[VarKind]): String =
    val sb = new StringBuilder
    sb ++= "def Subst.id {s : Sig} : Subst s s where\n"
    for kind <- kinds do
      val (_, ctorName) = findVarCtor(spec, kind)
      sb ++= s"  ${kind.name} := fun x => .$ctorName x\n"
    sb.toString

  // ===== 5. Per-sort .subst =====

  private def genSortSubst(spec: LangSpec, sort: SortDef, kindsWithSubst: List[VarKind]): String =
    val sb = new StringBuilder
    val sp = sortParamStr(sort)
    val iv = indexVarStr(sort)

    sb ++= s"def ${sort.name}.subst$sp : ${sort.name}$iv s1 -> Subst s1 s2 -> ${sort.name}$iv s2\n"

    for ctor <- sort.constructors do
      isVarCtor(spec, ctor) match
        case Some(kind) =>
          // Variable constructor: return substitution directly
          sb ++= s"| .${ctor.name} x0, σ => σ.${kind.name} x0\n"
        case None =>
          if ctor.fields.isEmpty then
            sb ++= s"| .${ctor.name}, _ => .${ctor.name}\n"
          else
            val allPlain = ctor.fields.forall(_.fieldType.isInstanceOf[FieldType.Plain])
            if allPlain then
              val vars = ctor.fields.indices.map(j => s"a$j").mkString(" ")
              sb ++= s"| .${ctor.name} $vars, _ => .${ctor.name} $vars\n"
            else
              val fieldNames = ctor.fields.zipWithIndex.map { (f, j) => substFieldVarName(f, j) }
              val substExprs = ctor.fields.zipWithIndex.map { (f, j) =>
                substFieldExpr(spec, f, j, kindsWithSubst)
              }
              sb ++= s"| .${ctor.name} ${fieldNames.mkString(" ")}, σ => .${ctor.name} ${substExprs.mkString(" ")}\n"

    sb.toString

  private def substFieldVarName(field: Field, idx: Int): String =
    field.fieldType match
      case FieldType.BVarRef(_) => s"x$idx"
      case FieldType.SortRef(_, _) => s"a$idx"
      case FieldType.VarRef(_) => s"x$idx"
      case FieldType.Plain(_) => s"p$idx"

  private def substFieldExpr(spec: LangSpec, field: Field, idx: Int, kindsWithSubst: List[VarKind]): String =
    val name = substFieldVarName(field, idx)
    val liftedSigma = field.binders.foldLeft("σ") { (acc, _) => s"$acc.lift" }
    field.fieldType match
      case FieldType.BVarRef(kindName) =>
        if kindsWithSubst.exists(_.name == kindName) then
          s"($liftedSigma.$kindName $name)"
        else
          // Kind without substImage: pass through unchanged
          name
      case FieldType.SortRef(_, _) =>
        s"($name.subst $liftedSigma)"
      case FieldType.VarRef(_) =>
        s"($name.subst $liftedSigma)"
      case FieldType.Plain(_) =>
        name

  // ===== 6. Subst.funext =====

  private def genFunext(spec: LangSpec, kinds: List[VarKind]): String =
    val sb = new StringBuilder
    sb ++= "theorem Subst.funext {σ1 σ2 : Subst s1 s2}\n"
    for kind <- kinds do
      sb ++= s"  (h${kind.name} : ∀ x, σ1.${kind.name} x = σ2.${kind.name} x)\n"
    sb ++= "  : σ1 = σ2 := by\n"
    sb ++= "  cases σ1; cases σ2\n"
    sb ++= "  simp only [Subst.mk.injEq]\n"
    if kinds.length == 1 then
      sb ++= s"  funext x; exact h${kinds.head.name} x\n"
    else
      for (kind, i) <- kinds.zipWithIndex do
        if i < kinds.length - 1 then
          sb ++= "  constructor\n"
          sb ++= s"  · funext x; exact h${kind.name} x\n"
        else
          sb ++= s"  · funext x; exact h${kind.name} x\n"
    sb.toString

  // ===== 7. Subst.comp =====

  private def genSubstComp(spec: LangSpec, kinds: List[VarKind]): String =
    val sb = new StringBuilder
    sb ++= "def Subst.comp (σ1 : Subst s1 s2) (σ2 : Subst s2 s3) : Subst s1 s3 where\n"
    for kind <- kinds do
      sb ++= s"  ${kind.name} := fun x => (σ1.${kind.name} x).subst σ2\n"
    sb.toString

  // ===== 8. Subst.lift_there_*_eq =====

  private def genSubstLiftThereEq(spec: LangSpec, kind: VarKind): String =
    s"theorem Subst.lift_there_${kind.name}_eq {σ : Subst s1 s2} {x : BVar s1 .${kind.name}} :\n" +
    s"  (σ.lift (k:=k)).${kind.name} (.there x) = (σ.${kind.name} x).rename Rename.succ := by\n" +
    s"  rfl\n"

  // ===== 9. Rename.lift_there_*_eq =====

  private def genRenameLiftThereEq(spec: LangSpec, kind: VarKind): String =
    s"theorem Rename.lift_there_${kind.name}_eq {f : Rename s1 s2} {x : BVar s1 .${kind.name}} :\n" +
    s"  (f.lift (k:=k)).var (.there x) = (f.var x).there := by\n" +
    s"  rfl\n"

  // ===== 10. Sort.weaken_rename_comm =====

  private def genWeakenRenameComm(spec: LangSpec, sort: SortDef): String =
    val sp = sortParamStr(sort)
    val iv = indexVarStr(sort)
    s"theorem ${sort.name}.weaken_rename_comm$sp {t : ${sort.name}$iv s1} {f : Rename s1 s2} :\n" +
    s"  (t.rename Rename.succ).rename (f.lift (k:=k0)) = (t.rename f).rename (Rename.succ) := by\n" +
    s"  simp [${sort.name}.rename_comp, Rename.succ_lift_comm]\n"

  // ===== 11. Kind.weaken_subst_comm_liftMany (BVar-level) =====

  private def genBVarWeakenLiftMany(spec: LangSpec, kind: VarKind): String =
    val cap = capitalizeKind(kind)
    val img = kind.substImage.get
    val sb = new StringBuilder
    sb ++= s"theorem $cap.weaken_subst_comm_liftMany {x : BVar (s1 ++ K) .${kind.name}} {σ : Subst s1 s2} :\n"
    sb ++= s"  ((σ.liftMany K).${kind.name} x).rename ((Rename.succ (k:=k0)).liftMany K) =\n"
    sb ++= s"  (σ.lift (k:=k0).liftMany K).${kind.name} (((Rename.succ (k:=k0)).liftMany K).var x) := by\n"
    sb ++= s"  induction K with\n"
    sb ++= s"  | nil =>\n"
    sb ++= s"    simp [Subst.liftMany, Rename.liftMany]\n"
    sb ++= s"    cases x with\n"
    sb ++= s"    | here => simp [Subst.lift, Rename.succ]\n"
    sb ++= s"    | there x => rfl\n"
    sb ++= s"  | cons k K ih =>\n"
    sb ++= s"    simp [Subst.liftMany, Rename.liftMany]\n"
    sb ++= s"    cases x with\n"
    sb ++= s"    | here => rfl\n"
    sb ++= s"    | there x =>\n"
    sb ++= s"      simp [Rename.lift_there_${kind.name}_eq]\n"
    sb ++= s"      simp [Subst.lift_there_${kind.name}_eq]\n"
    sb ++= s"      simp [${img.sortName}.weaken_rename_comm]\n"
    sb ++= s"      grind\n"
    sb.toString

  // ===== 12. Sort.weaken_subst_comm (liftMany version) =====

  private def genSortWeakenSubstComm(spec: LangSpec, sort: SortDef, kindsWithSubst: List[VarKind]): String =
    val sb = new StringBuilder
    val sp = sortParamStr(sort)
    val iv = indexVarStr(sort)

    sb ++= s"theorem ${sort.name}.weaken_subst_comm$sp {t : ${sort.name}$iv (s1 ++ K)} {σ : Subst s1 s2} :\n"
    sb ++= s"  (t.subst (σ.liftMany K)).rename ((Rename.succ (k:=k0)).liftMany K) =\n"
    sb ++= s"  (t.rename ((Rename.succ (k:=k0)).liftMany K)).subst (σ.lift (k:=k0).liftMany K) := by\n"
    sb ++= s"  match t with\n"

    for ctor <- sort.constructors do
      sb ++= genWeakenSubstCommCase(spec, sort, ctor, kindsWithSubst)

    sb.toString

  private def genWeakenSubstCommCase(spec: LangSpec, sort: SortDef, ctor: Constructor, kindsWithSubst: List[VarKind]): String =
    val sb = new StringBuilder

    // Check if this is a variable constructor
    isVarCtor(spec, ctor) match
      case Some(kind) =>
        val cap = capitalizeKind(kind)
        sb ++= s"  | .${ctor.name} x =>\n"
        sb ++= s"    simp [${sort.name}.subst, ${sort.name}.rename]\n"
        sb ++= s"    exact $cap.weaken_subst_comm_liftMany\n"
        return sb.toString
      case None => ()

    if ctor.fields.isEmpty || ctor.fields.forall(_.fieldType.isInstanceOf[FieldType.Plain]) then
      sb ++= s"  | .${ctor.name}${if ctor.fields.nonEmpty then " " + ctor.fields.indices.map(_ => "_").mkString(" ") else ""} => rfl\n"
      return sb.toString

    // Collect fields that need IHs (SortRef and VarRef)
    val sortRefFields = ctor.fields.zipWithIndex.filter { (f, _) =>
      f.fieldType match
        case FieldType.SortRef(_, _) => true
        case FieldType.VarRef(_) => true
        case _ => false
    }

    // Generate pattern with field names
    val fieldPatterns = ctor.fields.zipWithIndex.map { (f, j) =>
      f.fieldType match
        case FieldType.SortRef(_, _) | FieldType.VarRef(_) => s"f$j"
        case _ => "_"
    }
    sb ++= s"  | .${ctor.name} ${fieldPatterns.mkString(" ")} =>\n"

    // Generate have statements for each sort-ref field
    for (f, j) <- sortRefFields do
      val sortName = f.fieldType match
        case FieldType.SortRef(s, _) => s
        case FieldType.VarRef(_) => "Var"
        case _ => ???
      val kExtended = f.binders.foldLeft("K") { (acc, binder) => s"$acc,$binder" }
      sb ++= s"    have ih$j := ${sortName}.weaken_subst_comm (t:=f$j) (σ:=σ) (K:=$kExtended) (k0:=k0)\n"

    // Determine which fields have binders
    val fieldsWithBinders = sortRefFields.filter(_._1.binders.nonEmpty)
    val fieldsWithoutBinders = sortRefFields.filter(_._1.binders.isEmpty)

    if fieldsWithBinders.isEmpty then
      // All without binders: simp with all IHs
      val ihNames = sortRefFields.map((_, j) => s"ih$j")
      sb ++= s"    simp [${sort.name}.subst, ${sort.name}.rename, ${ihNames.mkString(", ")}]\n"
    else if fieldsWithBinders.length == 1 then
      // One binder field: simp with non-binder IHs, exact the binder one
      val nonBinderIhs = fieldsWithoutBinders.map((_, j) => s"ih$j")
      val binderIh = fieldsWithBinders.head._2
      val simpLemmas = List(s"${sort.name}.subst", s"${sort.name}.rename") ++ nonBinderIhs
      sb ++= s"    simp [${simpLemmas.mkString(", ")}]\n"
      sb ++= s"    exact ih$binderIh\n"
    else
      // Multiple binder fields: simp with all IHs (hope for the best)
      val ihNames = sortRefFields.map((_, j) => s"ih$j")
      sb ++= s"    simp [${sort.name}.subst, ${sort.name}.rename, ${ihNames.mkString(", ")}]\n"

    sb.toString

  // ===== 13. Sort.weaken_subst_comm_base =====

  private def genSortWeakenSubstCommBase(spec: LangSpec, sort: SortDef): String =
    val sp = sortParamStr(sort)
    val iv = indexVarStr(sort)
    s"theorem ${sort.name}.weaken_subst_comm_base$sp {t : ${sort.name}$iv s1} {σ : Subst s1 s2} :\n" +
    s"  (t.subst σ).rename (Rename.succ (k:=k0)) = (t.rename Rename.succ).subst (σ.lift (k:=k0)) :=\n" +
    s"  ${sort.name}.weaken_subst_comm (K:=[])\n"

  // ===== 14. Subst.comp_lift =====

  private def genCompLift(spec: LangSpec, kinds: List[VarKind]): String =
    val sb = new StringBuilder
    sb ++= "theorem Subst.comp_lift {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} {k : Kind} :\n"
    sb ++= "  (σ1.lift (k := k)).comp (σ2.lift (k := k)) = (σ1.comp σ2).lift (k := k) := by\n"
    sb ++= "  apply Subst.funext\n"
    for kind <- kinds do
      val img = kind.substImage.get
      sb ++= s"  · intro x\n"
      sb ++= s"    cases x with\n"
      sb ++= s"    | here => rfl\n"
      sb ++= s"    | there x0 =>\n"
      sb ++= s"      conv =>\n"
      sb ++= s"        lhs; simp only [Subst.comp, Subst.lift_there_${kind.name}_eq]\n"
      sb ++= s"      simp only [Subst.lift_there_${kind.name}_eq]\n"
      sb ++= s"      simp only [${img.sortName}.weaken_subst_comm_base, Subst.comp]\n"
    sb.toString

  // ===== 15. Subst.comp_liftMany =====

  private def genCompLiftMany(spec: LangSpec): String =
    "theorem Subst.comp_liftMany {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} {K : Sig} :\n" +
    "  (σ1.liftMany K).comp (σ2.liftMany K) = (σ1.comp σ2).liftMany K := by\n" +
    "  induction K with\n" +
    "  | nil => rfl\n" +
    "  | cons k K ih =>\n" +
    "    simp [Subst.liftMany]\n" +
    "    rw [Subst.comp_lift, ih]\n"

  // ===== 16. Per-sort subst_comp =====

  private def genSortSubstComp(spec: LangSpec, sort: SortDef, kindsWithSubst: List[VarKind]): String =
    val sb = new StringBuilder
    val sp = sortParamStr(sort)
    val iv = indexVarStr(sort)

    sb ++= s"theorem ${sort.name}.subst_comp$sp {t : ${sort.name}$iv s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :\n"
    sb ++= s"  (t.subst σ1).subst σ2 = t.subst (σ1.comp σ2) := by\n"
    sb ++= s"  induction t generalizing s2 s3 with\n"

    for ctor <- sort.constructors do
      sb ++= genSubstCompCase(spec, sort, ctor, kindsWithSubst)

    sb.toString

  private def genSubstCompCase(spec: LangSpec, sort: SortDef, ctor: Constructor, kindsWithSubst: List[VarKind]): String =
    if ctor.fields.isEmpty || ctor.fields.forall(_.fieldType.isInstanceOf[FieldType.Plain]) then
      return s"  | ${ctor.name} => rfl\n"

    // Variable constructor
    isVarCtor(spec, ctor) match
      case Some(kind) =>
        return s"  | ${ctor.name} => simp [${sort.name}.subst, Subst.comp]\n"
      case None => ()

    val onlyBVarAndPlain = ctor.fields.forall(f => f.fieldType match
      case FieldType.BVarRef(_) | FieldType.Plain(_) => true
      case _ => false
    )
    if onlyBVarAndPlain then
      return s"  | ${ctor.name} => simp [${sort.name}.subst, Subst.comp]\n"

    // Collect simp lemmas
    val lemmas = scala.collection.mutable.ListBuffer(s"${sort.name}.subst")
    val hasBinders = ctor.fields.exists(_.binders.nonEmpty)

    for f <- ctor.fields do
      f.fieldType match
        case FieldType.SortRef(s, _) if s != sort.name =>
          lemmas += s"$s.subst_comp"
        case FieldType.VarRef(_) =>
          lemmas += "Var.subst_comp"
        case FieldType.BVarRef(k) if kindsWithSubst.exists(_.name == k) =>
          lemmas += "Subst.comp"
        case _ => ()

    if hasBinders then
      lemmas += "Subst.comp_lift"

    val uniqueLemmas = lemmas.distinct.toList

    // Count IHs: only for fields of the SAME sort (self-referencing)
    val ihCount = ctor.fields.count(f => f.fieldType match
      case FieldType.SortRef(s, _) if s == sort.name => true
      case _ => false
    )
    val ihNames = (0 until ihCount).map(i => s"ih$i").mkString(" ")
    val ihPrefix = if ihNames.nonEmpty then s" $ihNames" else ""

    // Also count non-self sort refs (they don't get IHs from induction, but we list _ for them)
    // Actually, induction only generates IHs for recursive occurrences of the same type
    s"  | ${ctor.name}$ihPrefix =>\n    simp [${uniqueLemmas.mkString(", ")}]\n"

  // ===== 17. Subst.lift_id =====

  private def genLiftId(spec: LangSpec, kinds: List[VarKind]): String =
    val sb = new StringBuilder
    sb ++= "theorem Subst.lift_id :\n"
    sb ++= "  (Subst.id (s:=s)).lift (k:=k) = Subst.id := by\n"
    sb ++= "  apply Subst.funext\n"
    for kind <- kinds do
      sb ++= s"  · intro x\n"
      sb ++= s"    cases x <;> rfl\n"
    sb.toString

  // ===== 18. Per-sort subst_id =====

  private def genSortSubstId(spec: LangSpec, sort: SortDef, kindsWithSubst: List[VarKind]): String =
    val sb = new StringBuilder
    val sp = sortParamStr(sort)
    val iv = indexVarStr(sort)

    sb ++= s"theorem ${sort.name}.subst_id$sp {t : ${sort.name}$iv s} :\n"
    sb ++= s"  t.subst Subst.id = t := by\n"
    sb ++= s"  induction t with\n"

    for ctor <- sort.constructors do
      sb ++= genSubstIdCase(spec, sort, ctor, kindsWithSubst)

    sb.toString

  private def genSubstIdCase(spec: LangSpec, sort: SortDef, ctor: Constructor, kindsWithSubst: List[VarKind]): String =
    if ctor.fields.isEmpty || ctor.fields.forall(_.fieldType.isInstanceOf[FieldType.Plain]) then
      return s"  | ${ctor.name} => rfl\n"

    isVarCtor(spec, ctor) match
      case Some(kind) =>
        return s"  | ${ctor.name} => simp [${sort.name}.subst, Subst.id]\n"
      case None => ()

    val onlyBVarAndPlain = ctor.fields.forall(f => f.fieldType match
      case FieldType.BVarRef(_) | FieldType.Plain(_) => true
      case _ => false
    )
    if onlyBVarAndPlain then
      return s"  | ${ctor.name} => simp [${sort.name}.subst, Subst.id]\n"

    val lemmas = scala.collection.mutable.ListBuffer(s"${sort.name}.subst")
    val hasBinders = ctor.fields.exists(_.binders.nonEmpty)

    for f <- ctor.fields do
      f.fieldType match
        case FieldType.SortRef(s, _) if s != sort.name =>
          lemmas += s"$s.subst_id"
        case FieldType.VarRef(_) =>
          lemmas += "Var.subst_id"
        case FieldType.BVarRef(k) if kindsWithSubst.exists(_.name == k) =>
          lemmas += "Subst.id"
        case _ => ()

    if hasBinders then
      lemmas += "Subst.lift_id"

    val uniqueLemmas = lemmas.distinct.toList

    val ihCount = ctor.fields.count(f => f.fieldType match
      case FieldType.SortRef(s, _) if s == sort.name => true
      case _ => false
    )
    val ihNames = (0 until ihCount).map(i => s"ih$i").mkString(" ")
    val ihPrefix = if ihNames.nonEmpty then s" $ihNames" else ""

    s"  | ${ctor.name}$ihPrefix =>\n    simp [${uniqueLemmas.mkString(", ")}]\n"
