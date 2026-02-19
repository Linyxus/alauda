package alauda.gen

import alauda.dsl.*
import java.nio.file.{Files, Path, Paths}

object CodeGen:
  /** Generate all Lean files for the given language spec. */
  def generate(spec: LangSpec, outputDir: String): Unit =
    val outPath = Paths.get(outputDir)
    Files.createDirectories(outPath)

    // Generate Debruijn.lean
    val debruijnContent = DebruijnGen.generate(spec)
    writeFile(outPath.resolve("Debruijn.lean"), debruijnContent)
    println(s"Generated Debruijn.lean")

    // Topologically sort the sorts by dependency
    val sortOrder = topoSort(spec)

    // Generate per-sort syntax files
    val syntaxDir = outPath.resolve("Syntax")
    Files.createDirectories(syntaxDir)

    // Build the module prefix from outputDir
    // e.g. "Autosubst4Lean/Test" -> "Autosubst4Lean.Test"
    val modulePrefix = outputDir.replace("/", ".").replace("\\", ".")

    for (sortDef, idx) <- sortOrder.zipWithIndex do
      val depImports = computeImports(spec, sortDef, sortOrder.take(idx), modulePrefix)
      val content = SyntaxGen.generate(spec, sortDef, depImports)
      writeFile(syntaxDir.resolve(s"${sortDef.name}.lean"), content)
      println(s"Generated Syntax/${sortDef.name}.lean")

    // Generate Syntax.lean umbrella import
    val syntaxUmbrella = sortOrder.map(s => s"import $modulePrefix.Syntax.${s.name}").mkString("\n") + "\n"
    writeFile(outPath.resolve("Syntax.lean"), syntaxUmbrella)
    println(s"Generated Syntax.lean")

    // Generate Substitution.lean if any kind has a substImage
    if spec.kinds.exists(_.substImage.isDefined) then
      val substContent = SubstitutionGen.generate(spec, modulePrefix)
      writeFile(outPath.resolve("Substitution.lean"), substContent)
      println(s"Generated Substitution.lean")

  /** Compute imports for a sort file. */
  private def computeImports(spec: LangSpec, sort: SortDef, priorSorts: List[SortDef], modulePrefix: String): List[String] =
    val deps = sortDependencies(spec, sort)
    // Always need Debruijn
    val debruijnImport = s"$modulePrefix.Debruijn"
    val sortImports = priorSorts.filter(s => deps.contains(s.name)).map(s => s"$modulePrefix.Syntax.${s.name}")
    debruijnImport :: sortImports

  /** Get the names of sorts that this sort depends on. */
  private def sortDependencies(spec: LangSpec, sort: SortDef): Set[String] =
    sort.constructors.flatMap(_.fields).flatMap { f =>
      f.fieldType match
        case FieldType.SortRef(s, _) if s != sort.name => Some(s)
        case FieldType.VarRef(_) => Some("Var")
        case _ => None
    }.toSet

  /** Topological sort of sorts by dependency. */
  private def topoSort(spec: LangSpec): List[SortDef] =
    val sortMap = spec.sorts.map(s => s.name -> s).toMap
    var visited = Set.empty[String]
    var result = List.empty[SortDef]

    def visit(name: String): Unit =
      if !visited.contains(name) && sortMap.contains(name) then
        visited += name
        val s = sortMap(name)
        for dep <- sortDependencies(spec, s) do
          visit(dep)
        result = result :+ s

    for s <- spec.sorts do
      visit(s.name)

    result

  private def writeFile(path: Path, content: String): Unit =
    Files.writeString(path, content)
