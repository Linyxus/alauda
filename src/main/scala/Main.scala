import alauda.dsl.Parser
import alauda.gen.CodeGen
import java.nio.file.{Files, Paths}

@main def main(inputFile: String, outputDir: String): Unit =
  val source = Files.readString(Paths.get(inputFile))
  val spec = Parser.parse(source)
  println(s"Parsed language spec: ${spec.name}")
  println(s"  Kinds: ${spec.kinds.map(_.name).mkString(", ")}")
  println(s"  Enums: ${spec.enums.map(_.name).mkString(", ")}")
  println(s"  Sorts: ${spec.sorts.map(_.name).mkString(", ")}")
  CodeGen.generate(spec, outputDir)
  println("Done!")
