This is a project that automatically generate Lean 4 definitions for programming languages.

The target Lean 4 definition for programming languages is based on intrinsically-scoped de Bruijn indices.

This is both a Scala and a Lean 4 project. The Scala part is for the code generation logic. The Lean 4 part is for experimenting with the generated Lean 4 code.

`Autosubst4Lean/Example` contains an example project. It exemplifies the style of Lean 4 definitions that is to be generated.

Use `sbt` to run and test Scala code. When testing the logic, generate Lean 4 code in the `Autosubst4Lean/Test` directory. Compile Lean 4 code with the `lean4check` tool.

