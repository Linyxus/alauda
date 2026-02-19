# autosubst4lean

A code generator that produces Lean 4 definitions for programming language syntax based on intrinsically-scoped de Bruijn indices. Given a description of variable kinds and syntax sorts in a small DSL, it generates:

- De Bruijn index infrastructure (`Kind`, `Sig`, `BVar`, `Rename` with algebraic properties)
- Inductive type definitions for each syntax sort
- Renaming functions with `rename_id` and `rename_comp` theorems

## Usage

```
sbt "run <input-file> <output-dir>"
```

For example:

```
sbt "run test/cc.autosubst Autosubst4Lean/Test"
```

This reads the DSL file, generates Lean 4 source files in the output directory, and the generated code can be compiled with `lake build`.

## DSL Reference

The input DSL uses a Lean-like syntax. A file consists of the following sections, in order:

### Namespace

```
namespace <Name>
```

Declares the Lean 4 namespace that wraps all generated definitions.

### Variable Kinds

```
kinds:
  <name> "<postfix>"
  ...
```

Each line declares a kind of variable. The name becomes a constructor of the generated `Kind` inductive. The postfix string is used in signature extension notation (e.g., `postfix:80 ",x" => Sig.extend_var`).

### Enums (optional)

```
enum <Name> := <variant> | <variant> | ...
```

Declares an inductive enum type used to index syntax sorts. For example, `TySort` can index types into shape types, capturing types, etc.

### Inductive Sorts

```
inductive <Name> : <indices> -> Sig -> Type
| <ctor> : <field> -> ... -> <ReturnType>
| <ctor> : <ReturnType>
...
```

Each sort is an inductive type indexed by `Sig` (and optionally by an enum or `Kind`). Constructors list their fields separated by `->`, followed by the return type.

#### Field Types

| Syntax | Meaning | Rename behavior |
|---|---|---|
| `BVar s .kind` | Bound variable of a specific kind | `f.var x` |
| `BVar s k` | Bound variable with sort's kind index | `f.var x` |
| `Var .kind s` | Variable (bound or free) of a specific kind | `x.rename f` |
| `SortName s` | Reference to another syntax sort | `x.rename f` |
| `SortName .idx s` | Reference to an indexed sort at a specific index | `x.rename f` |
| `Nat`, etc. | Plain type, not involving bound variables | passed through unchanged |

#### Binders

When a field's signature position is `(s,x)` instead of `s`, it means the field lives under a binder that introduces a variable of the kind whose postfix is `x`. The renaming for that field uses `f.lift` to go under the binder.

Nested binders are written as `((s,C),x)`, meaning two binders: first kind `C`, then kind `x`. The renaming uses `f.lift.lift`.

#### Return Types

The return type specifies the sort name, an optional index (e.g., `.shape`), and the signature `s`:

```
| top : Ty .shape s        -- Ty indexed at .shape, no binders
| arrow : ... -> Ty .shape s
| exi : ... -> Ty .exi s   -- Ty indexed at .exi
| var : ... -> Exp s        -- Exp, no index
```

## Examples

### Simply-Typed Lambda Calculus

A minimal example with a single variable kind:

```
namespace STLC

kinds:
  var "x"

inductive Ty : Sig -> Type
| base : Ty s
| arrow : Ty s -> Ty s -> Ty s

inductive Exp : Sig -> Type
| var : BVar s .var -> Exp s
| abs : Ty s -> Exp (s,x) -> Exp s
| app : Exp s -> Exp s -> Exp s
```

This generates:

- `Kind` with a single constructor `var`
- `Sig` with extension `,x`
- `Ty` with `rename` (trivially passes through since `Ty` has no bound variable references), `rename_id`, `rename_comp`
- `Exp` with `rename` that lifts under the `abs` binder, plus `rename_id` and `rename_comp`

### System F

An example with term and type variables:

```
namespace SystemF

kinds:
  var "x"
  tvar "X"

inductive Ty : Sig -> Type
| tvar : BVar s .tvar -> Ty s
| arrow : Ty s -> Ty s -> Ty s
| forall_ : Ty (s,X) -> Ty s

inductive Exp : Sig -> Type
| var : BVar s .var -> Exp s
| abs : Ty s -> Exp (s,x) -> Exp s
| app : Exp s -> Exp s -> Exp s
| tabs : Exp (s,X) -> Exp s
| tapp : Exp s -> Ty s -> Exp s
```

Here `Ty` has a bound type variable reference (`tvar`) and a type-level binder (`forall_` binds `X`). `Exp` has both term-level binders (`abs` binds `x`) and type-level binders (`tabs` binds `X`).

### CC (Capture Calculus)

A full example with term variables, type variables, and capture variables. See `test/cc.autosubst` for the complete definition and `Autosubst4Lean/Example/` for the expected output style.

## Generated Output

For a language with namespace `NS` and sorts `A`, `B`, `C`, the generator produces:

```
<output-dir>/
  Debruijn.lean         -- Kind, Sig, BVar, Rename + theorems
  Syntax/
    A.lean              -- inductive A, A.rename, A.rename_id, A.rename_comp
    B.lean
    C.lean
  Syntax.lean           -- umbrella import for all syntax files
```

Sorts are topologically sorted by dependency so that imports are correct.

## Project Structure

```
src/main/scala/
  autosubst/
    dsl/
      Model.scala       -- DSL AST types (LangSpec, SortDef, Constructor, FieldType, ...)
      Parser.scala       -- Text parser (Lean-like syntax -> Model AST)
    gen/
      DebruijnGen.scala  -- Generates Debruijn.lean
      SyntaxGen.scala    -- Generates per-sort syntax files
      CodeGen.scala      -- Orchestrator: topo-sort, file writing
  Main.scala             -- Entry point
```
