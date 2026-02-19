package alauda.dsl

import scala.util.parsing.combinator.*

object Parser extends RegexParsers:
  // Override to NOT skip newlines (they matter for structure)
  override val whiteSpace = "[ \t]+".r

  def nl: Parser[Unit] = rep1("""\s*\n""".r) ^^^ ()
  def optNl: Parser[Unit] = rep("""\s*\n""".r) ^^^ ()
  def comment: Parser[Unit] = "--[^\n]*".r ^^^ ()
  def lineEnd: Parser[Unit] = opt(comment) ~> nl
  def blankLines: Parser[Unit] = rep(lineEnd) ^^^ ()

  def ident: Parser[String] = "[a-zA-Z_][a-zA-Z0-9_]*".r
  def quotedString: Parser[String] = "\"" ~> "[^\"]+".r <~ "\""

  // ---- Top-level ----

  def langSpec: Parser[LangSpec] =
    blankLines ~> namespaceDef ~ kindsBlock ~ rep(enumDef | inductiveDef) <~ blankLines ^^ {
      case name ~ kinds ~ defs =>
        val enums = defs.collect { case e: EnumDef => e }
        val sorts = defs.collect { case s: SortDef => s }
        LangSpec(name, kinds, enums, sorts)
    }

  def namespaceDef: Parser[String] =
    "namespace" ~> ident <~ lineEnd <~ blankLines

  // ---- Kinds ----

  def kindsBlock: Parser[List[VarKind]] =
    "kinds:" ~> lineEnd ~> rep1(kindLine) <~ blankLines

  def kindLine: Parser[VarKind] =
    ident ~ quotedString ~ opt("=>" ~> ident ~ opt(dotIdent)) <~ lineEnd ^^ {
      case name ~ postfix ~ None => VarKind(name, postfix)
      case name ~ postfix ~ Some(sort ~ idx) => VarKind(name, postfix, Some(SubstImage(sort, idx)))
    }

  // ---- Enums ----

  def enumDef: Parser[EnumDef] =
    ("enum" ~> ident <~ ":=") ~ rep1sep(ident, "|") <~ lineEnd <~ blankLines ^^ {
      case name ~ variants => EnumDef(name, variants)
    }

  // ---- Inductive sorts ----

  def inductiveDef: Parser[SortDef] =
    inductiveHeader ~ rep1(constructorLine) <~ blankLines ^^ {
      case (name, index) ~ ctors => SortDef(name, index, ctors)
    }

  def inductiveHeader: Parser[(String, Option[String])] =
    "inductive" ~> ident ~ (":" ~> sigArrow) <~ lineEnd ^^ {
      case name ~ idx => (name, idx)
    }

  /** Parse `Sig -> Type` or `Kind -> Sig -> Type` or `TySort -> Sig -> Type` etc.
    * Returns the index type name if present (not Sig, not Type). */
  def sigArrow: Parser[Option[String]] =
    rep1sep(ident, "->") ^^ { parts =>
      // parts is e.g. ["Sig", "Type"] or ["Kind", "Sig", "Type"] or ["TySort", "Sig", "Type"]
      val indices = parts.filterNot(p => p == "Sig" || p == "Type")
      indices.lastOption
    }

  def constructorLine: Parser[Constructor] =
    "|" ~> ident ~ opt(":" ~> constructorSig) <~ lineEnd ^^ {
      case name ~ None => Constructor(name)
      case name ~ Some((fields, resultIdx)) => Constructor(name, fields, resultIdx)
    }

  def constructorSig: Parser[(List[Field], Option[String])] =
    rep(fieldType <~ "->") ~ resultType ^^ {
      case fields ~ resultIdx => (fields, resultIdx)
    }

  // ---- Field types ----

  def fieldType: Parser[Field] =
    bvarField | varField | sortField | plainField

  def bvarField: Parser[Field] =
    "BVar" ~> sigExpr ~ kindRef ^^ {
      case binders ~ kind => Field(FieldType.BVarRef(kind), binders)
    }

  def varField: Parser[Field] =
    "Var" ~> kindRef ~ sigExpr ^^ {
      case kind ~ binders => Field(FieldType.VarRef(kind), binders)
    }

  /** Parse a kind reference: either `.kind` or `k` (index variable) */
  def kindRef: Parser[String] =
    dotIdent | ("k" ^^^ "_index")

  def sortField: Parser[Field] =
    ident ~ opt(dotIdent) ~ sigExpr ^^ {
      case sort ~ idx ~ binders => Field(FieldType.SortRef(sort, idx), binders)
    }

  def plainField: Parser[Field] =
    ident ^^ { name => Field(FieldType.Plain(name)) }

  def dotIdent: Parser[String] =
    "." ~> ident

  /** Parse `s` or `(s,x)` or `((s,C),x)` — extracts binder postfixes in order.
    * `(s,x)` => List("x"), `((s,C),x)` => List("C", "x") */
  def sigExpr: Parser[List[String]] =
    sigExprInner | ("s" ^^^ Nil)

  def sigExprInner: Parser[List[String]] =
    "(" ~> (sigExprInner | ("s" ^^^ Nil)) ~ ("," ~> ident) <~ ")" ^^ {
      case inner ~ binder => inner :+ binder
    }

  // ---- Result type ----

  /** Parse the return type: `SortName s` or `SortName .idx s` or `SortName k s` or `SortName .idx (s,x)` */
  def resultType: Parser[Option[String]] =
    ident ~ rep(resultArg) ^^ {
      case _ ~ args =>
        // Find the index: a dotIdent like ".shape" (strip the dot)
        args.collectFirst { case s if s.startsWith(".") => s.drop(1) }
    }

  def resultArg: Parser[String] =
    dotIdent.map("." + _) |
    ("(" ~> "[^)]+".r <~ ")") |
    ident

  // ---- Entry point ----

  def parse(input: String): LangSpec =
    parseAll(langSpec, input) match
      case Success(result, _) => result
      case failure: NoSuccess =>
        throw new RuntimeException(s"Parse error: ${failure.msg}\n${failure.next.pos}")
