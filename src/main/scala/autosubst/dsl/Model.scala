package autosubst.dsl

/** A kind of variable, e.g. term variable, type variable. */
case class VarKind(name: String, postfix: String)

/** An enum type used to index a sort, e.g. TySort. */
case class EnumDef(name: String, variants: List[String])

/** The type of a constructor field. */
enum FieldType:
  /** A raw bound variable: BVar s .kind */
  case BVarRef(kind: String)
  /** A reference to a syntax sort: SortName .index (s,binders...) */
  case SortRef(sort: String, index: Option[String])
  /** A variable (bound or free): Var .kind s */
  case VarRef(kind: String)
  /** A plain non-syntax type like Nat */
  case Plain(name: String)

/** A single field of a constructor. */
case class Field(
  fieldType: FieldType,
  binders: List[String] = Nil // list of kind postfixes, e.g. List("x") means one var binder
)

/** A constructor of a syntax sort. */
case class Constructor(
  name: String,
  fields: List[Field] = Nil,
  resultIndex: Option[String] = None // e.g. Some("shape") for Ty constructors
)

/** A syntax sort (inductive type indexed by Sig). */
case class SortDef(
  name: String,
  index: Option[String] = None, // enum name indexing this sort, or "Kind"
  constructors: List[Constructor]
)

/** Top-level language specification. */
case class LangSpec(
  name: String,
  kinds: List[VarKind],
  enums: List[EnumDef] = Nil,
  sorts: List[SortDef]
):
  /** Look up the kind that has the given postfix. */
  def kindByPostfix(postfix: String): VarKind =
    kinds.find(_.postfix == postfix).getOrElse(
      throw new IllegalArgumentException(s"Unknown kind postfix: $postfix")
    )

  /** Check if a name refers to a defined sort. */
  def isSort(name: String): Boolean =
    sorts.exists(_.name == name)

  /** Check if a name refers to a defined enum. */
  def isEnum(name: String): Boolean =
    enums.exists(_.name == name)
