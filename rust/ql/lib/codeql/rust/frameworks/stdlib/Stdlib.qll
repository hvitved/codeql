/**
 * Provides classes modeling security-relevant aspects of the standard libraries.
 */

private import rust
private import codeql.rust.Concepts
private import codeql.rust.controlflow.ControlFlowGraph as Cfg
private import codeql.rust.controlflow.CfgNodes as CfgNodes
private import codeql.rust.dataflow.DataFlow
private import codeql.rust.dataflow.FlowSummary
private import codeql.rust.internal.PathResolution
private import codeql.rust.internal.Type
private import codeql.rust.internal.TypeInference
private import codeql.rust.internal.TypeMention

/**
 * A call to the `starts_with` method on a `Path`.
 */
private class StartswithCall extends Path::SafeAccessCheck::Range, CfgNodes::MethodCallExprCfgNode {
  StartswithCall() {
    this.getMethodCallExpr().getStaticTarget().getCanonicalPath() = "<std::path::Path>::starts_with"
  }

  override predicate checks(Cfg::CfgNode e, boolean branch) {
    e = this.getReceiver() and
    branch = true
  }
}

/**
 * The [`Option` enum][1].
 *
 * [1]: https://doc.rust-lang.org/std/option/enum.Option.html
 */
class OptionEnum extends Enum {
  pragma[nomagic]
  OptionEnum() { this.getCanonicalPath() = "core::option::Option" }

  /** Gets the `Some` variant. */
  Variant getSome() { result = this.getVariant("Some") }
}

/**
 * The [`Result` enum][1].
 *
 * [1]: https://doc.rust-lang.org/stable/std/result/enum.Result.html
 */
class ResultEnum extends Enum {
  pragma[nomagic]
  ResultEnum() { this.getCanonicalPath() = "core::result::Result" }

  /** Gets the `Ok` variant. */
  Variant getOk() { result = this.getVariant("Ok") }

  /** Gets the `Err` variant. */
  Variant getErr() { result = this.getVariant("Err") }
}

/**
 * The [`Range` struct][1].
 *
 * [1]: https://doc.rust-lang.org/core/ops/struct.Range.html
 */
class RangeStruct extends Struct {
  pragma[nomagic]
  RangeStruct() { this.getCanonicalPath() = "core::ops::range::Range" }

  /** Gets the `start` field. */
  StructField getStart() { result = this.getStructField("start") }

  /** Gets the `end` field. */
  StructField getEnd() { result = this.getStructField("end") }
}

/**
 * The [`RangeFrom` struct][1].
 *
 * [1]: https://doc.rust-lang.org/core/ops/struct.RangeFrom.html
 */
class RangeFromStruct extends Struct {
  pragma[nomagic]
  RangeFromStruct() { this.getCanonicalPath() = "core::ops::range::RangeFrom" }

  /** Gets the `start` field. */
  StructField getStart() { result = this.getStructField("start") }
}

/**
 * The [`RangeTo` struct][1].
 *
 * [1]: https://doc.rust-lang.org/core/ops/struct.RangeTo.html
 */
class RangeToStruct extends Struct {
  pragma[nomagic]
  RangeToStruct() { this.getCanonicalPath() = "core::ops::range::RangeTo" }

  /** Gets the `end` field. */
  StructField getEnd() { result = this.getStructField("end") }
}

/**
 * The [`RangeFull` struct][1].
 *
 * [1]: https://doc.rust-lang.org/core/ops/struct.RangeFull.html
 */
class RangeFullStruct extends Struct {
  pragma[nomagic]
  RangeFullStruct() { this.getCanonicalPath() = "core::ops::range::RangeFull" }
}

/**
 * The [`RangeInclusive` struct][1].
 *
 * [1]: https://doc.rust-lang.org/core/ops/struct.RangeInclusive.html
 */
class RangeInclusiveStruct extends Struct {
  pragma[nomagic]
  RangeInclusiveStruct() { this.getCanonicalPath() = "core::ops::range::RangeInclusive" }

  /** Gets the `start` field. */
  StructField getStart() { result = this.getStructField("start") }

  /** Gets the `end` field. */
  StructField getEnd() { result = this.getStructField("end") }
}

/**
 * The [`RangeToInclusive` struct][1].
 *
 * [1]: https://doc.rust-lang.org/core/ops/struct.RangeToInclusive.html
 */
class RangeToInclusiveStruct extends Struct {
  pragma[nomagic]
  RangeToInclusiveStruct() { this.getCanonicalPath() = "core::ops::range::RangeToInclusive" }

  /** Gets the `end` field. */
  StructField getEnd() { result = this.getStructField("end") }
}

/**
 * The [`Future` trait][1].
 *
 * [1]: https://doc.rust-lang.org/std/future/trait.Future.html
 */
class FutureTrait extends Trait {
  pragma[nomagic]
  FutureTrait() { this.getCanonicalPath() = "core::future::future::Future" }

  /** Gets the `Output` associated type. */
  pragma[nomagic]
  TypeAlias getOutputType() {
    result = this.getAssocItemList().getAnAssocItem() and
    result.getName().getText() = "Output"
  }
}

/**
 * The [`FnOnce` trait][1].
 *
 * [1]: https://doc.rust-lang.org/std/ops/trait.FnOnce.html
 */
class FnOnceTrait extends Trait {
  pragma[nomagic]
  FnOnceTrait() { this.getCanonicalPath() = "core::ops::function::FnOnce" }

  /** Gets the type parameter of this trait. */
  TypeParam getTypeParam() { result = this.getGenericParamList().getGenericParam(0) }

  /** Gets the `Output` associated type. */
  pragma[nomagic]
  TypeAlias getOutputType() {
    result = this.getAssocItemList().getAnAssocItem() and
    result.getName().getText() = "Output"
  }
}

/**
 * The [`Iterator` trait][1].
 *
 * [1]: https://doc.rust-lang.org/std/iter/trait.Iterator.html
 */
class IteratorTrait extends Trait {
  pragma[nomagic]
  IteratorTrait() { this.getCanonicalPath() = "core::iter::traits::iterator::Iterator" }

  /** Gets the `Item` associated type. */
  pragma[nomagic]
  TypeAlias getItemType() {
    result = this.getAssocItemList().getAnAssocItem() and
    result.getName().getText() = "Item"
  }
}

/**
 * The [`IntoIterator` trait][1].
 *
 * [1]: https://doc.rust-lang.org/std/iter/trait.IntoIterator.html
 */
class IntoIteratorTrait extends Trait {
  pragma[nomagic]
  IntoIteratorTrait() { this.getCanonicalPath() = "core::iter::traits::collect::IntoIterator" }

  /** Gets the `Item` associated type. */
  pragma[nomagic]
  TypeAlias getItemType() {
    result = this.getAssocItemList().getAnAssocItem() and
    result.getName().getText() = "Item"
  }
}

/**
 * The [`String` struct][1].
 *
 * [1]: https://doc.rust-lang.org/std/string/struct.String.html
 */
class StringStruct extends Struct {
  pragma[nomagic]
  StringStruct() { this.getCanonicalPath() = "alloc::string::String" }
}

/**
 * The [`Deref` trait][1].
 *
 * [1]: https://doc.rust-lang.org/core/ops/trait.Deref.html
 */
class DerefTrait extends Trait {
  pragma[nomagic]
  DerefTrait() { this.getCanonicalPath() = "core::ops::deref::Deref" }

  /** Gets the `deref` function. */
  Function getDerefFunction() { result = this.(TraitItemNode).getAssocItem("deref") }

  /** Gets the `Target` associated type. */
  pragma[nomagic]
  TypeAlias getTargetType() {
    result = this.getAssocItemList().getAnAssocItem() and
    result.getName().getText() = "Target"
  }
}

/**
 * One of the two special
 *
 * ```rust
 * impl<T: ?Sized> const Deref for &T
 * impl<T: ?Sized> const Deref for &mut T
 * ```
 *
 * implementations.
 */
private class CoreDerefImpl extends ImplItemNode {
  pragma[nomagic]
  CoreDerefImpl() {
    this.resolveTraitTy() instanceof DerefTrait and
    this.(Impl)
        .getSelfTy()
        .(TypeMention)
        .resolveTypeAt(TypePath::singleton(TRefTypeParameter()))
        .(TypeParamTypeParameter)
        .getTypeParam() = this.getTypeParam(_)
  }

  Function getDeref() { result = this.getASuccessor("deref") }
}

// TODO: Use MaD when `&(mut) T` is assigned an appropriate canonical path
private class CoreDerefSummarizedCallable extends SummarizedCallable::Range {
  CoreDerefSummarizedCallable() { this = any(CoreDerefImpl i).getDeref() }

  override predicate propagatesFlow(string input, string output, boolean preservesValue) {
    input = "Argument[self].Reference" and
    output = "ReturnValue" and
    preservesValue = true
  }
}

/**
 * The [`Index` trait][1].
 *
 * [1]: https://doc.rust-lang.org/std/ops/trait.Index.html
 */
class IndexTrait extends Trait {
  pragma[nomagic]
  IndexTrait() { this.getCanonicalPath() = "core::ops::index::Index" }

  /** Gets the `index` function. */
  Function getIndexFunction() { result = this.(TraitItemNode).getAssocItem("index") }

  /** Gets the `Output` associated type. */
  pragma[nomagic]
  TypeAlias getOutputType() {
    result = this.getAssocItemList().getAnAssocItem() and
    result.getName().getText() = "Output"
  }
}

/**
 * One of the two special
 *
 * ```rust
 * impl<T, I, const N: usize> Index<I> for [T; N]
 * impl<T, I> ops::Index<I> for [T]
 * ```
 *
 * implementations.
 */
private class CoreIndexImpl extends ImplItemNode {
  pragma[nomagic]
  CoreIndexImpl() {
    this.resolveTraitTy() instanceof IndexTrait and
    exists(TypeParameter tp | tp = TArrayTypeParameter() or tp = TSliceTypeParameter() |
      this.(Impl)
          .getSelfTy()
          .(TypeMention)
          .resolveTypeAt(TypePath::singleton(tp))
          .(TypeParamTypeParameter)
          .getTypeParam() = this.getTypeParam(_)
    )
  }

  Function getIndex() { result = this.getASuccessor("index") }
}

// TODO: Use MaD when `[T(; N)]` is assigned an appropriate canonical path
private class CoreIndexSummarizedCallable extends SummarizedCallable::Range {
  CoreIndexSummarizedCallable() { this = any(CoreIndexImpl i).getIndex() }

  override predicate propagatesFlow(string input, string output, boolean preservesValue) {
    input = "Argument[self].Reference.Element" and
    output = "ReturnValue" and
    preservesValue = true
  }
}
