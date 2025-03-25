/**
 * This module provides a hand-modifiable wrapper around the generated class `UseTree`.
 *
 * INTERNAL: Do not use.
 */

private import codeql.rust.elements.internal.generated.UseTree

/**
 * INTERNAL: This module contains the customizable definition of `UseTree` and should not
 * be referenced directly.
 */
module Impl {
  // the following QLdoc is generated: if you need to edit it, do it in the schema file
  /**
   * A UseTree. For example:
   * ```rust
   * use std::collections::HashMap;
   * use std::collections::*;
   * use std::collections::HashMap as MyHashMap;
   * use std::collections::{self, HashMap, HashSet};
   * ```
   */
  class UseTree extends Generated::UseTree {
    override string toStringImpl() {
      result =
        this.getPath().toStringImpl() +
          any(string list | if this.hasUseTreeList() then list = "::{...}" else list = "") +
          any(string glob | if this.isGlob() then glob = "::*" else glob = "") +
          any(string rename |
            rename = " as " + this.getRename().getName().getText()
            or
            rename = "" and not this.hasRename()
          )
    }
  }
}
