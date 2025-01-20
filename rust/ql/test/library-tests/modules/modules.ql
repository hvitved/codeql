import rust
import codeql.rust.elements.internal.ItemImpl::Impl as ItemImpl

query predicate mod(Module m) { any() }

query predicate resolveItem(Path p, Item i) { i = ItemImpl::resolveItem(p) }
