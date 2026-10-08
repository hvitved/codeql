overlay[local]
module;

private import unified
private import AstPlugin

private predicate structHasParameterForField(
  ClassLikeDeclaration struct, int i, string name, boolean hasDefault, AstNode type
) {
  struct.hasModifier("struct") and
  exists(VariableDeclaration decl |
    decl = struct.getMember(i) and
    not decl.hasModifier("static") and
    name = decl.getPattern().(Identifier).getValue() and
    type = decl.getType()
  |
    // if `decl` has an initializer then the parameter has that initializer as a default value
    decl.hasModifier("var") and
    hasDefault = true
    or
    decl.hasModifier("let") and
    not exists(decl.getValue()) and
    hasDefault = false
  )
}

private class AstPluginSwift extends AstPlugin {
  bindingset[f]
  override string getFunctionDeclarationKeyword(FunctionDeclaration f) {
    exists(f) and result = "func"
  }

  bindingset[c]
  override string getConstructorDeclarationKeyword(ConstructorDeclaration c) {
    c.hasModifier(result) and
    result = "convenience"
  }

  override string getClassLikeDeclarationKeyword(ClassLikeDeclaration cls) {
    cls.hasModifier(result) and
    result in ["class", "struct", "enum", "actor", "extension", "protocol"]
  }

  override string getVariableDeclarationKeyword(VariableDeclaration decl) {
    decl.hasModifier(result) and
    result in ["var", "let"]
  }

  bindingset[cd]
  override predicate defaultConstructorParameter(
    ConstructorDeclaration cd, int i, string name, boolean hasDefault, AstNode type
  ) {
    exists(ClassLikeDeclaration struct |
      cd = struct.getAMember() and
      name =
        rank[i](int j, string s | structHasParameterForField(struct, j, s, _, _) | s order by j) and
      structHasParameterForField(struct, _, name, hasDefault, type)
    )
  }
}
