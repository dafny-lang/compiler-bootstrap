module Bootstrap.AST.Names {
  type Atom =
    // An individual component of a Dafny name.
    s: string | s != "" && '.' !in s witness "n"

  datatype Name =
    | Anonymous
    | Name(parent: Name, suffix: Atom)
  {
    predicate method Extends(parent: Name)
      // Check whether `this` is a descendant of `parent`.
    {
      this.Name? && this.parent == parent
    }
  }
}
