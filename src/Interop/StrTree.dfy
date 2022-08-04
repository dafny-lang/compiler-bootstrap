include "../Utils/StrTree.dfy"
include "../Interop/CSharpDafnyInterop.dfy"

module Bootstrap.Interop.StrTree {
  import opened Utils.StrTree
  import opened CSharpDafnyInterop
  import Microsoft

  class SyntaxTreeAdapter {
    var wr: Microsoft.Dafny.ConcreteSyntaxTree

    constructor(wr: Microsoft.Dafny.ConcreteSyntaxTree) {
      this.wr := wr;
    }

    method Write(value: string) {
      wr.Write(StringUtils.ToCString(value));
    }

    method WriteLine(value: string) {
      wr.WriteLine(StringUtils.ToCString(value));
    }

    method NewBlock(header: string) returns (st': SyntaxTreeAdapter) {
      var wr' := wr.NewBlock(StringUtils.ToCString(header));
      st' := new SyntaxTreeAdapter(wr');
    }

    method WriteTree(tree: StrTree.StrTree) {
      match tree {
        case Str(s) =>
          Write(s);
        case SepSeq(sep, trees) =>
          for i := 0 to |trees| {
            if i != 0 && sep.Some? {
              Write(sep.value);
            }
            WriteTree(trees[i]);
          }
        case Unsupported() =>
      }
    }
  }
}
