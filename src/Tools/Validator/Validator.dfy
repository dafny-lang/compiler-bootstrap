include "../../AST/Translator.Entity.dfy"
include "../../Backends/CompilerAdapterPlugin.dfy"

// TODO: Change from a resolver plugin to a command line plugin
module
  {:options "-functionSyntax:4"}
  {:extern "Bootstrap.Tools.Validator.Validator"}
  Bootstrap.Tools.Validator.Validator
{
  import opened AST.Syntax
  import opened AST.Entities
  import AST.Translator.Entity
  import P = AST.Predicates.Deep
  import opened Utils.Lib.Datatypes
  import Interop.CSharpDafnyASTModel

  predicate Supported(e: Expr) {
    !e.Unsupported?
  }

  class DafnyValidator {
    static function ValidateTranslatedProgram(program: Program): Outcome<seq<Debug.Unsupported>> {
      P.All_Program_Outcome(program, (e: Expr) =>
        if e.Unsupported? then Fail(e.un) else Pass)
    }

    static method ValidateProgram(program: CSharpDafnyASTModel.Program) {
      match Entity.TranslateProgram(program, includeCompileModules := true) {
        case Success(translated) =>
          match ValidateTranslatedProgram(translated) {
            case Pass => print "No translation issues found.\n";
            case Fail(issues) =>
              for i := 0 to |issues| {
                var issue := issues[i];
                print issue.loc.ToString() + ": " + issue.Message() + "\n";
              }
          }
        case Failure(err) =>
          print "!! Translation error: " + err.ToString() + "\n";
      }
    }
  }
}
