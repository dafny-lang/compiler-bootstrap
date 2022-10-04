include "../../AST/Translator.Entity.dfy"
include "../../Backends/CompilerAdapterPlugin.dfy"

// TODO: Change from a resolver plugin to a command line plugin
module
  {:options "-functionSyntax:4"}
  {:extern "Bootstrap.Tools.Validator.Validator"}
  Bootstrap.Tools.Validator.Validator
{
  import Microsoft.Dafny
  import opened AST.Syntax
  import opened AST.Entities
  import AST.Translator.Entity
  import P = AST.Predicates.Deep
  import opened Utils.Lib.Datatypes

  predicate Supported(e: Expr) {
    !e.Unsupported?
  }

  class DafnyValidator {
    static function ValidateTranslatedProgram(program: Program): Outcome<seq<Debug.Unsupported>> {
      P.All_Program_Outcome(program, (e: Expr) =>
        if e.Unsupported? then Fail(e.un) else Pass)
    }

    static method ValidateProgram(reporter: Dafny.ErrorReporter, program: Dafny.Program) {
      var adapter := new Locations.ReporterAdapter(reporter);
      // FIXME: Why does the entity store not validate with `includeCompileModules := true`?
      match Entity.TranslateProgram(program, includeCompileModules := false) {
        case Success(translated) =>
          match ValidateTranslatedProgram(translated) {
            case Pass => print "No translation issues found.\n";
            case Fail(issues) =>
              for i := 0 to |issues| {
                var issue := issues[i];
                adapter.Message(
                  Dafny.MessageSource.Compiler,
                  Dafny.ErrorLevel.Error,
                  issue.loc, issue.Message()
                );
              }
          }
        case Failure(err) =>
          print "!! Translation error: " + err.ToString() + "\n";
      }
    }
  }
}
