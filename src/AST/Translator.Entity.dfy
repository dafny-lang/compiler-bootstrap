include "Translator.Expressions.dfy"

module {:options "-functionSyntax:4"} Bootstrap.AST.Translator.Entity {
  import opened Utils.Lib
  import opened Utils.Lib.Datatypes
  import opened Interop.CSharpInterop
  import opened Interop.CSharpDafnyInterop
  import opened Interop.CSharpDafnyASTInterop
  import C = Interop.CSharpDafnyASTModel
  import E = Entities
  import N = Names
  import Expr = Expressions
  import opened Common

  function TranslateName(str: System.String): TranslationResult<N.Name> {
    var name := TypeConv.AsString(str);
    if name == "" then
      Success(N.Anonymous)
    else
      var parts := Seq.Split('.', name);
      :- Need(forall s | s in parts :: s != "", Invalid("Empty component in name: " + name));
      assert forall s | s in parts :: '.' !in s;
      assert forall s | s in parts :: s != "" && '.' !in s;
      var atoms : seq<N.Atom> := parts;
      Success(Seq.FoldL((n: N.Name, a: N.Atom) => N.Name(n, a), N.Anonymous, atoms))
  }

  function TranslateLocation(tok: Microsoft.Boogie.IToken): E.Location
    reads *
  {
    var filename := if tok.FileName == null then "<none>" else TypeConv.AsString(tok.FileName);
    var line := tok.Line;
    var col := tok.Column;
    E.Location(filename, line as int, col as int)
  }

  function TranslateAttributeName(s: string): E.AttributeName {
    match s {
      case "axiom" => E.AttributeName.Axiom
      case "extern" => E.AttributeName.Extern
      case _ => E.AttributeName.UserAttribute(s)
    }
  }

  function TranslateAttributes(attrs: C.Attributes): TranslationResult<seq<E.Attribute>>
    reads *
    decreases ASTHeight(attrs)
  {
    if attrs == null then
      Success([])
    else
      var name := TypeConv.AsString(attrs.Name);
      var args :- Seq.MapResult(ListUtils.ToSeq(attrs.Args), Expr.TranslateExpression);
      assume ASTHeight(attrs.Prev) < ASTHeight(attrs);
      var rest :- TranslateAttributes(attrs.Prev);
      Success([E.Attribute.Attribute(TranslateAttributeName(name), args)] + rest)
  }

  function TranslateMemberEntityInfo(md: C.MemberDecl): (e: TranslationResult<E.EntityInfo>)
    reads *
  {
    var name :- TranslateName(md.FullDafnyName);
    var attrs :- TranslateAttributes(md.Attributes);
    var loc := TranslateLocation(md.tok);
    Success(E.EntityInfo(name, location := loc, attrs := attrs, members := []))
  }

  function TranslateField(f: C.Field): (d: TranslationResult<E.Entity>)
    reads *
  {
    var kind := if f.IsMutable then E.Var else E.Const;
    var ei :- TranslateMemberEntityInfo(f);
    if f is C.ConstantField then
      var init :- Expr.TranslateExpression((f as C.ConstantField).Rhs);
      Success(E.Definition(ei, E.Definition.Field(E.Field.Field(kind, Some(init)))))
    else
      Success(E.Definition(ei, E.Definition.Field(E.Field.Field(kind, None))))
  }

  function TranslateMethod(m: C.Method): (d: TranslationResult<E.Entity>)
    reads *
  {
    var body :- Expr.TranslateOptionalStatement(m.Body);
    var req :- Seq.MapResult(ListUtils.ToSeq(m.Req), (ae: C.AttributedExpression) reads * => Expr.TranslateExpression(ae.E));
    var ens :- Seq.MapResult(ListUtils.ToSeq(m.Ens), (ae: C.AttributedExpression) reads * => Expr.TranslateExpression(ae.E));
    var def := if m is C.Constructor then
                 E.Constructor(req := req, ens := ens, body := body)
               else
                 E.Method(req := req, ens := ens, body := body);
    var ei :- TranslateMemberEntityInfo(m);
    Success(E.Definition(ei, E.Callable(def)))
  }

  function TranslateFunction(f: C.Function): (d: TranslationResult<E.Entity>)
    reads *
  {
    var body :- Expr.TranslateOptionalExpression(f.Body);
    var req :- Seq.MapResult(ListUtils.ToSeq(f.Req), (ae: C.AttributedExpression) reads * => Expr.TranslateExpression(ae.E));
    var ens :- Seq.MapResult(ListUtils.ToSeq(f.Ens), (ae: C.AttributedExpression) reads * => Expr.TranslateExpression(ae.E));
    var ei :- TranslateMemberEntityInfo(f);
    Success(E.Definition(ei, E.Callable(E.Function(req := req, ens := ens, body := body))))
  }

  function TranslateMemberDecl(md: C.MemberDecl): (d: TranslationResult<E.Entity>)
    reads *
  {
    if md is C.Field then
      TranslateField(md)
    else if md is C.Function then
      TranslateFunction(md)
    else if md is C.Method then
      TranslateMethod(md)
    else
      Failure(Invalid("Unsupported member declaration type: " + TypeConv.AsString(md.FullDafnyName)))
  }

  function TranslateTypeSynonymDecl(ts: C.TypeSynonymDecl): (e: TranslationResult<seq<E.Entity>>)
    reads *
  {
    // TODO: handle subset, nonnull types
    var ty :- Expr.TranslateType(ts.Rhs);
    var ei :- TranslateTopLevelEntityInfo(ts);
    Success([E.Entity.Type(ei, E.Type.TypeAlias(E.TypeAlias.TypeAlias(ty)))])
  }

  function TranslateTypeParameter(ts: C.TypeParameter): (e: TranslationResult<seq<E.Entity>>)
    reads *
  {
    // TODO: handle variance, etc
    var ei :- TranslateTopLevelEntityInfo(ts);
    Success([E.Entity.Type(ei, E.Type.TypeParameter(E.TypeParameter.TypeParameter()))])
  }

  function TranslateOpaqueTypeDecl(ot: C.OpaqueTypeDecl): (e: TranslationResult<E.Type>)
    reads *
  {
    Success(E.Type.AbstractType(E.AbstractType.AbstractType()))
  }

  function TranslateNewtypeDecl(nt: C.NewtypeDecl): (e: TranslationResult<E.Type>)
    reads *
  {
    Success(E.Type.NewType(E.NewType.NewType()))
  }

  function TranslateDatatypeDecl(dt: C.DatatypeDecl): (e: TranslationResult<E.Type>)
    reads *
  {
    Success(E.Type.DataType(E.DataType.DataType()))
  }

  function TranslateTraitDecl(t: C.TraitDecl): (e: TranslationResult<E.Type>)
    reads *
  {
    var parentTraits :- Seq.MapResult(ListUtils.ToSeq(t.ParentTraits), (t: C.Type) reads * =>
      TranslateName(t.AsTraitType.FullDafnyName));
    Success(E.Type.TraitType(E.TraitType.TraitType(parentTraits)))
  }

  function TranslateClassDecl(c: C.ClassDecl): (e: TranslationResult<E.Type>)
    reads *
  {
    var parentTraits :- Seq.MapResult(ListUtils.ToSeq(c.ParentTraits), (t: C.Type) reads * =>
      TranslateName(t.AsTraitType.FullDafnyName));
    Success(E.Type.ClassType(E.ClassType.ClassType(parentTraits)))
  }

  function TranslateTopLevelEntityInfo(tl: C.TopLevelDecl): (e: TranslationResult<E.EntityInfo>)
    reads *
  {
    var name :- TranslateName(tl.FullDafnyName);
    var attrs :- TranslateAttributes(tl.Attributes);
    var loc := TranslateLocation(tl.tok);
    Success(E.EntityInfo(name, location := loc, attrs := attrs, members := []))
  }

  function TranslateTopLevelEntityInfoMembers(tl: C.TopLevelDeclWithMembers): (e: TranslationResult<(seq<E.Entity>, E.EntityInfo)>)
    reads *
  {
    var name :- TranslateName(tl.FullDafnyName);
    var attrs :- TranslateAttributes(tl.Attributes);
    var loc := TranslateLocation(tl.tok);
    var memberDecls := ListUtils.ToSeq(tl.Members);
    var members :- Seq.MapResult(memberDecls, d reads * => TranslateMemberDecl(d));
    var memberNames := Seq.Map((m: E.Entity) => m.ei.name, members);
    :- Need(forall nm <- memberNames :: nm.ChildOf(name), Invalid("Malformed member name in " + name.ToString()));
    Success((members, E.EntityInfo(name, location := loc, attrs := attrs, members := memberNames)))
  }

  function TranslateTopLevelDeclWithMembers(tl: C.TopLevelDeclWithMembers): (e: TranslationResult<seq<E.Entity>>)
    reads *
  {
    var (members, ei) :- TranslateTopLevelEntityInfoMembers(tl);
    var top :- if tl is C.OpaqueTypeDecl then
                 TranslateOpaqueTypeDecl(tl)
               else if tl is C.NewtypeDecl then
                 TranslateNewtypeDecl(tl)
               else if tl is C.DatatypeDecl then
                 TranslateDatatypeDecl(tl)
               else if tl is C.TraitDecl then
                 TranslateTraitDecl(tl)
               else if tl is C.ClassDecl then
                 TranslateClassDecl(tl)
               else
                 Failure(Invalid("Unsupported top level declaration type for " + TypeConv.AsString(tl.FullDafnyName)));
    var topEntity := E.Entity.Type(ei, top);
    Success([topEntity] + members)
  }

  function TranslateTopLevelDecl(tl: C.TopLevelDecl): (exps: TranslationResult<seq<E.Entity>>)
    reads *
    decreases ASTHeight(tl), 0
  {
    if tl is C.TopLevelDeclWithMembers then
      TranslateTopLevelDeclWithMembers(tl)
    else if tl is C.TypeSynonymDecl then
      TranslateTypeSynonymDecl(tl)
    else if tl is C.TypeParameter then
      TranslateTypeParameter(tl)
    else if tl is C.ModuleDecl then
      var md := tl as C.ModuleDecl;
      assume ASTHeight(md.Signature) < ASTHeight(tl);
      TranslateModule(md.Signature)
    else
      Failure(Invalid("Unsupported top level declaration type for " + TypeConv.AsString(tl.FullDafnyName)))
  }

  function TranslateModule(sig: C.ModuleSignature): (m: TranslationResult<seq<E.Entity>>)
    reads *
    decreases ASTHeight(sig), 1
  {
    var def := sig.ModuleDef;
    var name :- TranslateName(def.FullDafnyName);
    var attrs :- TranslateAttributes(def.Attributes);
    var loc := TranslateLocation(def.tok);
    var includes := ListUtils.ToSeq(def.Includes);
    var exports := sig.ExportSets;
    var topLevels := DictUtils.DictionaryToSeq(sig.TopLevels);
    var topDecls :- Seq.MapResult(topLevels,
      (tl: (System.String, C.TopLevelDecl)) reads * =>
        assume ASTHeight(tl.1) < ASTHeight(sig);
        TranslateTopLevelDecl(tl.1));
    var topDecls' := Seq.Flatten(topDecls);
    var topNames := Seq.Map((d: E.Entity) => d.ei.name, topDecls');
    assume forall nm <- topNames :: nm.ChildOf(name);
    //:- Need(forall nm <- topNames :: nm.ChildOf(name), Invalid("Malformed name in " + name.ToString()));
    var ei := E.EntityInfo(name, location := loc, attrs := attrs, members := topNames);
    var mod := E.Entity.Module(ei, E.Module.Module());
    Success([mod] + topDecls')
  }

  // TODO: generate a valid program with a validated registry
  function TranslateProgram(p: C.Program): (exps: TranslationResult<E.Registry_>)
    reads *
  {
    var moduleSigs := DictUtils.DictionaryToSeq(p.ModuleSigs);
    var entities :- Seq.MapResult(moduleSigs,
      (sig: (C.ModuleDefinition, C.ModuleSignature)) reads * => TranslateModule(sig.1));
    var regMap := Seq.FoldL((m:map<N.Name, E.Entity>, e: E.Entity) => m + map[e.ei.name := e], map[], Seq.Flatten(entities));
    var mainMethodName :- if p.MainMethod == null then
                            Success(None)
                          else
                            var methodName :- TranslateName(p.MainMethod.FullDafnyName);
                            Success(Some(methodName));
    var defaultModuleName :- TranslateName(p.DefaultModule.FullDafnyName);
    var reg := E.Registry_.Registry(regMap);
    Success(reg)
    /*
    match reg.Validate() {
      case Pass =>
        var prog := E.Program(reg, defaultModule := defaultModuleName, mainMethod := mainMethodName);
        if prog.Valid?() then Success(prog) else Failure(Invalid("Generated invalid program"))
      case Fail(errs) =>
        var err := Seq.Flatten(Seq.Map((e: E.ValidationError) => e.ToString(), errs));
        Failure(Invalid("Failed to validate registry: " + err))
    }
    */
  }
}