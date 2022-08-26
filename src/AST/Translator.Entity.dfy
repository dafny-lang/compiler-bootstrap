include "Translator.Expressions.dfy"

module Bootstrap.AST.Translator.Entity {
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

  function method TranslateName(str: System.String): TranslationResult<N.Name> {
    var name := TypeConv.AsString(str);
    var parts := Seq.Split('.', name);
    :- Need(forall s | s in parts :: s != "", Invalid("Empty component in name"));
    assert forall s | s in parts :: '.' !in s;
    assert forall s | s in parts :: s != "" && '.' !in s;
    var atoms : seq<N.Atom> := parts;
    Success(Seq.FoldL((n: N.Name, a: N.Atom) => N.Name(n, a), N.Anonymous, atoms))
  }

  function method TranslateAttributeName(s: string): E.AttributeName {
    match s {
      case "axiom" => E.AttributeName.Axiom
      case "extern" => E.AttributeName.Extern
      case _ => E.AttributeName.UserAttribute(s)
    }
  }

  function method TranslateAttributes(attrs: C.Attributes): TranslationResult<seq<E.Attribute>>
    reads *
  {
    var name := TypeConv.AsString(attrs.Name);
    var args :- Seq.MapResult(ListUtils.ToSeq(attrs.Args), Expr.TranslateExpression);
    // TODO: Attributes needs to be nullable
    //var rest :- if attrs.Prev == null then Success([]) else TranslateAttributes(attrs.Prev);
    var rest := [];
    Success([E.Attribute.Attribute(TranslateAttributeName(name), args)] + rest)
  }

  function method TranslateField(f: C.Field): (d: TranslationResult<E.Entity>)
    reads *
  {
    var name :- TranslateName(f.FullDafnyName);
    var attrs :- TranslateAttributes(f.Attributes);
    var kind := if f.IsMutable then E.Var else E.Const;
    var ei := E.EntityInfo(name, attrs := attrs, members := []);
    if f is C.ConstantField then
      var init :- Expr.TranslateExpression((f as C.ConstantField).Rhs);
      Success(E.Definition(ei, E.Definition.Field(E.Field.Field(kind, Some(init)))))
    else
      Success(E.Definition(ei, E.Definition.Field(E.Field.Field(kind, None))))
  }

  function method TranslateMethod(m: C.Method): (d: TranslationResult<E.Entity>)
    reads *
  {
    var name :- TranslateName(m.FullDafnyName);
    var attrs :- TranslateAttributes(m.Attributes);
    var body :- Expr.TranslateStatement(m.Body);
    var def := if m is C.Constructor then
                 E.Constructor(body)
               else
                 E.Method(body);
    var ei := E.EntityInfo(name, attrs := attrs, members := []);
    Success(E.Definition(ei, E.Callable(def)))
  }

  function method TranslateFunction(f: C.Function): (d: TranslationResult<E.Entity>)
    reads *
  {
    var name :- TranslateName(f.FullDafnyName);
    var attrs :- TranslateAttributes(f.Attributes);
    var body :- Expr.TranslateExpression(f.Body);
    var ei := E.EntityInfo(name, attrs := attrs, members := []);
    Success(E.Definition(ei, E.Callable(E.Function(body))))
  }

  function method TranslateMemberDecl(md: C.MemberDecl): (d: TranslationResult<E.Entity>)
    reads *
  {
    if md is C.Field then
      TranslateField(md)
    else if md is C.Function then
      TranslateFunction(md)
    else if md is C.Method then
      TranslateMethod(md)
    else
      Failure(Invalid("Unsupported member declaration type"))
  }

  function method TranslateTypeSynonymDecl(ts: C.TypeSynonymDecl): (e: TranslationResult<E.Type>)
    reads *
  {
    var ty :- Expr.TranslateType(ts.Rhs);
    Success(E.Type.TypeAlias(E.TypeAlias.TypeAlias(ty)))
  }

  function method TranslateOpaqueTypeDecl(ot: C.OpaqueTypeDecl): (e: TranslationResult<E.Type>)
    reads *
  {
    Success(E.Type.AbstractType(E.AbstractType.AbstractType()))
  }

  function method TranslateNewtypeDecl(nt: C.NewtypeDecl): (e: TranslationResult<E.Type>)
    reads *
  {
    Success(E.Type.NewType(E.NewType.NewType()))
  }

  function method TranslateDatatypeDecl(dt: C.DatatypeDecl): (e: TranslationResult<E.Type>)
    reads *
  {
    Success(E.Type.DataType(E.DataType.DataType()))
  }

  function method TranslateTraitDecl(t: C.TraitDecl): (e: TranslationResult<E.Type>)
    reads *
  {
    var parentTraits :- Seq.MapResult(ListUtils.ToSeq(t.ParentTraits), (t: C.Type) reads * =>
      TranslateName(t.AsTraitType.FullDafnyName));
    Success(E.Type.TraitType(E.TraitType.TraitType(parentTraits)))
  }

  function method TranslateClassDecl(c: C.ClassDecl): (e: TranslationResult<E.Type>)
    reads *
  {
    var parentTraits :- Seq.MapResult(ListUtils.ToSeq(c.ParentTraits), (t: C.Type) reads * =>
      TranslateName(t.AsTraitType.FullDafnyName));
    Success(E.Type.ClassType(E.ClassType.ClassType(parentTraits)))
  }

  function method TranslateEntityInfo(tl: C.TopLevelDecl): (e: TranslationResult<E.EntityInfo>)
    reads *
  {
    var name :- TranslateName(tl.FullDafnyName);
    var attrs :- TranslateAttributes(tl.Attributes);
    Success(E.EntityInfo(name, attrs := attrs, members := []))
  }

  function method TranslateEntityInfoMembers(tl: C.TopLevelDeclWithMembers): (e: TranslationResult<(seq<E.Entity>, E.EntityInfo)>)
    reads *
  {
    var name :- TranslateName(tl.FullDafnyName);
    var attrs :- TranslateAttributes(tl.Attributes);
    var memberDecls := ListUtils.ToSeq(tl.Members);
    var members :- Seq.MapResult(memberDecls, d reads * => TranslateMemberDecl(d));
    var memberNames := Seq.Map((m: E.Entity) => m.ei.name, members);
    :- Need(forall nm <- memberNames :: nm.ChildOf(name), Invalid("Malformed name"));
    Success((members, E.EntityInfo(name, attrs := attrs, members := memberNames)))
  }

  function method TranslateTopLevelDeclWithMembers(tl: C.TopLevelDeclWithMembers): (e: TranslationResult<seq<E.Entity>>)
    reads *
  {
    var (members, ei) :- TranslateEntityInfoMembers(tl);
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
                 Failure(Invalid("Unsupported top level declaration type"));
    var topEntity := E.Entity.Type(ei, top);
    Success([topEntity] + members)
  }

  function method TranslateTopLevelDecl(tl: C.TopLevelDecl): (exps: TranslationResult<seq<E.Entity>>)
    reads *
    decreases ASTHeight(tl), 0
  {
    if tl is C.TopLevelDeclWithMembers then
      TranslateTopLevelDeclWithMembers(tl)
    else if tl is C.ModuleDecl then
      var md := tl as C.ModuleDecl;
      assume ASTHeight(md.Signature) < ASTHeight(tl);
      TranslateModule(md.Signature)
    else
      Failure(Invalid("Unsupported top level declaration type"))
  }

  function method TranslateModule(sig: C.ModuleSignature): (m: TranslationResult<seq<E.Entity>>)
    reads *
    decreases ASTHeight(sig), 1
  {
    var name :- TranslateName(sig.ModuleDef.FullDafnyName);
    var attrs :- TranslateAttributes(sig.ModuleDef.Attributes);
    var includes := ListUtils.ToSeq(sig.ModuleDef.Includes);
    var exports := sig.ExportSets;
    var topLevels := DictUtils.DictionaryToSeq(sig.TopLevels);
    var topDecls :- Seq.MapResult(topLevels,
      (tl: (System.String, C.TopLevelDecl)) reads * =>
        assume ASTHeight(tl.1) < ASTHeight(sig);
        TranslateTopLevelDecl(tl.1));
    var topDecls' := Seq.Flatten(topDecls);
    var topNames := Seq.Map((d: E.Entity) => d.ei.name, topDecls');
    :- Need(forall nm <- topNames :: nm.ChildOf(name), Invalid("Malformed name"));
    var ei := E.EntityInfo(name, attrs := attrs, members := topNames);
    var mod := E.Entity.Module(ei, E.Module.Module());
    Success([mod] + topDecls')
  }

  function method TranslateProgram(p: C.Program): (exps: TranslationResult<E.Program>)
    reads *
  {
    var moduleSigs := DictUtils.DictionaryToSeq(p.ModuleSigs);
    var entities :- Seq.MapResult(moduleSigs,
      (sig: (C.ModuleDefinition, C.ModuleSignature)) reads * => TranslateModule(sig.1));
    var regMap := Seq.FoldL((m:map<N.Name, E.Entity>, e: E.Entity) => m + map[e.ei.name := e], map[], Seq.Flatten(entities));
    var mainMethodName :- TranslateName(p.MainMethod.FullDafnyName);
    var defaultModuleName :- TranslateName(p.DefaultModule.FullDafnyName);
    var reg := E.Registry_.Registry(regMap);
    :- Need(reg.Validate().Pass?, Invalid("Failed to validate registry"));
    var prog := E.Program(reg, defaultModule := defaultModuleName, mainMethod := Some(mainMethodName));
    if prog.Valid?() then Success(prog) else Failure(Invalid("Generated invalid program"))
  }
}