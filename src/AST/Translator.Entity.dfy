include "Locations.dfy"
include "Translator.Expressions.dfy"
include "Translator.Location.dfy"

module {:options "-functionSyntax:4"} Bootstrap.AST.Translator.Entity {
  import opened Utils.Lib
  import opened Utils.Lib.Datatypes
  import opened Interop.CSharpInterop
  import opened Interop.CSharpDafnyInterop
  import opened Interop.CSharpDafnyASTInterop
  import opened Locations
  import L = Location
  import C = Microsoft.Dafny
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
    if IsNull(attrs) then
      Success([])
    else
      var name := TypeConv.AsString(attrs.Name);
      var args :- Seq.MapResult(ListUtils.ToSeq(attrs.Args), Expr.TranslateExpression);
      assume {:axiom} {:axiom} ASTHeight(attrs.Prev) < ASTHeight(attrs);
      var rest :- TranslateAttributes(attrs.Prev);
      Success([E.Attribute.Attribute(TranslateAttributeName(name), args)] + rest)
  }

  function TranslateMemberEntityInfo(md: C.MemberDecl): (e: TranslationResult<E.EntityInfo>)
    reads *
  {
    var name :- TranslateName(md.FullName);
    var attrs :- TranslateAttributes(md.Attributes);
    var loc := L.TranslateLocation(md.tok);
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
      var ei :- TranslateMemberEntityInfo(md);
      TranslateUnsupportedDecl(ei, md)
  }

  function TranslateTypeSynonymDecl(ts: C.TypeSynonymDecl): (e: TranslationResult<seq<E.Entity>>)
    reads *
  {
    var ty :- Expr.TranslateType(ts.Rhs);
    var ei :- TranslateTopLevelEntityInfo(ts);
    Success([E.Entity.Type(ei, E.Type.TypeAlias(E.TypeAlias.TypeAlias(ty, false)))])
  }

  function TranslateSubsetTypeDecl(st: C.SubsetTypeDecl): (e: TranslationResult<seq<E.Entity>>)
    reads *
  {
    // TODO: handle nonnull types
    var x := TypeConv.AsString(st.Var.Name);
    var ty :- Expr.TranslateType(st.Rhs);
    var constraint :- Expr.TranslateExpression(st.Constraint);
    var wit :- Expr.TranslateOptionalExpression(st.Witness);
    var ei :- TranslateTopLevelEntityInfo(st);
    Success([E.Entity.Type(ei, E.Type.SubsetType(E.SubsetType.SubsetType(x, ty, constraint, wit, false)))])
  }

  function TranslateOpaqueTypeDecl(ot: C.OpaqueTypeDecl): (e: TranslationResult<E.Type>)
    reads *
  {
    Success(E.Type.AbstractType(E.AbstractType.AbstractType()))
  }

  function TranslateNewtypeDecl(nt: C.NewtypeDecl): (e: TranslationResult<E.Type>)
    reads *
  {
    var ty :- Expr.TranslateType(nt.BaseType);
    if IsNull(nt.Var) || IsNull(nt.Constraint) then
      Success(E.Type.TypeAlias(E.TypeAlias.TypeAlias(ty, true)))
    else
      var x := TypeConv.AsString(nt.Var.Name);
      var constraint :- Expr.TranslateExpression(nt.Constraint);
      var wit :- Expr.TranslateOptionalExpression(nt.Witness);
    Success(E.Type.SubsetType(E.SubsetType.SubsetType(x, ty, constraint, wit, true)))
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
      TranslateName(t.AsTraitType.FullName));
    Success(E.Type.TraitType(E.TraitType.TraitType(parentTraits)))
  }

  function TranslateClassDecl(c: C.ClassDecl): (e: TranslationResult<E.Type>)
    reads *
  {
    var parentTraits :- Seq.MapResult(ListUtils.ToSeq(c.ParentTraits), (t: C.Type) reads * =>
      TranslateName(t.AsTraitType.FullName));
    Success(E.Type.ClassType(E.ClassType.ClassType(parentTraits)))
  }

  function TranslateTopLevelEntityInfo(tl: C.TopLevelDecl): (e: TranslationResult<E.EntityInfo>)
    reads *
  {
    var name :- TranslateName(tl.FullName);
    var attrs :- TranslateAttributes(tl.Attributes);
    var loc := L.TranslateLocation(tl.tok);
    Success(E.EntityInfo(name, location := loc, attrs := attrs, members := []))
  }

  function TranslateTopLevelEntityInfoMembers(tl: C.TopLevelDeclWithMembers): (e: TranslationResult<(seq<E.Entity>, E.EntityInfo)>)
    reads *
  {
    var name :- TranslateName(tl.FullName);
    var attrs :- TranslateAttributes(tl.Attributes);
    var loc := L.TranslateLocation(tl.tok);
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
                 var prefix := "Unsupported top level declaration type for " +
                   TypeConv.AsString(tl.FullName);
                 Success(E.Type.Unsupported(TranslateUnsupported(tl, prefix)));
    var topEntity := E.Entity.Type(ei, top);
    Success([topEntity] + members)
  }

  function TranslateTopLevelDecl(tl: C.TopLevelDecl): (exps: TranslationResult<seq<E.Entity>>)
    reads *
    decreases ASTHeight(tl), 0
  {
    if tl is C.TopLevelDeclWithMembers then
      TranslateTopLevelDeclWithMembers(tl)
    else if tl is C.SubsetTypeDecl then
      TranslateSubsetTypeDecl(tl)
    else if tl is C.TypeSynonymDecl then
      TranslateTypeSynonymDecl(tl)
    else if tl is C.LiteralModuleDecl then
      var md := tl as C.LiteralModuleDecl;
      assume {:axiom} {:axiom} ASTHeight(md.ModuleDef) < ASTHeight(tl);
      TranslateModule(md.ModuleDef)
    else
      var ei :- TranslateTopLevelEntityInfo(tl);
      var un :- TranslateUnsupportedDecl(ei, tl);
      Success([un])
  }

  function TranslateUnsupportedDecl(ei: E.EntityInfo, d: C.Declaration)
    : (exps: TranslationResult<E.Entity>)
    reads *
    decreases ASTHeight(d), 0, ()
  {
    var prefix := "Unsupported declaration (" + TypeConv.AsString(d.Name) + ")";
    var un := TranslateUnsupported(d, prefix);
    Success(E.Entity.Unsupported(ei, un))
  }

  function TranslateModule(def: C.ModuleDefinition): (m: TranslationResult<seq<E.Entity>>)
    reads *
    decreases ASTHeight(def), 1
  {
    if def.tok is C.IncludeToken then
      Success([])
    else
      var name :- TranslateName(def.FullName);
      var attrs :- TranslateAttributes(def.Attributes);
      var loc := L.TranslateLocation(def.tok);
      var includes := ListUtils.ToSeq(def.Includes);
      var topLevels := ListUtils.ToSeq(def.TopLevelDecls);
      var topDecls :- Seq.MapResult(topLevels,
        (tl: C.TopLevelDecl) reads * =>
          assume {:axiom} {:axiom} ASTHeight(tl) < ASTHeight(def);
          TranslateTopLevelDecl(tl));
      var topDecls' := Seq.Flatten(topDecls);
      var topAndBelowNames := Seq.Map((d: E.Entity) => d.ei.name, topDecls');
      var topNames := Seq.Filter(topAndBelowNames, (n:N.Name) => n.ChildOf(name));
      var ei := E.EntityInfo(name, location := loc, attrs := attrs, members := topNames);
      var mod := E.Entity.Module(ei, E.Module.Module());
      Success([mod] + topDecls')
  }

  function TranslateProgram(p: C.Program, nameonly includeCompileModules: bool := true): (exps: TranslationResult<E.Program>)
    reads *
  {
    var moduleDefs := ListUtils.ToSeq(p.CompileModules);
    var entities :- Seq.MapResult(moduleDefs,
      (def: C.ModuleDefinition) reads * => TranslateModule(def));
    var flatEntities := Seq.Flatten(entities);
    var inclEntities := if includeCompileModules then
                          flatEntities
                        else
                          Seq.Filter(flatEntities, (e: E.Entity) => !e.ei.name.IsCompile());
    var names := Seq.Map((e: E.Entity) => e.ei.name, inclEntities);
    var topNames := Seq.Filter(names, (n:N.Name) => n.Name? && n.parent.Anonymous?);
    :- Need(forall nm <- topNames :: nm.ChildOf(N.Anonymous), Invalid("Malformed name at top level"));
    var rootEI := E.EntityInfo.EntityInfo(N.Name.Anonymous, location := Location.EMPTY(), attrs := [], members := topNames);
    var root := E.Entity.Module(rootEI, E.Module.Module());
    var regMap := Seq.FoldL((m:map<N.Name, E.Entity>, e: E.Entity) => m + map[e.ei.name := e], map[], [root] + inclEntities);
    var mainMethodName :- if IsNull(p.MainMethod) then
                            Success(None)
                          else
                            var methodName :- TranslateName(p.MainMethod.FullName);
                            Success(Some(methodName));
    var defaultModuleName :- TranslateName(p.DefaultModule.FullName);
    var reg := E.Registry_.Registry(regMap);
    match reg.Validate() {
      case Pass =>
        var prog := E.Program(reg, defaultModule := defaultModuleName, mainMethod := mainMethodName);
        if prog.Valid?() then Success(prog) else Failure(Invalid("Generated invalid program"))
      case Fail(errs) =>
        var msg := Seq.Flatten(Seq.Interleave("\n", Seq.Map((e: E.ValidationError) => e.ToString(), errs)));
        Failure(Invalid("Failed to validate registry:\n" + msg))
    }
  }
}
