# Modeling Dafny's entity hierarchy in Dafny

## Existing design

Dafny models entities (fields, functions, methods, classes, modules, etc.) as mutable classes.  Names are strings (`FullDafnyName`) constructed recursively as `FullDafnyName = <Name of parent> . <name of child>`.

## Use cases

The following are places where we'd like to use a model of Dafny's hierarchy of entities in the context of Dafny-in-Dafny:

- In the interpreter, to resolve a global function
  `Find: Name → Registry → Entity`

- In the compiler, to apply a transformation over every definition
  `Map: (f: NamedEntity → NamedEntity) → Registry → Registry`
  (Plus some well-formedness criteria)

- In the compiler, to introduce or remove entities
  `Add/Replace: NamedEntity → Registry → Registry`
  `Remove: Name → Registry → Registry`

- In the auditor, to look for entities with certain properties
  `Fold: (Entity → α → α) → Registry → α₀ → α`

- In the compiler, to translate Dafny's hierarchies into target-language hierarchies, such as C# namespaces
  This may require a custom traversal.

- In the compiler, to find the shortest name for an entity in a given context (for a given target language)
  This is out of scope for now, since it depends on the semantics of the target language.

## Existing entities

The following are all Dafny entities that we care to support:

- Modules
- Export sets
- Imports
- Types without members (subset types, type aliases)
- Types with members (abstract type, trait, class, (co)datatype, newtype)
- Definitions (method, function, class constructor, datatype constructor, const, var)

They have the following parent/child relationships:

- Module → Module
- Module → Export set
- Module → Import
- Module → Type
- Type with members → Definition
- Function → Method (in the by method case)

## Reference types vs. value types

Dafny's C# implementation of the entity hierarchy is mutable, with fairly complex pointers between entities.

On the Dafny-in-Dafny side, we would prefer to use only `!new` types.  This is because we want to quantify over some of these entities.  For example, if we make `Method` a class type (as is done in C# Dafny), then we cannot quantify over all methods (which is not too bad), and we cannot include a reference to a method directly in an AST (because variables that are quantified over cannot have a type that may contain references).

On the other hand, using exclusively value types is problematic, too.  That is because sharing is not explicit, so if we have two places in the hierarchy or in an AST that refer to the same entity, we have to update both places (we cannot simply mutate the thing that both of them point to).

## Design proposal

Instead of strings with periods, we'll define a **Name** to be a list of name components (**Atoms**):

```dafny
type Atom = s: string | s != "" && "." !in s
datatype Name = Anonymous | Name(parent: Name, suffix: Atom)
```

The parent-child relationship is captured by the following predicate:

```dafny
predicate Extends(parent: Name, child: Name) {
  child.Name? && child.parent == parent
}
```

**Entities** are constructors of an `Entity` type:

```dafny
datatype Entity =
  | Module(children: seq<Name>)
    // Note: Not separating submodules, exports, and imports in `children`
  | ExportSet(provided: map<Name, Provided|Revealed>)
  | Import(localName: Atom, target: Name)
  | Type(children: seq<Name>, …)
  | Definition(…)
datatype NamedEntity = NamedEntity(n: Name, e: Entity)
```

Note that entities do not contain a name; the name is packaged in the `NamedEntity`.  This makes access to the name of an entity more consistent (there's no need to have a `Name` field in every constructor).

A **registry** is a collection of named entities.  The root of the registry is a module with an empty name.

```
datatype Registry = Registry(entities: map<Name, NamedEntity>) {
  const root := entities[Anonymous];
}
```

### Well-formedness

The definitions above are augmented with criteria capturing well-formedness, including:

- A root module exists (`entities` is non-empty)
- Parent-children relationships are respected (e.g. type can't point to module, import must point to a module)
- Parent-children naming conventions are respected with their parents (see `.Extends` above).
- All names found in the entity graph resolve to an entity (no dangling names).
