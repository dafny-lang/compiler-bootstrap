---
date: 2022-06-27
authors: @cpitclaudel, @sonmarcho
---

# Dafny-in-Dafny AST design notes: Bind, scopes, and variable declarations

This note explores different possible representations for variable bindings in the Dafny-in-Dafny AST.
Our initial design used traditional let-bindings (the first model described below), but it does not line up well with the way most of our target languages think about variable declarations and assignments,

To illustrate, consider the following running example:

```dafny
method Main() {
  var x := 1;
  var y := true;
  print x, " ", y, "\n";   // 1, true
  {
    x := 2;
    var x := 3;
    y := false;
    print x, " ", y, "\n"; // 3, false
  }
  print x, " ", y, "\n";   // 2, false
}
```

This piece of code prints `1, true`, `3, false`, `2, false`.
In Dafny's existing AST, each of these `var` is a ``VarDecl`` statement.
How do we model this example in Dafny-in-Dafny?

## Models of Dafny's semantics

### Let bindings

In this model each `var` introduces a new scope; we represent this in the AST with a single ``Bind`` mode:

```dafny
| Bind(vars: seq<string>, vals: seq<string>, body: Expr)
```

In the code below, I've indicated this by adding double braces to mark implicit scopes introduced by `var`s.
Note that I have removed the original scope markers (the single braces in the example above), because their only contribution was determining how far the `var x` extended.

```dafny
method Main() {
  {{ var x := 1;
     {{ var y := true;
        print x, " ", y, "\n";
        x := 2;
        {{ var x := 3;
           y := false;
           print x, " ", y, "\n";
        }}
        print x, " ", y, "\n";
     }}
  }}
}
```

This model has relatively simple operational semantics: entering a `var`'s scope creates a snapshot of the current context (the map of variable values), and exiting the `var`'s scope restores the previous context, plus any mutations to variables that were not bound by the `var`.
This is made possible by the fact that each `var` creates nesting in the AST, so an operational semantics can run code when entering and existing the scope.

```dafny
method Main() {       //     Init: map[]
  var x := 1; {{      // Snapshot: map[]
                      //   Update: map[x := 1]
     {{ // Snapshot: map[x := ] var y := true;
                      //   Update: map[x := 1, y := true]
      x := 2;         //   Update: map[x := 2, y := true]
       {{  // Snapshot: map[x := 2, y := tru] var x := 3;
                      //   Update: map[x := 3, y := true]
        y := false;   //   Update: map[x := 3, y := false]
      }}              //  Restore: map[x := 2, y := false]
    }}                //  Restore: map[x := 2]
  }}                  //  Restore: map[]
}
```

### Stack of contexts

Here `var` does not create any nesting structure in the AST.
Instead we have two separate nodes: one for scopes, and one for introducing variables.

```dafny
| Scope(body: Expr)
| VarDecl(var: string, val: Expr)
```

The operational semantics keeps track not of one set of variables (one context), but instead of a stack of contexts.
Entering a scope creates a new (empty) context on the stack, and ``VarDecl``s within that scope then create entries in the newly created context at the top of the stack.

```dafny
method Main() {  // Init:       [map[]]
  var x := 1;    // Decl:       [map[x := _]]
                 // Update:     [map[x := 1]]
  var y := true; // Decl:       [map[x := 1, y := _]]
                 // Update:     [map[x := 1, y := true ]]
  {              // Push scope: [map[x := 1, y := true ], map[]]
    x := 2;      // Update:     [map[x := 2, y := true ], map[]]
    var x := 3;  // Decl:       [map[x := 2, y := true ], map[x := _]]
                 // Update:     [map[x := 2, y := true ], map[x := 3]]
    y := false;  // Update:     [map[x := 2, y := false], map[x := 3]]
  }              // Pop scope:  [map[x := 2, y := false]]
}
```

### Stack of scopes

Initially we thought that it might be possible to simplify the semantics of the model above by tracking only which variables were being declared in each scope while keeping track of a single context (we would have create snapshots of each set of variable and of the single context when entering a scope and restored it when leaving), like this:

```dafny
method Main() {  // Init:       map[] {}
  var x := 1;    // Decl:       map[] {x}
                 // Update:     map[x := 1] {x}
  var y := true; // Decl:       map[x := 1] {x, y}
                 // Update:     map[x := 1, y := true ] {x, y}
  {              // Snapshot:   map[x := 1, y := true ] {x, y}
                 // Enter:      map[x := 1, y := true ] {}
    x := 2;      // Update:     map[x := 2, y := true ]
    var x := 3;  // Decl:       map[x := 2, y := true ] {x}
                 // Update:     map[x := 3, y := true ] {x}
    y := false;  // Update:     map[x := 3, y := false] {x}
  }              // Restore:    !!
}
```

The problem comes when attempting to restore: we know that we need to restore `x`, since it was ``VarDecl``-d within the scope (as indicated by the `{x}` set), but we don't know which value to restore it to (since the `2` was overwritten).

### Nonlocal contexts (pessimistic transactions)

This is a simplification of the operational semantics of the stack-of-contexts model.

The operational semantics keeps track of a pair of contexts: nonlocal variables, and local variables.
Entering a scope merges the nonlocal and local contexts to create a new nonlocal context and continues with an empty local context, and exiting the scope discards the local context and propagates changes made to the nonlocal context into the original local and nonlocal contexts.
``VarDecl``s create entries in the local context.

```dafny
method Main() {  // Init:       map[], map[]
  var x := 1;    // Decl:       map[], map[x := _]
                 // Update:     map[], map[x := 1]
  var y := true; // Decl:       map[], map[x := 1, y := _]
                 // Update:     map[], map[x := 1, y := true ]
  {              // Push scope:        map[x := 1, y := true ], map[]
    x := 2;      // Update:            map[x := 2, y := true ], map[]
    var x := 3;  // Decl:              map[x := 2, y := true ], map[x := _]
                 // Update:            map[x := 2, y := true ], map[x := 3]
    y := false;  // Update:            map[x := 2, y := false], map[x := 3]
  }              // Pop scope:  map[], map[x := 2, y := false]
}
```

This example does not do a great job of demonstrating what happens when we leave a scope, so here is another example:

```dafny
              // Init:       map[x := 1, y := true ], map[x := 2]
{             // Push scope:                          map[x := 2, y := true ], map[]
  x := 3;     // Update:                              map[x := 3, y := false], map[]
  y := false; // Update:                              map[x := 3, y := false], map[]
  var x := 4; // Decl:                                map[x := 3, y := false], map[x := _]
              // Update:                              map[x := 3, y := false], map[x := 4]
}             // Pop scope:  map[x := 1, y := false], map[x := 3]
```

The relation between this model and the "stack-of-contexts" one is this:

    nonlocals == ∪_{i < |stack|} stack[i]
    locals    == stack[^1]

I believe the "pop scope" rule is this:

    locals    := locals    + (nonlocals' & locals.Keys)
    nonlocals := nonlocals + (nonlocals' & nonlocals.Keys - locals.Keys)

That is, update the locals according to the new nonlocals map, and update nonlocals according to that same map, but only for those values not already found in the locals.

### Rollback contexts (optimistic transactions)

Another simplification of stack-of-contexts model (by @sonmarcho).
We can augment the “let-binding” model with a “rollback” context that keeps a copy of the values of variables re-declared in the current scope.

In the example below, the first context matches the “current context” from the “let-binding” model, and the second context records the old values for variables redeclared in the current scope.

```dafny
method Main() {  // Init:       map[], map[]
  var x := 1;    // Decl:       map[x := _], map[]
                 // Update:     map[x := 1], map[]
  var y := true; // Decl:       map[x := 1, y := _], map[]
                 // Update:     map[x := 1, y := true ], map[]
  {              // Push scope: map[x := 1, y := true ], map[]
    x := 2;      // Update:     map[x := 2, y := true ], map[]
    var x := 3;  // Decl:       map[x := _, y := true ], map[x := 2]
                 // Update:     map[x := 3, y := true ], map[x := 2]
    y := false;  // Update:     map[x := 3, y := false], map[x := 2]
  }              // Pop scope:  map[x := 2, y := false], map[]
}
```

The advantage of this model is that all the lookups/updates are performed in the *current* context:

```dafny
lookup x scopes ≡ scopes.current[x]
```

While in the pair-of-contexts proposal, we have:

```dafny
lookup x scopes ≡
  if x in scopes.locals then scopes.locals[x]
  else scopes.nonlocals[x]
```

The *old* context is only used for book-keeping:

- it is updated when declaring a variable, to remember the current value of the variable from  the outer scope(s) (if any)
- it is read when popping a scope, to reset the variables which were re-declared in the current scope

Pushing a scope does the following:

```
current := current // current is left unchanged
old := []
```

Popping a scope does the following:

```
current := (current' & current.Keys) + old'
                    (1)                (2)
old := old // old is left unchanged
```

That is:

1. Restrict the new current context to the domain of the previous current context.
2. Reset the variables which were redeclared in the new scope.

## Chosing a model and an AST representation

The first model (where each `var` also creates a scope that extends to cover the region of the code that this `var` dominates) is convenient because it leads to very simple semantics.
Unfortunately, it is not ideal for ideal for compilation, because it introduces unnecessary nesting (curly braces) if translated naively to, say, C#:

```c#
void Main() {
  { var x = 1; // !
    { var y = true; // !
      Console.Write(x, " ", y, "\n");
      x = 2;
      { var x = 3;
        y = false;
        Console.Write(x, " ", y, "\n");
      }
      Console.Write(x, " ", y, "\n");
    }
  }
}
```

The two scopes marked `// !` are not necessary, and we would like to eliminate them before we pretty-print to C#.
In the ``Bind`` model, however, there is not straightforward way to eliminate the curly braces.

In contrast, even though they have more complicated operational semantics, the various multi-contexts models captures precisely where braces need to be introduced.

On the other hand, the stack-of-contexts model also introduces difficulties: since some constructs induce scopes in Dafny (like the branches of an `if`, or the body of a `while`), we have to ensure that there are `Scope` nodes in various places.

The stack-of-context model requires more complex semantics for lookups and updates, making it less desirable than the two pairs-of-contexts models.  between those there is no clear winner, but the optimistic model has simpler update semantics, so we decided to use that one.

## Note on name collisions

All of these issues stem from having name collisions: if we renamed all variables first, or if we used a nameless representation, then there would be no need for scopes at all, and we could use the ``Bind`` model without ever printing braces.

We are keeping variable names (for now) for readability purposes.  We might introduce a nameless part of the AST later on if it makes transformations easier.
