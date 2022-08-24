include "../AST/Entities.dfy"
include "../Utils/Library.dfy"

module {:options "-functionSyntax:4"} Bootstrap.Debug.Entities {
  import Utils.Lib.Seq
  import Utils.Lib.Str
  import opened AST.Names
  import opened AST.Entities

  datatype RegistryPrinter = RegistryPrinter(registry: Registry) {
    static const INDENT := "  ";

    static function Paragraph(title: string, indent: string): string {
      indent + "- " + title + ": "
    }

    static function Title(title: string, indent: string): string {
      indent + "== " + title + " ==\n"
    }

    static function Subtitle(title: string, indent: string): string {
      indent + " - " + title + " -\n"
    }

    static method DumpEntityHeader(ei: EntityInfo, indent: string) {
      print Title(ei.name.ToString(), indent);
      DumpEntityAttributes(ei.attrs, indent);
    }

    static method DumpEntityAttributes(attrs: seq<Attribute>, indent: string) {
      if attrs != [] {
        print indent, "- Attributes: ",
          Str.Join(" ", Seq.Map((at: Attribute) => at.ToString(), attrs)),
          "\n";
      }
    }

    method DumpEntity(name: Name, indent: string)
      requires registry.Contains(name)
      decreases registry.TransitiveMembers(name), 0
    {
      var entity := registry.Get(name);
      DumpEntityHeader(entity.ei, indent);
      print Subtitle("Members", indent);
      registry.Decreases_TransitiveMembersOfMany(entity.ei);
      DumpEntities(entity.ei.members, indent + INDENT);
    }

    method DumpEntities(names: seq<Name>, indent: string)
      requires forall name <- names :: registry.Contains(name)
      decreases registry.TransitiveMembersOfMany(names), 1
    {
      for i := 0 to |names| {
        var name := names[i];
        registry.Decreases_TransitiveMembers(names, name);
        DumpEntity(name, indent);
        print "\n";
      }
    }

    method DumpEntitiesFlat() {
      var names := registry.entities.Keys;
      while |names| > 0
        invariant names <= registry.entities.Keys
      {
        var name :| name in names;
        DumpEntity(name, indent := "");
        names := names - {name};
      }
    }
  }

  method DumpProgram(p: Program) {
    RegistryPrinter(p.registry).DumpEntity(p.defaultModule, indent := "");
  }
}
