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

    method DumpEntity(e: Entity, indent: string)
      requires e.ei.name in registry.entities
      decreases registry.SuffixesOf(e.ei.name), 0
    {
      registry.Decreases_SuffixesOfMany(e.ei);
      DumpEntityHeader(e.ei, indent);
      print Subtitle("Members", indent);
      DumpEntities(e.ei.members, indent + INDENT);
    }

    method DumpEntities(names: seq<Name>, indent: string)
      decreases registry.SuffixesOfMany(names), 1
    {
      for i := 0 to |names| {
        var name := names[i];
        match registry.Find(name)
          case None =>
            print indent, "!! Name not found:", name, "\n";
          case Some(e) =>
            registry.Decreases_SuffixesOf(names, name);
            DumpEntity(e, indent);
        print "\n";
      }
    }

    method DumpEntitiesFlat() {
      var names := registry.entities.Keys;
      while |names| > 0
        invariant names <= registry.entities.Keys
      {
        var name :| name in names;
        DumpEntity(registry.entities[name], indent := "");
        names := names - {name};
      }
    }
  }
}
