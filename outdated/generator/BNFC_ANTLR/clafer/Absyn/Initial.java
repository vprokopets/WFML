package clafer.Absyn; // Java Package generated by the BNF Converter.

public class Initial  extends TempModifier {
  public Initial() { }

  public <R,A> R accept(clafer.Absyn.TempModifier.Visitor<R,A> v, A arg) { return v.visit(this, arg); }

  public boolean equals(java.lang.Object o) {
    if (this == o) return true;
    if (o instanceof clafer.Absyn.Initial) {
      return true;
    }
    return false;
  }

  public int hashCode() {
    return 37;
  }


}
