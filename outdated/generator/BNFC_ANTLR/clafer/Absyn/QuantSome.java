package clafer.Absyn; // Java Package generated by the BNF Converter.

public class QuantSome  extends Quant {
  public QuantSome() { }

  public <R,A> R accept(clafer.Absyn.Quant.Visitor<R,A> v, A arg) { return v.visit(this, arg); }

  public boolean equals(java.lang.Object o) {
    if (this == o) return true;
    if (o instanceof clafer.Absyn.QuantSome) {
      return true;
    }
    return false;
  }

  public int hashCode() {
    return 37;
  }


}
