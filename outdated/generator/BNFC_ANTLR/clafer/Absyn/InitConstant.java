package clafer.Absyn; // Java Package generated by the BNF Converter.

public class InitConstant  extends InitHow {
  public InitConstant() { }

  public <R,A> R accept(clafer.Absyn.InitHow.Visitor<R,A> v, A arg) { return v.visit(this, arg); }

  public boolean equals(java.lang.Object o) {
    if (this == o) return true;
    if (o instanceof clafer.Absyn.InitConstant) {
      return true;
    }
    return false;
  }

  public int hashCode() {
    return 37;
  }


}
