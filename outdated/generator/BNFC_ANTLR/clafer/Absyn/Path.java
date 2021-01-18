package clafer.Absyn; // Java Package generated by the BNF Converter.

public class Path  extends Name {
  public final ListModId listmodid_;
  public Path(ListModId p1) { listmodid_ = p1; }

  public <R,A> R accept(clafer.Absyn.Name.Visitor<R,A> v, A arg) { return v.visit(this, arg); }

  public boolean equals(java.lang.Object o) {
    if (this == o) return true;
    if (o instanceof clafer.Absyn.Path) {
      clafer.Absyn.Path x = (clafer.Absyn.Path)o;
      return this.listmodid_.equals(x.listmodid_);
    }
    return false;
  }

  public int hashCode() {
    return this.listmodid_.hashCode();
  }


}
