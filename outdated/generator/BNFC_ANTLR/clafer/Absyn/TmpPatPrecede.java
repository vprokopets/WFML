package clafer.Absyn; // Java Package generated by the BNF Converter.

public class TmpPatPrecede  extends Exp {
  public final Exp exp_1, exp_2;
  public final PatternScope patternscope_;
  public TmpPatPrecede(Exp p1, Exp p2, PatternScope p3) { exp_1 = p1; exp_2 = p2; patternscope_ = p3; }

  public <R,A> R accept(clafer.Absyn.Exp.Visitor<R,A> v, A arg) { return v.visit(this, arg); }

  public boolean equals(java.lang.Object o) {
    if (this == o) return true;
    if (o instanceof clafer.Absyn.TmpPatPrecede) {
      clafer.Absyn.TmpPatPrecede x = (clafer.Absyn.TmpPatPrecede)o;
      return this.exp_1.equals(x.exp_1) && this.exp_2.equals(x.exp_2) && this.patternscope_.equals(x.patternscope_);
    }
    return false;
  }

  public int hashCode() {
    return 37*(37*(this.exp_1.hashCode())+this.exp_2.hashCode())+this.patternscope_.hashCode();
  }


}
