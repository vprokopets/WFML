package clafer.Absyn; // Java Package generated by the BNF Converter.

public class TmpPatAlways  extends Exp {
  public final Exp exp_;
  public final PatternScope patternscope_;
  public TmpPatAlways(Exp p1, PatternScope p2) { exp_ = p1; patternscope_ = p2; }

  public <R,A> R accept(clafer.Absyn.Exp.Visitor<R,A> v, A arg) { return v.visit(this, arg); }

  public boolean equals(java.lang.Object o) {
    if (this == o) return true;
    if (o instanceof clafer.Absyn.TmpPatAlways) {
      clafer.Absyn.TmpPatAlways x = (clafer.Absyn.TmpPatAlways)o;
      return this.exp_.equals(x.exp_) && this.patternscope_.equals(x.patternscope_);
    }
    return false;
  }

  public int hashCode() {
    return 37*(this.exp_.hashCode())+this.patternscope_.hashCode();
  }


}
