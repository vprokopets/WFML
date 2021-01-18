package clafer.Absyn; // Java Package generated by the BNF Converter.

public class GuardedSyncTransArrow  extends TransArrow {
  public final TransGuard transguard_;
  public GuardedSyncTransArrow(TransGuard p1) { transguard_ = p1; }

  public <R,A> R accept(clafer.Absyn.TransArrow.Visitor<R,A> v, A arg) { return v.visit(this, arg); }

  public boolean equals(java.lang.Object o) {
    if (this == o) return true;
    if (o instanceof clafer.Absyn.GuardedSyncTransArrow) {
      clafer.Absyn.GuardedSyncTransArrow x = (clafer.Absyn.GuardedSyncTransArrow)o;
      return this.transguard_.equals(x.transguard_);
    }
    return false;
  }

  public int hashCode() {
    return this.transguard_.hashCode();
  }


}
