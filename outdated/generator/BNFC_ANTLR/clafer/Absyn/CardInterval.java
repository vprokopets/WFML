package clafer.Absyn; // Java Package generated by the BNF Converter.

public class CardInterval  extends Card {
  public final NCard ncard_;
  public CardInterval(NCard p1) { ncard_ = p1; }

  public <R,A> R accept(clafer.Absyn.Card.Visitor<R,A> v, A arg) { return v.visit(this, arg); }

  public boolean equals(java.lang.Object o) {
    if (this == o) return true;
    if (o instanceof clafer.Absyn.CardInterval) {
      clafer.Absyn.CardInterval x = (clafer.Absyn.CardInterval)o;
      return this.ncard_.equals(x.ncard_);
    }
    return false;
  }

  public int hashCode() {
    return this.ncard_.hashCode();
  }


}
