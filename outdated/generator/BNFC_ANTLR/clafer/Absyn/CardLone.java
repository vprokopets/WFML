package clafer.Absyn; // Java Package generated by the BNF Converter.

public class CardLone  extends Card {
  public CardLone() { }

  public <R,A> R accept(clafer.Absyn.Card.Visitor<R,A> v, A arg) { return v.visit(this, arg); }

  public boolean equals(java.lang.Object o) {
    if (this == o) return true;
    if (o instanceof clafer.Absyn.CardLone) {
      return true;
    }
    return false;
  }

  public int hashCode() {
    return 37;
  }


}
