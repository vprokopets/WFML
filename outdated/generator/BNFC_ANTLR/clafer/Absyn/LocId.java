package clafer.Absyn; // Java Package generated by the BNF Converter.

public abstract class LocId implements java.io.Serializable {
  public abstract <R,A> R accept(LocId.Visitor<R,A> v, A arg);
  public interface Visitor <R,A> {
    public R visit(clafer.Absyn.LocIdIdent p, A arg);

  }

}
