package clafer.Absyn; // Java Package generated by the BNF Converter.

public abstract class TransArrow implements java.io.Serializable {
  public abstract <R,A> R accept(TransArrow.Visitor<R,A> v, A arg);
  public interface Visitor <R,A> {
    public R visit(clafer.Absyn.SyncTransArrow p, A arg);
    public R visit(clafer.Absyn.GuardedSyncTransArrow p, A arg);
    public R visit(clafer.Absyn.NextTransArrow p, A arg);
    public R visit(clafer.Absyn.GuardedNextTransArrow p, A arg);

  }

}
