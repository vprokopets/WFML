package clafer;

/** BNFC-Generated All Visitor */

public interface AllVisitor<R,A> extends
  clafer.Absyn.Module.Visitor<R,A>,
  clafer.Absyn.Declaration.Visitor<R,A>,
  clafer.Absyn.Clafer.Visitor<R,A>,
  clafer.Absyn.Constraint.Visitor<R,A>,
  clafer.Absyn.Assertion.Visitor<R,A>,
  clafer.Absyn.Goal.Visitor<R,A>,
  clafer.Absyn.TempModifier.Visitor<R,A>,
  clafer.Absyn.Transition.Visitor<R,A>,
  clafer.Absyn.Abstract.Visitor<R,A>,
  clafer.Absyn.Elements.Visitor<R,A>,
  clafer.Absyn.Element.Visitor<R,A>,
  clafer.Absyn.Super.Visitor<R,A>,
  clafer.Absyn.Reference.Visitor<R,A>,
  clafer.Absyn.Init.Visitor<R,A>,
  clafer.Absyn.InitHow.Visitor<R,A>,
  clafer.Absyn.GCard.Visitor<R,A>,
  clafer.Absyn.Card.Visitor<R,A>,
  clafer.Absyn.NCard.Visitor<R,A>,
  clafer.Absyn.ExInteger.Visitor<R,A>,
  clafer.Absyn.Name.Visitor<R,A>,
  clafer.Absyn.Exp.Visitor<R,A>,
  clafer.Absyn.TransGuard.Visitor<R,A>,
  clafer.Absyn.TransArrow.Visitor<R,A>,
  clafer.Absyn.PatternScope.Visitor<R,A>,
  clafer.Absyn.Decl.Visitor<R,A>,
  clafer.Absyn.VarBinding.Visitor<R,A>,
  clafer.Absyn.Quant.Visitor<R,A>,
  clafer.Absyn.EnumId.Visitor<R,A>,
  clafer.Absyn.ModId.Visitor<R,A>,
  clafer.Absyn.LocId.Visitor<R,A>
{}
