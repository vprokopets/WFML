package clafer;

/*** BNFC-Generated Visitor Design Pattern Skeleton. ***/

/* This implements the common visitor design pattern.
   Tests show it to be slightly less efficient than the
   instanceof method, but easier to use.
   Replace the R and A parameters with the desired return
   and context types.*/

public class VisitSkel
{
  public class ModuleVisitor<R,A> implements clafer.Absyn.Module.Visitor<R,A>
  {
    public R visit(clafer.Absyn.ModuleX p, A arg)
    { /* Code for ModuleX goes here */
      for (clafer.Absyn.Declaration x: p.listdeclaration_) {
        x.accept(new DeclarationVisitor<R,A>(), arg);
      }
      return null;
    }
  }
  public class DeclarationVisitor<R,A> implements clafer.Absyn.Declaration.Visitor<R,A>
  {
    public R visit(clafer.Absyn.EnumDecl p, A arg)
    { /* Code for EnumDecl goes here */
      //p.posident_;
      for (clafer.Absyn.EnumId x: p.listenumid_) {
        x.accept(new EnumIdVisitor<R,A>(), arg);
      }
      return null;
    }
    public R visit(clafer.Absyn.ElementDecl p, A arg)
    { /* Code for ElementDecl goes here */
      p.element_.accept(new ElementVisitor<R,A>(), arg);
      return null;
    }
  }
  public class ClaferVisitor<R,A> implements clafer.Absyn.Clafer.Visitor<R,A>
  {
    public R visit(clafer.Absyn.ClaferX p, A arg)
    { /* Code for ClaferX goes here */
      p.abstract_.accept(new AbstractVisitor<R,A>(), arg);
      for (clafer.Absyn.TempModifier x: p.listtempmodifier_) {
        x.accept(new TempModifierVisitor<R,A>(), arg);
      }
      p.gcard_.accept(new GCardVisitor<R,A>(), arg);
      //p.posident_;
      p.super_.accept(new SuperVisitor<R,A>(), arg);
      p.reference_.accept(new ReferenceVisitor<R,A>(), arg);
      p.card_.accept(new CardVisitor<R,A>(), arg);
      p.init_.accept(new InitVisitor<R,A>(), arg);
      p.transition_.accept(new TransitionVisitor<R,A>(), arg);
      p.elements_.accept(new ElementsVisitor<R,A>(), arg);
      return null;
    }
  }
  public class ConstraintVisitor<R,A> implements clafer.Absyn.Constraint.Visitor<R,A>
  {
    public R visit(clafer.Absyn.ConstraintX p, A arg)
    { /* Code for ConstraintX goes here */
      for (clafer.Absyn.Exp x: p.listexp_) {
        x.accept(new ExpVisitor<R,A>(), arg);
      }
      return null;
    }
  }
  public class AssertionVisitor<R,A> implements clafer.Absyn.Assertion.Visitor<R,A>
  {
    public R visit(clafer.Absyn.AssertionX p, A arg)
    { /* Code for AssertionX goes here */
      for (clafer.Absyn.Exp x: p.listexp_) {
        x.accept(new ExpVisitor<R,A>(), arg);
      }
      return null;
    }
  }
  public class GoalVisitor<R,A> implements clafer.Absyn.Goal.Visitor<R,A>
  {
    public R visit(clafer.Absyn.GoalMinDeprecated p, A arg)
    { /* Code for GoalMinDeprecated goes here */
      for (clafer.Absyn.Exp x: p.listexp_) {
        x.accept(new ExpVisitor<R,A>(), arg);
      }
      return null;
    }
    public R visit(clafer.Absyn.GoalMaxDeprecated p, A arg)
    { /* Code for GoalMaxDeprecated goes here */
      for (clafer.Absyn.Exp x: p.listexp_) {
        x.accept(new ExpVisitor<R,A>(), arg);
      }
      return null;
    }
    public R visit(clafer.Absyn.GoalMinimize p, A arg)
    { /* Code for GoalMinimize goes here */
      for (clafer.Absyn.Exp x: p.listexp_) {
        x.accept(new ExpVisitor<R,A>(), arg);
      }
      return null;
    }
    public R visit(clafer.Absyn.GoalMaximize p, A arg)
    { /* Code for GoalMaximize goes here */
      for (clafer.Absyn.Exp x: p.listexp_) {
        x.accept(new ExpVisitor<R,A>(), arg);
      }
      return null;
    }
  }
  public class TempModifierVisitor<R,A> implements clafer.Absyn.TempModifier.Visitor<R,A>
  {
    public R visit(clafer.Absyn.Initial p, A arg)
    { /* Code for Initial goes here */
      return null;
    }
    public R visit(clafer.Absyn.Final p, A arg)
    { /* Code for Final goes here */
      return null;
    }
    public R visit(clafer.Absyn.FinalRef p, A arg)
    { /* Code for FinalRef goes here */
      return null;
    }
    public R visit(clafer.Absyn.FinalTarget p, A arg)
    { /* Code for FinalTarget goes here */
      return null;
    }
  }
  public class TransitionVisitor<R,A> implements clafer.Absyn.Transition.Visitor<R,A>
  {
    public R visit(clafer.Absyn.TransitionEmpty p, A arg)
    { /* Code for TransitionEmpty goes here */
      return null;
    }
    public R visit(clafer.Absyn.TransitionX p, A arg)
    { /* Code for TransitionX goes here */
      p.transarrow_.accept(new TransArrowVisitor<R,A>(), arg);
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
  }
  public class AbstractVisitor<R,A> implements clafer.Absyn.Abstract.Visitor<R,A>
  {
    public R visit(clafer.Absyn.AbstractEmpty p, A arg)
    { /* Code for AbstractEmpty goes here */
      return null;
    }
    public R visit(clafer.Absyn.AbstractX p, A arg)
    { /* Code for AbstractX goes here */
      return null;
    }
  }
  public class ElementsVisitor<R,A> implements clafer.Absyn.Elements.Visitor<R,A>
  {
    public R visit(clafer.Absyn.ElementsEmpty p, A arg)
    { /* Code for ElementsEmpty goes here */
      return null;
    }
    public R visit(clafer.Absyn.ElementsList p, A arg)
    { /* Code for ElementsList goes here */
      for (clafer.Absyn.Element x: p.listelement_) {
        x.accept(new ElementVisitor<R,A>(), arg);
      }
      return null;
    }
  }
  public class ElementVisitor<R,A> implements clafer.Absyn.Element.Visitor<R,A>
  {
    public R visit(clafer.Absyn.Subclafer p, A arg)
    { /* Code for Subclafer goes here */
      p.clafer_.accept(new ClaferVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.ClaferUse p, A arg)
    { /* Code for ClaferUse goes here */
      p.name_.accept(new NameVisitor<R,A>(), arg);
      p.card_.accept(new CardVisitor<R,A>(), arg);
      p.elements_.accept(new ElementsVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.Subconstraint p, A arg)
    { /* Code for Subconstraint goes here */
      p.constraint_.accept(new ConstraintVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.Subgoal p, A arg)
    { /* Code for Subgoal goes here */
      p.goal_.accept(new GoalVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.SubAssertion p, A arg)
    { /* Code for SubAssertion goes here */
      p.assertion_.accept(new AssertionVisitor<R,A>(), arg);
      return null;
    }
  }
  public class SuperVisitor<R,A> implements clafer.Absyn.Super.Visitor<R,A>
  {
    public R visit(clafer.Absyn.SuperEmpty p, A arg)
    { /* Code for SuperEmpty goes here */
      return null;
    }
    public R visit(clafer.Absyn.SuperSome p, A arg)
    { /* Code for SuperSome goes here */
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
  }
  public class ReferenceVisitor<R,A> implements clafer.Absyn.Reference.Visitor<R,A>
  {
    public R visit(clafer.Absyn.ReferenceEmpty p, A arg)
    { /* Code for ReferenceEmpty goes here */
      return null;
    }
    public R visit(clafer.Absyn.ReferenceSet p, A arg)
    { /* Code for ReferenceSet goes here */
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.ReferenceBag p, A arg)
    { /* Code for ReferenceBag goes here */
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
  }
  public class InitVisitor<R,A> implements clafer.Absyn.Init.Visitor<R,A>
  {
    public R visit(clafer.Absyn.InitEmpty p, A arg)
    { /* Code for InitEmpty goes here */
      return null;
    }
    public R visit(clafer.Absyn.InitSome p, A arg)
    { /* Code for InitSome goes here */
      p.inithow_.accept(new InitHowVisitor<R,A>(), arg);
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
  }
  public class InitHowVisitor<R,A> implements clafer.Absyn.InitHow.Visitor<R,A>
  {
    public R visit(clafer.Absyn.InitConstant p, A arg)
    { /* Code for InitConstant goes here */
      return null;
    }
    public R visit(clafer.Absyn.InitDefault p, A arg)
    { /* Code for InitDefault goes here */
      return null;
    }
  }
  public class GCardVisitor<R,A> implements clafer.Absyn.GCard.Visitor<R,A>
  {
    public R visit(clafer.Absyn.GCardEmpty p, A arg)
    { /* Code for GCardEmpty goes here */
      return null;
    }
    public R visit(clafer.Absyn.GCardXor p, A arg)
    { /* Code for GCardXor goes here */
      return null;
    }
    public R visit(clafer.Absyn.GCardOr p, A arg)
    { /* Code for GCardOr goes here */
      return null;
    }
    public R visit(clafer.Absyn.GCardMux p, A arg)
    { /* Code for GCardMux goes here */
      return null;
    }
    public R visit(clafer.Absyn.GCardOpt p, A arg)
    { /* Code for GCardOpt goes here */
      return null;
    }
    public R visit(clafer.Absyn.GCardInterval p, A arg)
    { /* Code for GCardInterval goes here */
      p.ncard_.accept(new NCardVisitor<R,A>(), arg);
      return null;
    }
  }
  public class CardVisitor<R,A> implements clafer.Absyn.Card.Visitor<R,A>
  {
    public R visit(clafer.Absyn.CardEmpty p, A arg)
    { /* Code for CardEmpty goes here */
      return null;
    }
    public R visit(clafer.Absyn.CardLone p, A arg)
    { /* Code for CardLone goes here */
      return null;
    }
    public R visit(clafer.Absyn.CardSome p, A arg)
    { /* Code for CardSome goes here */
      return null;
    }
    public R visit(clafer.Absyn.CardAny p, A arg)
    { /* Code for CardAny goes here */
      return null;
    }
    public R visit(clafer.Absyn.CardNum p, A arg)
    { /* Code for CardNum goes here */
      //p.posinteger_;
      return null;
    }
    public R visit(clafer.Absyn.CardInterval p, A arg)
    { /* Code for CardInterval goes here */
      p.ncard_.accept(new NCardVisitor<R,A>(), arg);
      return null;
    }
  }
  public class NCardVisitor<R,A> implements clafer.Absyn.NCard.Visitor<R,A>
  {
    public R visit(clafer.Absyn.NCardX p, A arg)
    { /* Code for NCardX goes here */
      //p.posinteger_;
      p.exinteger_.accept(new ExIntegerVisitor<R,A>(), arg);
      return null;
    }
  }
  public class ExIntegerVisitor<R,A> implements clafer.Absyn.ExInteger.Visitor<R,A>
  {
    public R visit(clafer.Absyn.ExIntegerAst p, A arg)
    { /* Code for ExIntegerAst goes here */
      return null;
    }
    public R visit(clafer.Absyn.ExIntegerNum p, A arg)
    { /* Code for ExIntegerNum goes here */
      //p.posinteger_;
      return null;
    }
  }
  public class NameVisitor<R,A> implements clafer.Absyn.Name.Visitor<R,A>
  {
    public R visit(clafer.Absyn.Path p, A arg)
    { /* Code for Path goes here */
      for (clafer.Absyn.ModId x: p.listmodid_) {
        x.accept(new ModIdVisitor<R,A>(), arg);
      }
      return null;
    }
  }
  public class ExpVisitor<R,A> implements clafer.Absyn.Exp.Visitor<R,A>
  {
    public R visit(clafer.Absyn.TransitionExp p, A arg)
    { /* Code for TransitionExp goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.transarrow_.accept(new TransArrowVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.EDeclAllDisj p, A arg)
    { /* Code for EDeclAllDisj goes here */
      p.decl_.accept(new DeclVisitor<R,A>(), arg);
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.EDeclAll p, A arg)
    { /* Code for EDeclAll goes here */
      p.decl_.accept(new DeclVisitor<R,A>(), arg);
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.EDeclQuantDisj p, A arg)
    { /* Code for EDeclQuantDisj goes here */
      p.quant_.accept(new QuantVisitor<R,A>(), arg);
      p.decl_.accept(new DeclVisitor<R,A>(), arg);
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.EDeclQuant p, A arg)
    { /* Code for EDeclQuant goes here */
      p.quant_.accept(new QuantVisitor<R,A>(), arg);
      p.decl_.accept(new DeclVisitor<R,A>(), arg);
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.EImpliesElse p, A arg)
    { /* Code for EImpliesElse goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      p.exp_3.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.LetExp p, A arg)
    { /* Code for LetExp goes here */
      p.varbinding_.accept(new VarBindingVisitor<R,A>(), arg);
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.TmpPatNever p, A arg)
    { /* Code for TmpPatNever goes here */
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      p.patternscope_.accept(new PatternScopeVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.TmpPatSometime p, A arg)
    { /* Code for TmpPatSometime goes here */
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      p.patternscope_.accept(new PatternScopeVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.TmpPatLessOrOnce p, A arg)
    { /* Code for TmpPatLessOrOnce goes here */
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      p.patternscope_.accept(new PatternScopeVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.TmpPatAlways p, A arg)
    { /* Code for TmpPatAlways goes here */
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      p.patternscope_.accept(new PatternScopeVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.TmpPatPrecede p, A arg)
    { /* Code for TmpPatPrecede goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      p.patternscope_.accept(new PatternScopeVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.TmpPatFollow p, A arg)
    { /* Code for TmpPatFollow goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      p.patternscope_.accept(new PatternScopeVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.TmpInitially p, A arg)
    { /* Code for TmpInitially goes here */
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.TmpFinally p, A arg)
    { /* Code for TmpFinally goes here */
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.EIff p, A arg)
    { /* Code for EIff goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.EImplies p, A arg)
    { /* Code for EImplies goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.EOr p, A arg)
    { /* Code for EOr goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.EXor p, A arg)
    { /* Code for EXor goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.EAnd p, A arg)
    { /* Code for EAnd goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.LtlU p, A arg)
    { /* Code for LtlU goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.TmpUntil p, A arg)
    { /* Code for TmpUntil goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.LtlW p, A arg)
    { /* Code for LtlW goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.TmpWUntil p, A arg)
    { /* Code for TmpWUntil goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.LtlF p, A arg)
    { /* Code for LtlF goes here */
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.TmpEventually p, A arg)
    { /* Code for TmpEventually goes here */
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.LtlG p, A arg)
    { /* Code for LtlG goes here */
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.TmpGlobally p, A arg)
    { /* Code for TmpGlobally goes here */
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.LtlX p, A arg)
    { /* Code for LtlX goes here */
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.TmpNext p, A arg)
    { /* Code for TmpNext goes here */
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.ENeg p, A arg)
    { /* Code for ENeg goes here */
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.ELt p, A arg)
    { /* Code for ELt goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.EGt p, A arg)
    { /* Code for EGt goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.EEq p, A arg)
    { /* Code for EEq goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.ELte p, A arg)
    { /* Code for ELte goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.EGte p, A arg)
    { /* Code for EGte goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.ENeq p, A arg)
    { /* Code for ENeq goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.EIn p, A arg)
    { /* Code for EIn goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.ENin p, A arg)
    { /* Code for ENin goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.EQuantExp p, A arg)
    { /* Code for EQuantExp goes here */
      p.quant_.accept(new QuantVisitor<R,A>(), arg);
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.EAdd p, A arg)
    { /* Code for EAdd goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.ESub p, A arg)
    { /* Code for ESub goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.EMul p, A arg)
    { /* Code for EMul goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.EDiv p, A arg)
    { /* Code for EDiv goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.ERem p, A arg)
    { /* Code for ERem goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.EGMax p, A arg)
    { /* Code for EGMax goes here */
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.EGMin p, A arg)
    { /* Code for EGMin goes here */
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.ESum p, A arg)
    { /* Code for ESum goes here */
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.EProd p, A arg)
    { /* Code for EProd goes here */
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.ECard p, A arg)
    { /* Code for ECard goes here */
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.EMinExp p, A arg)
    { /* Code for EMinExp goes here */
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.EDomain p, A arg)
    { /* Code for EDomain goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.ERange p, A arg)
    { /* Code for ERange goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.EUnion p, A arg)
    { /* Code for EUnion goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.EUnionCom p, A arg)
    { /* Code for EUnionCom goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.EDifference p, A arg)
    { /* Code for EDifference goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.EIntersection p, A arg)
    { /* Code for EIntersection goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.EIntersectionDeprecated p, A arg)
    { /* Code for EIntersectionDeprecated goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.EJoin p, A arg)
    { /* Code for EJoin goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.ClaferId p, A arg)
    { /* Code for ClaferId goes here */
      p.name_.accept(new NameVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.EInt p, A arg)
    { /* Code for EInt goes here */
      //p.posinteger_;
      return null;
    }
    public R visit(clafer.Absyn.EDouble p, A arg)
    { /* Code for EDouble goes here */
      //p.posdouble_;
      return null;
    }
    public R visit(clafer.Absyn.EReal p, A arg)
    { /* Code for EReal goes here */
      //p.posreal_;
      return null;
    }
    public R visit(clafer.Absyn.EStr p, A arg)
    { /* Code for EStr goes here */
      //p.posstring_;
      return null;
    }
  }
  public class TransGuardVisitor<R,A> implements clafer.Absyn.TransGuard.Visitor<R,A>
  {
    public R visit(clafer.Absyn.TransGuardX p, A arg)
    { /* Code for TransGuardX goes here */
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
  }
  public class TransArrowVisitor<R,A> implements clafer.Absyn.TransArrow.Visitor<R,A>
  {
    public R visit(clafer.Absyn.SyncTransArrow p, A arg)
    { /* Code for SyncTransArrow goes here */
      return null;
    }
    public R visit(clafer.Absyn.GuardedSyncTransArrow p, A arg)
    { /* Code for GuardedSyncTransArrow goes here */
      p.transguard_.accept(new TransGuardVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.NextTransArrow p, A arg)
    { /* Code for NextTransArrow goes here */
      return null;
    }
    public R visit(clafer.Absyn.GuardedNextTransArrow p, A arg)
    { /* Code for GuardedNextTransArrow goes here */
      p.transguard_.accept(new TransGuardVisitor<R,A>(), arg);
      return null;
    }
  }
  public class PatternScopeVisitor<R,A> implements clafer.Absyn.PatternScope.Visitor<R,A>
  {
    public R visit(clafer.Absyn.PatScopeBefore p, A arg)
    { /* Code for PatScopeBefore goes here */
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.PatScopeAfter p, A arg)
    { /* Code for PatScopeAfter goes here */
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.PatScopeBetweenAnd p, A arg)
    { /* Code for PatScopeBetweenAnd goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.PatScopeAfterUntil p, A arg)
    { /* Code for PatScopeAfterUntil goes here */
      p.exp_1.accept(new ExpVisitor<R,A>(), arg);
      p.exp_2.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
    public R visit(clafer.Absyn.PatScopeEmpty p, A arg)
    { /* Code for PatScopeEmpty goes here */
      return null;
    }
  }
  public class DeclVisitor<R,A> implements clafer.Absyn.Decl.Visitor<R,A>
  {
    public R visit(clafer.Absyn.DeclX p, A arg)
    { /* Code for DeclX goes here */
      for (clafer.Absyn.LocId x: p.listlocid_) {
        x.accept(new LocIdVisitor<R,A>(), arg);
      }
      p.exp_.accept(new ExpVisitor<R,A>(), arg);
      return null;
    }
  }
  public class VarBindingVisitor<R,A> implements clafer.Absyn.VarBinding.Visitor<R,A>
  {
    public R visit(clafer.Absyn.VarBindingX p, A arg)
    { /* Code for VarBindingX goes here */
      p.locid_.accept(new LocIdVisitor<R,A>(), arg);
      p.name_.accept(new NameVisitor<R,A>(), arg);
      return null;
    }
  }
  public class QuantVisitor<R,A> implements clafer.Absyn.Quant.Visitor<R,A>
  {
    public R visit(clafer.Absyn.QuantNo p, A arg)
    { /* Code for QuantNo goes here */
      return null;
    }
    public R visit(clafer.Absyn.QuantNot p, A arg)
    { /* Code for QuantNot goes here */
      return null;
    }
    public R visit(clafer.Absyn.QuantLone p, A arg)
    { /* Code for QuantLone goes here */
      return null;
    }
    public R visit(clafer.Absyn.QuantOne p, A arg)
    { /* Code for QuantOne goes here */
      return null;
    }
    public R visit(clafer.Absyn.QuantSome p, A arg)
    { /* Code for QuantSome goes here */
      return null;
    }
  }
  public class EnumIdVisitor<R,A> implements clafer.Absyn.EnumId.Visitor<R,A>
  {
    public R visit(clafer.Absyn.EnumIdIdent p, A arg)
    { /* Code for EnumIdIdent goes here */
      //p.posident_;
      return null;
    }
  }
  public class ModIdVisitor<R,A> implements clafer.Absyn.ModId.Visitor<R,A>
  {
    public R visit(clafer.Absyn.ModIdIdent p, A arg)
    { /* Code for ModIdIdent goes here */
      //p.posident_;
      return null;
    }
  }
  public class LocIdVisitor<R,A> implements clafer.Absyn.LocId.Visitor<R,A>
  {
    public R visit(clafer.Absyn.LocIdIdent p, A arg)
    { /* Code for LocIdIdent goes here */
      //p.posident_;
      return null;
    }
  }
}
