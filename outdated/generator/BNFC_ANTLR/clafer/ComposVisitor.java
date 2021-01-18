package clafer;
/** BNFC-Generated Composition Visitor
*/

public class ComposVisitor<A> implements
  clafer.Absyn.Module.Visitor<clafer.Absyn.Module,A>,
  clafer.Absyn.Declaration.Visitor<clafer.Absyn.Declaration,A>,
  clafer.Absyn.Clafer.Visitor<clafer.Absyn.Clafer,A>,
  clafer.Absyn.Constraint.Visitor<clafer.Absyn.Constraint,A>,
  clafer.Absyn.Assertion.Visitor<clafer.Absyn.Assertion,A>,
  clafer.Absyn.Goal.Visitor<clafer.Absyn.Goal,A>,
  clafer.Absyn.TempModifier.Visitor<clafer.Absyn.TempModifier,A>,
  clafer.Absyn.Transition.Visitor<clafer.Absyn.Transition,A>,
  clafer.Absyn.Abstract.Visitor<clafer.Absyn.Abstract,A>,
  clafer.Absyn.Elements.Visitor<clafer.Absyn.Elements,A>,
  clafer.Absyn.Element.Visitor<clafer.Absyn.Element,A>,
  clafer.Absyn.Super.Visitor<clafer.Absyn.Super,A>,
  clafer.Absyn.Reference.Visitor<clafer.Absyn.Reference,A>,
  clafer.Absyn.Init.Visitor<clafer.Absyn.Init,A>,
  clafer.Absyn.InitHow.Visitor<clafer.Absyn.InitHow,A>,
  clafer.Absyn.GCard.Visitor<clafer.Absyn.GCard,A>,
  clafer.Absyn.Card.Visitor<clafer.Absyn.Card,A>,
  clafer.Absyn.NCard.Visitor<clafer.Absyn.NCard,A>,
  clafer.Absyn.ExInteger.Visitor<clafer.Absyn.ExInteger,A>,
  clafer.Absyn.Name.Visitor<clafer.Absyn.Name,A>,
  clafer.Absyn.Exp.Visitor<clafer.Absyn.Exp,A>,
  clafer.Absyn.TransGuard.Visitor<clafer.Absyn.TransGuard,A>,
  clafer.Absyn.TransArrow.Visitor<clafer.Absyn.TransArrow,A>,
  clafer.Absyn.PatternScope.Visitor<clafer.Absyn.PatternScope,A>,
  clafer.Absyn.Decl.Visitor<clafer.Absyn.Decl,A>,
  clafer.Absyn.VarBinding.Visitor<clafer.Absyn.VarBinding,A>,
  clafer.Absyn.Quant.Visitor<clafer.Absyn.Quant,A>,
  clafer.Absyn.EnumId.Visitor<clafer.Absyn.EnumId,A>,
  clafer.Absyn.ModId.Visitor<clafer.Absyn.ModId,A>,
  clafer.Absyn.LocId.Visitor<clafer.Absyn.LocId,A>
{
    /* Module */
    public clafer.Absyn.Module visit(clafer.Absyn.ModuleX p, A arg)
    {
      clafer.Absyn.ListDeclaration listdeclaration_ = new clafer.Absyn.ListDeclaration();
      for (clafer.Absyn.Declaration x : p.listdeclaration_)
      {
        listdeclaration_.add(x.accept(this,arg));
      }
      return new clafer.Absyn.ModuleX(listdeclaration_);
    }

    /* Declaration */
    public clafer.Absyn.Declaration visit(clafer.Absyn.EnumDecl p, A arg)
    {
      String posident_ = p.posident_;
      clafer.Absyn.ListEnumId listenumid_ = new clafer.Absyn.ListEnumId();
      for (clafer.Absyn.EnumId x : p.listenumid_)
      {
        listenumid_.add(x.accept(this,arg));
      }
      return new clafer.Absyn.EnumDecl(posident_, listenumid_);
    }
    public clafer.Absyn.Declaration visit(clafer.Absyn.ElementDecl p, A arg)
    {
      clafer.Absyn.Element element_ = p.element_.accept(this, arg);
      return new clafer.Absyn.ElementDecl(element_);
    }

    /* Clafer */
    public clafer.Absyn.Clafer visit(clafer.Absyn.ClaferX p, A arg)
    {
      clafer.Absyn.Abstract abstract_ = p.abstract_.accept(this, arg);
      clafer.Absyn.ListTempModifier listtempmodifier_ = new clafer.Absyn.ListTempModifier();
      for (clafer.Absyn.TempModifier x : p.listtempmodifier_)
      {
        listtempmodifier_.add(x.accept(this,arg));
      }
      clafer.Absyn.GCard gcard_ = p.gcard_.accept(this, arg);
      String posident_ = p.posident_;
      clafer.Absyn.Super super_ = p.super_.accept(this, arg);
      clafer.Absyn.Reference reference_ = p.reference_.accept(this, arg);
      clafer.Absyn.Card card_ = p.card_.accept(this, arg);
      clafer.Absyn.Init init_ = p.init_.accept(this, arg);
      clafer.Absyn.Transition transition_ = p.transition_.accept(this, arg);
      clafer.Absyn.Elements elements_ = p.elements_.accept(this, arg);
      return new clafer.Absyn.ClaferX(abstract_, listtempmodifier_, gcard_, posident_, super_, reference_, card_, init_, transition_, elements_);
    }

    /* Constraint */
    public clafer.Absyn.Constraint visit(clafer.Absyn.ConstraintX p, A arg)
    {
      clafer.Absyn.ListExp listexp_ = new clafer.Absyn.ListExp();
      for (clafer.Absyn.Exp x : p.listexp_)
      {
        listexp_.add(x.accept(this,arg));
      }
      return new clafer.Absyn.ConstraintX(listexp_);
    }

    /* Assertion */
    public clafer.Absyn.Assertion visit(clafer.Absyn.AssertionX p, A arg)
    {
      clafer.Absyn.ListExp listexp_ = new clafer.Absyn.ListExp();
      for (clafer.Absyn.Exp x : p.listexp_)
      {
        listexp_.add(x.accept(this,arg));
      }
      return new clafer.Absyn.AssertionX(listexp_);
    }

    /* Goal */
    public clafer.Absyn.Goal visit(clafer.Absyn.GoalMinDeprecated p, A arg)
    {
      clafer.Absyn.ListExp listexp_ = new clafer.Absyn.ListExp();
      for (clafer.Absyn.Exp x : p.listexp_)
      {
        listexp_.add(x.accept(this,arg));
      }
      return new clafer.Absyn.GoalMinDeprecated(listexp_);
    }
    public clafer.Absyn.Goal visit(clafer.Absyn.GoalMaxDeprecated p, A arg)
    {
      clafer.Absyn.ListExp listexp_ = new clafer.Absyn.ListExp();
      for (clafer.Absyn.Exp x : p.listexp_)
      {
        listexp_.add(x.accept(this,arg));
      }
      return new clafer.Absyn.GoalMaxDeprecated(listexp_);
    }
    public clafer.Absyn.Goal visit(clafer.Absyn.GoalMinimize p, A arg)
    {
      clafer.Absyn.ListExp listexp_ = new clafer.Absyn.ListExp();
      for (clafer.Absyn.Exp x : p.listexp_)
      {
        listexp_.add(x.accept(this,arg));
      }
      return new clafer.Absyn.GoalMinimize(listexp_);
    }
    public clafer.Absyn.Goal visit(clafer.Absyn.GoalMaximize p, A arg)
    {
      clafer.Absyn.ListExp listexp_ = new clafer.Absyn.ListExp();
      for (clafer.Absyn.Exp x : p.listexp_)
      {
        listexp_.add(x.accept(this,arg));
      }
      return new clafer.Absyn.GoalMaximize(listexp_);
    }

    /* TempModifier */
    public clafer.Absyn.TempModifier visit(clafer.Absyn.Initial p, A arg)
    {
      return new clafer.Absyn.Initial();
    }
    public clafer.Absyn.TempModifier visit(clafer.Absyn.Final p, A arg)
    {
      return new clafer.Absyn.Final();
    }
    public clafer.Absyn.TempModifier visit(clafer.Absyn.FinalRef p, A arg)
    {
      return new clafer.Absyn.FinalRef();
    }
    public clafer.Absyn.TempModifier visit(clafer.Absyn.FinalTarget p, A arg)
    {
      return new clafer.Absyn.FinalTarget();
    }

    /* Transition */
    public clafer.Absyn.Transition visit(clafer.Absyn.TransitionEmpty p, A arg)
    {
      return new clafer.Absyn.TransitionEmpty();
    }
    public clafer.Absyn.Transition visit(clafer.Absyn.TransitionX p, A arg)
    {
      clafer.Absyn.TransArrow transarrow_ = p.transarrow_.accept(this, arg);
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      return new clafer.Absyn.TransitionX(transarrow_, exp_);
    }

    /* Abstract */
    public clafer.Absyn.Abstract visit(clafer.Absyn.AbstractEmpty p, A arg)
    {
      return new clafer.Absyn.AbstractEmpty();
    }
    public clafer.Absyn.Abstract visit(clafer.Absyn.AbstractX p, A arg)
    {
      return new clafer.Absyn.AbstractX();
    }

    /* Elements */
    public clafer.Absyn.Elements visit(clafer.Absyn.ElementsEmpty p, A arg)
    {
      return new clafer.Absyn.ElementsEmpty();
    }
    public clafer.Absyn.Elements visit(clafer.Absyn.ElementsList p, A arg)
    {
      clafer.Absyn.ListElement listelement_ = new clafer.Absyn.ListElement();
      for (clafer.Absyn.Element x : p.listelement_)
      {
        listelement_.add(x.accept(this,arg));
      }
      return new clafer.Absyn.ElementsList(listelement_);
    }

    /* Element */
    public clafer.Absyn.Element visit(clafer.Absyn.Subclafer p, A arg)
    {
      clafer.Absyn.Clafer clafer_ = p.clafer_.accept(this, arg);
      return new clafer.Absyn.Subclafer(clafer_);
    }
    public clafer.Absyn.Element visit(clafer.Absyn.ClaferUse p, A arg)
    {
      clafer.Absyn.Name name_ = p.name_.accept(this, arg);
      clafer.Absyn.Card card_ = p.card_.accept(this, arg);
      clafer.Absyn.Elements elements_ = p.elements_.accept(this, arg);
      return new clafer.Absyn.ClaferUse(name_, card_, elements_);
    }
    public clafer.Absyn.Element visit(clafer.Absyn.Subconstraint p, A arg)
    {
      clafer.Absyn.Constraint constraint_ = p.constraint_.accept(this, arg);
      return new clafer.Absyn.Subconstraint(constraint_);
    }
    public clafer.Absyn.Element visit(clafer.Absyn.Subgoal p, A arg)
    {
      clafer.Absyn.Goal goal_ = p.goal_.accept(this, arg);
      return new clafer.Absyn.Subgoal(goal_);
    }
    public clafer.Absyn.Element visit(clafer.Absyn.SubAssertion p, A arg)
    {
      clafer.Absyn.Assertion assertion_ = p.assertion_.accept(this, arg);
      return new clafer.Absyn.SubAssertion(assertion_);
    }

    /* Super */
    public clafer.Absyn.Super visit(clafer.Absyn.SuperEmpty p, A arg)
    {
      return new clafer.Absyn.SuperEmpty();
    }
    public clafer.Absyn.Super visit(clafer.Absyn.SuperSome p, A arg)
    {
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      return new clafer.Absyn.SuperSome(exp_);
    }

    /* Reference */
    public clafer.Absyn.Reference visit(clafer.Absyn.ReferenceEmpty p, A arg)
    {
      return new clafer.Absyn.ReferenceEmpty();
    }
    public clafer.Absyn.Reference visit(clafer.Absyn.ReferenceSet p, A arg)
    {
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      return new clafer.Absyn.ReferenceSet(exp_);
    }
    public clafer.Absyn.Reference visit(clafer.Absyn.ReferenceBag p, A arg)
    {
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      return new clafer.Absyn.ReferenceBag(exp_);
    }

    /* Init */
    public clafer.Absyn.Init visit(clafer.Absyn.InitEmpty p, A arg)
    {
      return new clafer.Absyn.InitEmpty();
    }
    public clafer.Absyn.Init visit(clafer.Absyn.InitSome p, A arg)
    {
      clafer.Absyn.InitHow inithow_ = p.inithow_.accept(this, arg);
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      return new clafer.Absyn.InitSome(inithow_, exp_);
    }

    /* InitHow */
    public clafer.Absyn.InitHow visit(clafer.Absyn.InitConstant p, A arg)
    {
      return new clafer.Absyn.InitConstant();
    }
    public clafer.Absyn.InitHow visit(clafer.Absyn.InitDefault p, A arg)
    {
      return new clafer.Absyn.InitDefault();
    }

    /* GCard */
    public clafer.Absyn.GCard visit(clafer.Absyn.GCardEmpty p, A arg)
    {
      return new clafer.Absyn.GCardEmpty();
    }
    public clafer.Absyn.GCard visit(clafer.Absyn.GCardXor p, A arg)
    {
      return new clafer.Absyn.GCardXor();
    }
    public clafer.Absyn.GCard visit(clafer.Absyn.GCardOr p, A arg)
    {
      return new clafer.Absyn.GCardOr();
    }
    public clafer.Absyn.GCard visit(clafer.Absyn.GCardMux p, A arg)
    {
      return new clafer.Absyn.GCardMux();
    }
    public clafer.Absyn.GCard visit(clafer.Absyn.GCardOpt p, A arg)
    {
      return new clafer.Absyn.GCardOpt();
    }
    public clafer.Absyn.GCard visit(clafer.Absyn.GCardInterval p, A arg)
    {
      clafer.Absyn.NCard ncard_ = p.ncard_.accept(this, arg);
      return new clafer.Absyn.GCardInterval(ncard_);
    }

    /* Card */
    public clafer.Absyn.Card visit(clafer.Absyn.CardEmpty p, A arg)
    {
      return new clafer.Absyn.CardEmpty();
    }
    public clafer.Absyn.Card visit(clafer.Absyn.CardLone p, A arg)
    {
      return new clafer.Absyn.CardLone();
    }
    public clafer.Absyn.Card visit(clafer.Absyn.CardSome p, A arg)
    {
      return new clafer.Absyn.CardSome();
    }
    public clafer.Absyn.Card visit(clafer.Absyn.CardAny p, A arg)
    {
      return new clafer.Absyn.CardAny();
    }
    public clafer.Absyn.Card visit(clafer.Absyn.CardNum p, A arg)
    {
      String posinteger_ = p.posinteger_;
      return new clafer.Absyn.CardNum(posinteger_);
    }
    public clafer.Absyn.Card visit(clafer.Absyn.CardInterval p, A arg)
    {
      clafer.Absyn.NCard ncard_ = p.ncard_.accept(this, arg);
      return new clafer.Absyn.CardInterval(ncard_);
    }

    /* NCard */
    public clafer.Absyn.NCard visit(clafer.Absyn.NCardX p, A arg)
    {
      String posinteger_ = p.posinteger_;
      clafer.Absyn.ExInteger exinteger_ = p.exinteger_.accept(this, arg);
      return new clafer.Absyn.NCardX(posinteger_, exinteger_);
    }

    /* ExInteger */
    public clafer.Absyn.ExInteger visit(clafer.Absyn.ExIntegerAst p, A arg)
    {
      return new clafer.Absyn.ExIntegerAst();
    }
    public clafer.Absyn.ExInteger visit(clafer.Absyn.ExIntegerNum p, A arg)
    {
      String posinteger_ = p.posinteger_;
      return new clafer.Absyn.ExIntegerNum(posinteger_);
    }

    /* Name */
    public clafer.Absyn.Name visit(clafer.Absyn.Path p, A arg)
    {
      clafer.Absyn.ListModId listmodid_ = new clafer.Absyn.ListModId();
      for (clafer.Absyn.ModId x : p.listmodid_)
      {
        listmodid_.add(x.accept(this,arg));
      }
      return new clafer.Absyn.Path(listmodid_);
    }

    /* Exp */
    public clafer.Absyn.Exp visit(clafer.Absyn.TransitionExp p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.TransArrow transarrow_ = p.transarrow_.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.TransitionExp(exp_1, transarrow_, exp_2);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EDeclAllDisj p, A arg)
    {
      clafer.Absyn.Decl decl_ = p.decl_.accept(this, arg);
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      return new clafer.Absyn.EDeclAllDisj(decl_, exp_);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EDeclAll p, A arg)
    {
      clafer.Absyn.Decl decl_ = p.decl_.accept(this, arg);
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      return new clafer.Absyn.EDeclAll(decl_, exp_);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EDeclQuantDisj p, A arg)
    {
      clafer.Absyn.Quant quant_ = p.quant_.accept(this, arg);
      clafer.Absyn.Decl decl_ = p.decl_.accept(this, arg);
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      return new clafer.Absyn.EDeclQuantDisj(quant_, decl_, exp_);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EDeclQuant p, A arg)
    {
      clafer.Absyn.Quant quant_ = p.quant_.accept(this, arg);
      clafer.Absyn.Decl decl_ = p.decl_.accept(this, arg);
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      return new clafer.Absyn.EDeclQuant(quant_, decl_, exp_);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EImpliesElse p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      clafer.Absyn.Exp exp_3 = p.exp_3.accept(this, arg);
      return new clafer.Absyn.EImpliesElse(exp_1, exp_2, exp_3);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.LetExp p, A arg)
    {
      clafer.Absyn.VarBinding varbinding_ = p.varbinding_.accept(this, arg);
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      return new clafer.Absyn.LetExp(varbinding_, exp_);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.TmpPatNever p, A arg)
    {
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      clafer.Absyn.PatternScope patternscope_ = p.patternscope_.accept(this, arg);
      return new clafer.Absyn.TmpPatNever(exp_, patternscope_);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.TmpPatSometime p, A arg)
    {
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      clafer.Absyn.PatternScope patternscope_ = p.patternscope_.accept(this, arg);
      return new clafer.Absyn.TmpPatSometime(exp_, patternscope_);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.TmpPatLessOrOnce p, A arg)
    {
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      clafer.Absyn.PatternScope patternscope_ = p.patternscope_.accept(this, arg);
      return new clafer.Absyn.TmpPatLessOrOnce(exp_, patternscope_);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.TmpPatAlways p, A arg)
    {
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      clafer.Absyn.PatternScope patternscope_ = p.patternscope_.accept(this, arg);
      return new clafer.Absyn.TmpPatAlways(exp_, patternscope_);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.TmpPatPrecede p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      clafer.Absyn.PatternScope patternscope_ = p.patternscope_.accept(this, arg);
      return new clafer.Absyn.TmpPatPrecede(exp_1, exp_2, patternscope_);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.TmpPatFollow p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      clafer.Absyn.PatternScope patternscope_ = p.patternscope_.accept(this, arg);
      return new clafer.Absyn.TmpPatFollow(exp_1, exp_2, patternscope_);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.TmpInitially p, A arg)
    {
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      return new clafer.Absyn.TmpInitially(exp_);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.TmpFinally p, A arg)
    {
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      return new clafer.Absyn.TmpFinally(exp_);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EIff p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.EIff(exp_1, exp_2);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EImplies p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.EImplies(exp_1, exp_2);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EOr p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.EOr(exp_1, exp_2);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EXor p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.EXor(exp_1, exp_2);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EAnd p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.EAnd(exp_1, exp_2);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.LtlU p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.LtlU(exp_1, exp_2);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.TmpUntil p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.TmpUntil(exp_1, exp_2);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.LtlW p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.LtlW(exp_1, exp_2);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.TmpWUntil p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.TmpWUntil(exp_1, exp_2);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.LtlF p, A arg)
    {
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      return new clafer.Absyn.LtlF(exp_);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.TmpEventually p, A arg)
    {
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      return new clafer.Absyn.TmpEventually(exp_);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.LtlG p, A arg)
    {
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      return new clafer.Absyn.LtlG(exp_);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.TmpGlobally p, A arg)
    {
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      return new clafer.Absyn.TmpGlobally(exp_);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.LtlX p, A arg)
    {
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      return new clafer.Absyn.LtlX(exp_);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.TmpNext p, A arg)
    {
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      return new clafer.Absyn.TmpNext(exp_);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.ENeg p, A arg)
    {
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      return new clafer.Absyn.ENeg(exp_);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.ELt p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.ELt(exp_1, exp_2);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EGt p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.EGt(exp_1, exp_2);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EEq p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.EEq(exp_1, exp_2);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.ELte p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.ELte(exp_1, exp_2);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EGte p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.EGte(exp_1, exp_2);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.ENeq p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.ENeq(exp_1, exp_2);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EIn p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.EIn(exp_1, exp_2);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.ENin p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.ENin(exp_1, exp_2);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EQuantExp p, A arg)
    {
      clafer.Absyn.Quant quant_ = p.quant_.accept(this, arg);
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      return new clafer.Absyn.EQuantExp(quant_, exp_);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EAdd p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.EAdd(exp_1, exp_2);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.ESub p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.ESub(exp_1, exp_2);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EMul p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.EMul(exp_1, exp_2);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EDiv p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.EDiv(exp_1, exp_2);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.ERem p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.ERem(exp_1, exp_2);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EGMax p, A arg)
    {
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      return new clafer.Absyn.EGMax(exp_);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EGMin p, A arg)
    {
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      return new clafer.Absyn.EGMin(exp_);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.ESum p, A arg)
    {
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      return new clafer.Absyn.ESum(exp_);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EProd p, A arg)
    {
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      return new clafer.Absyn.EProd(exp_);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.ECard p, A arg)
    {
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      return new clafer.Absyn.ECard(exp_);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EMinExp p, A arg)
    {
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      return new clafer.Absyn.EMinExp(exp_);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EDomain p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.EDomain(exp_1, exp_2);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.ERange p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.ERange(exp_1, exp_2);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EUnion p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.EUnion(exp_1, exp_2);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EUnionCom p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.EUnionCom(exp_1, exp_2);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EDifference p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.EDifference(exp_1, exp_2);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EIntersection p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.EIntersection(exp_1, exp_2);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EIntersectionDeprecated p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.EIntersectionDeprecated(exp_1, exp_2);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EJoin p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.EJoin(exp_1, exp_2);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.ClaferId p, A arg)
    {
      clafer.Absyn.Name name_ = p.name_.accept(this, arg);
      return new clafer.Absyn.ClaferId(name_);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EInt p, A arg)
    {
      String posinteger_ = p.posinteger_;
      return new clafer.Absyn.EInt(posinteger_);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EDouble p, A arg)
    {
      String posdouble_ = p.posdouble_;
      return new clafer.Absyn.EDouble(posdouble_);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EReal p, A arg)
    {
      String posreal_ = p.posreal_;
      return new clafer.Absyn.EReal(posreal_);
    }
    public clafer.Absyn.Exp visit(clafer.Absyn.EStr p, A arg)
    {
      String posstring_ = p.posstring_;
      return new clafer.Absyn.EStr(posstring_);
    }

    /* TransGuard */
    public clafer.Absyn.TransGuard visit(clafer.Absyn.TransGuardX p, A arg)
    {
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      return new clafer.Absyn.TransGuardX(exp_);
    }

    /* TransArrow */
    public clafer.Absyn.TransArrow visit(clafer.Absyn.SyncTransArrow p, A arg)
    {
      return new clafer.Absyn.SyncTransArrow();
    }
    public clafer.Absyn.TransArrow visit(clafer.Absyn.GuardedSyncTransArrow p, A arg)
    {
      clafer.Absyn.TransGuard transguard_ = p.transguard_.accept(this, arg);
      return new clafer.Absyn.GuardedSyncTransArrow(transguard_);
    }
    public clafer.Absyn.TransArrow visit(clafer.Absyn.NextTransArrow p, A arg)
    {
      return new clafer.Absyn.NextTransArrow();
    }
    public clafer.Absyn.TransArrow visit(clafer.Absyn.GuardedNextTransArrow p, A arg)
    {
      clafer.Absyn.TransGuard transguard_ = p.transguard_.accept(this, arg);
      return new clafer.Absyn.GuardedNextTransArrow(transguard_);
    }

    /* PatternScope */
    public clafer.Absyn.PatternScope visit(clafer.Absyn.PatScopeBefore p, A arg)
    {
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      return new clafer.Absyn.PatScopeBefore(exp_);
    }
    public clafer.Absyn.PatternScope visit(clafer.Absyn.PatScopeAfter p, A arg)
    {
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      return new clafer.Absyn.PatScopeAfter(exp_);
    }
    public clafer.Absyn.PatternScope visit(clafer.Absyn.PatScopeBetweenAnd p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.PatScopeBetweenAnd(exp_1, exp_2);
    }
    public clafer.Absyn.PatternScope visit(clafer.Absyn.PatScopeAfterUntil p, A arg)
    {
      clafer.Absyn.Exp exp_1 = p.exp_1.accept(this, arg);
      clafer.Absyn.Exp exp_2 = p.exp_2.accept(this, arg);
      return new clafer.Absyn.PatScopeAfterUntil(exp_1, exp_2);
    }
    public clafer.Absyn.PatternScope visit(clafer.Absyn.PatScopeEmpty p, A arg)
    {
      return new clafer.Absyn.PatScopeEmpty();
    }

    /* Decl */
    public clafer.Absyn.Decl visit(clafer.Absyn.DeclX p, A arg)
    {
      clafer.Absyn.ListLocId listlocid_ = new clafer.Absyn.ListLocId();
      for (clafer.Absyn.LocId x : p.listlocid_)
      {
        listlocid_.add(x.accept(this,arg));
      }
      clafer.Absyn.Exp exp_ = p.exp_.accept(this, arg);
      return new clafer.Absyn.DeclX(listlocid_, exp_);
    }

    /* VarBinding */
    public clafer.Absyn.VarBinding visit(clafer.Absyn.VarBindingX p, A arg)
    {
      clafer.Absyn.LocId locid_ = p.locid_.accept(this, arg);
      clafer.Absyn.Name name_ = p.name_.accept(this, arg);
      return new clafer.Absyn.VarBindingX(locid_, name_);
    }

    /* Quant */
    public clafer.Absyn.Quant visit(clafer.Absyn.QuantNo p, A arg)
    {
      return new clafer.Absyn.QuantNo();
    }
    public clafer.Absyn.Quant visit(clafer.Absyn.QuantNot p, A arg)
    {
      return new clafer.Absyn.QuantNot();
    }
    public clafer.Absyn.Quant visit(clafer.Absyn.QuantLone p, A arg)
    {
      return new clafer.Absyn.QuantLone();
    }
    public clafer.Absyn.Quant visit(clafer.Absyn.QuantOne p, A arg)
    {
      return new clafer.Absyn.QuantOne();
    }
    public clafer.Absyn.Quant visit(clafer.Absyn.QuantSome p, A arg)
    {
      return new clafer.Absyn.QuantSome();
    }

    /* EnumId */
    public clafer.Absyn.EnumId visit(clafer.Absyn.EnumIdIdent p, A arg)
    {
      String posident_ = p.posident_;
      return new clafer.Absyn.EnumIdIdent(posident_);
    }

    /* ModId */
    public clafer.Absyn.ModId visit(clafer.Absyn.ModIdIdent p, A arg)
    {
      String posident_ = p.posident_;
      return new clafer.Absyn.ModIdIdent(posident_);
    }

    /* LocId */
    public clafer.Absyn.LocId visit(clafer.Absyn.LocIdIdent p, A arg)
    {
      String posident_ = p.posident_;
      return new clafer.Absyn.LocIdIdent(posident_);
    }
}
