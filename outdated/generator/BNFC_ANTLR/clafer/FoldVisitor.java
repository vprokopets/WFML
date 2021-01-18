package clafer;

/** BNFC-Generated Fold Visitor */
public abstract class FoldVisitor<R,A> implements AllVisitor<R,A> {
    public abstract R leaf(A arg);
    public abstract R combine(R x, R y, A arg);

/* Module */
    public R visit(clafer.Absyn.ModuleX p, A arg) {
      R r = leaf(arg);
      for (clafer.Absyn.Declaration x : p.listdeclaration_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      return r;
    }

/* Declaration */
    public R visit(clafer.Absyn.EnumDecl p, A arg) {
      R r = leaf(arg);
      for (clafer.Absyn.EnumId x : p.listenumid_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      return r;
    }
    public R visit(clafer.Absyn.ElementDecl p, A arg) {
      R r = leaf(arg);
      r = combine(p.element_.accept(this, arg), r, arg);
      return r;
    }

/* Clafer */
    public R visit(clafer.Absyn.ClaferX p, A arg) {
      R r = leaf(arg);
      r = combine(p.abstract_.accept(this, arg), r, arg);
      for (clafer.Absyn.TempModifier x : p.listtempmodifier_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      r = combine(p.gcard_.accept(this, arg), r, arg);
      r = combine(p.super_.accept(this, arg), r, arg);
      r = combine(p.reference_.accept(this, arg), r, arg);
      r = combine(p.card_.accept(this, arg), r, arg);
      r = combine(p.init_.accept(this, arg), r, arg);
      r = combine(p.transition_.accept(this, arg), r, arg);
      r = combine(p.elements_.accept(this, arg), r, arg);
      return r;
    }

/* Constraint */
    public R visit(clafer.Absyn.ConstraintX p, A arg) {
      R r = leaf(arg);
      for (clafer.Absyn.Exp x : p.listexp_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      return r;
    }

/* Assertion */
    public R visit(clafer.Absyn.AssertionX p, A arg) {
      R r = leaf(arg);
      for (clafer.Absyn.Exp x : p.listexp_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      return r;
    }

/* Goal */
    public R visit(clafer.Absyn.GoalMinDeprecated p, A arg) {
      R r = leaf(arg);
      for (clafer.Absyn.Exp x : p.listexp_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      return r;
    }
    public R visit(clafer.Absyn.GoalMaxDeprecated p, A arg) {
      R r = leaf(arg);
      for (clafer.Absyn.Exp x : p.listexp_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      return r;
    }
    public R visit(clafer.Absyn.GoalMinimize p, A arg) {
      R r = leaf(arg);
      for (clafer.Absyn.Exp x : p.listexp_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      return r;
    }
    public R visit(clafer.Absyn.GoalMaximize p, A arg) {
      R r = leaf(arg);
      for (clafer.Absyn.Exp x : p.listexp_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      return r;
    }

/* TempModifier */
    public R visit(clafer.Absyn.Initial p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(clafer.Absyn.Final p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(clafer.Absyn.FinalRef p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(clafer.Absyn.FinalTarget p, A arg) {
      R r = leaf(arg);
      return r;
    }

/* Transition */
    public R visit(clafer.Absyn.TransitionEmpty p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(clafer.Absyn.TransitionX p, A arg) {
      R r = leaf(arg);
      r = combine(p.transarrow_.accept(this, arg), r, arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      return r;
    }

/* Abstract */
    public R visit(clafer.Absyn.AbstractEmpty p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(clafer.Absyn.AbstractX p, A arg) {
      R r = leaf(arg);
      return r;
    }

/* Elements */
    public R visit(clafer.Absyn.ElementsEmpty p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(clafer.Absyn.ElementsList p, A arg) {
      R r = leaf(arg);
      for (clafer.Absyn.Element x : p.listelement_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      return r;
    }

/* Element */
    public R visit(clafer.Absyn.Subclafer p, A arg) {
      R r = leaf(arg);
      r = combine(p.clafer_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.ClaferUse p, A arg) {
      R r = leaf(arg);
      r = combine(p.name_.accept(this, arg), r, arg);
      r = combine(p.card_.accept(this, arg), r, arg);
      r = combine(p.elements_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.Subconstraint p, A arg) {
      R r = leaf(arg);
      r = combine(p.constraint_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.Subgoal p, A arg) {
      R r = leaf(arg);
      r = combine(p.goal_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.SubAssertion p, A arg) {
      R r = leaf(arg);
      r = combine(p.assertion_.accept(this, arg), r, arg);
      return r;
    }

/* Super */
    public R visit(clafer.Absyn.SuperEmpty p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(clafer.Absyn.SuperSome p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      return r;
    }

/* Reference */
    public R visit(clafer.Absyn.ReferenceEmpty p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(clafer.Absyn.ReferenceSet p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.ReferenceBag p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      return r;
    }

/* Init */
    public R visit(clafer.Absyn.InitEmpty p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(clafer.Absyn.InitSome p, A arg) {
      R r = leaf(arg);
      r = combine(p.inithow_.accept(this, arg), r, arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      return r;
    }

/* InitHow */
    public R visit(clafer.Absyn.InitConstant p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(clafer.Absyn.InitDefault p, A arg) {
      R r = leaf(arg);
      return r;
    }

/* GCard */
    public R visit(clafer.Absyn.GCardEmpty p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(clafer.Absyn.GCardXor p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(clafer.Absyn.GCardOr p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(clafer.Absyn.GCardMux p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(clafer.Absyn.GCardOpt p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(clafer.Absyn.GCardInterval p, A arg) {
      R r = leaf(arg);
      r = combine(p.ncard_.accept(this, arg), r, arg);
      return r;
    }

/* Card */
    public R visit(clafer.Absyn.CardEmpty p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(clafer.Absyn.CardLone p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(clafer.Absyn.CardSome p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(clafer.Absyn.CardAny p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(clafer.Absyn.CardNum p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(clafer.Absyn.CardInterval p, A arg) {
      R r = leaf(arg);
      r = combine(p.ncard_.accept(this, arg), r, arg);
      return r;
    }

/* NCard */
    public R visit(clafer.Absyn.NCardX p, A arg) {
      R r = leaf(arg);
      r = combine(p.exinteger_.accept(this, arg), r, arg);
      return r;
    }

/* ExInteger */
    public R visit(clafer.Absyn.ExIntegerAst p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(clafer.Absyn.ExIntegerNum p, A arg) {
      R r = leaf(arg);
      return r;
    }

/* Name */
    public R visit(clafer.Absyn.Path p, A arg) {
      R r = leaf(arg);
      for (clafer.Absyn.ModId x : p.listmodid_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      return r;
    }

/* Exp */
    public R visit(clafer.Absyn.TransitionExp p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.transarrow_.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.EDeclAllDisj p, A arg) {
      R r = leaf(arg);
      r = combine(p.decl_.accept(this, arg), r, arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.EDeclAll p, A arg) {
      R r = leaf(arg);
      r = combine(p.decl_.accept(this, arg), r, arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.EDeclQuantDisj p, A arg) {
      R r = leaf(arg);
      r = combine(p.quant_.accept(this, arg), r, arg);
      r = combine(p.decl_.accept(this, arg), r, arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.EDeclQuant p, A arg) {
      R r = leaf(arg);
      r = combine(p.quant_.accept(this, arg), r, arg);
      r = combine(p.decl_.accept(this, arg), r, arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.EImpliesElse p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      r = combine(p.exp_3.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.LetExp p, A arg) {
      R r = leaf(arg);
      r = combine(p.varbinding_.accept(this, arg), r, arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.TmpPatNever p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      r = combine(p.patternscope_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.TmpPatSometime p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      r = combine(p.patternscope_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.TmpPatLessOrOnce p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      r = combine(p.patternscope_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.TmpPatAlways p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      r = combine(p.patternscope_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.TmpPatPrecede p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      r = combine(p.patternscope_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.TmpPatFollow p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      r = combine(p.patternscope_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.TmpInitially p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.TmpFinally p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.EIff p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.EImplies p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.EOr p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.EXor p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.EAnd p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.LtlU p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.TmpUntil p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.LtlW p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.TmpWUntil p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.LtlF p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.TmpEventually p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.LtlG p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.TmpGlobally p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.LtlX p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.TmpNext p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.ENeg p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.ELt p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.EGt p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.EEq p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.ELte p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.EGte p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.ENeq p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.EIn p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.ENin p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.EQuantExp p, A arg) {
      R r = leaf(arg);
      r = combine(p.quant_.accept(this, arg), r, arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.EAdd p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.ESub p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.EMul p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.EDiv p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.ERem p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.EGMax p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.EGMin p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.ESum p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.EProd p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.ECard p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.EMinExp p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.EDomain p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.ERange p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.EUnion p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.EUnionCom p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.EDifference p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.EIntersection p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.EIntersectionDeprecated p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.EJoin p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.ClaferId p, A arg) {
      R r = leaf(arg);
      r = combine(p.name_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.EInt p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(clafer.Absyn.EDouble p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(clafer.Absyn.EReal p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(clafer.Absyn.EStr p, A arg) {
      R r = leaf(arg);
      return r;
    }

/* TransGuard */
    public R visit(clafer.Absyn.TransGuardX p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      return r;
    }

/* TransArrow */
    public R visit(clafer.Absyn.SyncTransArrow p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(clafer.Absyn.GuardedSyncTransArrow p, A arg) {
      R r = leaf(arg);
      r = combine(p.transguard_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.NextTransArrow p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(clafer.Absyn.GuardedNextTransArrow p, A arg) {
      R r = leaf(arg);
      r = combine(p.transguard_.accept(this, arg), r, arg);
      return r;
    }

/* PatternScope */
    public R visit(clafer.Absyn.PatScopeBefore p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.PatScopeAfter p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.PatScopeBetweenAnd p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.PatScopeAfterUntil p, A arg) {
      R r = leaf(arg);
      r = combine(p.exp_1.accept(this, arg), r, arg);
      r = combine(p.exp_2.accept(this, arg), r, arg);
      return r;
    }
    public R visit(clafer.Absyn.PatScopeEmpty p, A arg) {
      R r = leaf(arg);
      return r;
    }

/* Decl */
    public R visit(clafer.Absyn.DeclX p, A arg) {
      R r = leaf(arg);
      for (clafer.Absyn.LocId x : p.listlocid_)
      {
        r = combine(x.accept(this, arg), r, arg);
      }
      r = combine(p.exp_.accept(this, arg), r, arg);
      return r;
    }

/* VarBinding */
    public R visit(clafer.Absyn.VarBindingX p, A arg) {
      R r = leaf(arg);
      r = combine(p.locid_.accept(this, arg), r, arg);
      r = combine(p.name_.accept(this, arg), r, arg);
      return r;
    }

/* Quant */
    public R visit(clafer.Absyn.QuantNo p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(clafer.Absyn.QuantNot p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(clafer.Absyn.QuantLone p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(clafer.Absyn.QuantOne p, A arg) {
      R r = leaf(arg);
      return r;
    }
    public R visit(clafer.Absyn.QuantSome p, A arg) {
      R r = leaf(arg);
      return r;
    }

/* EnumId */
    public R visit(clafer.Absyn.EnumIdIdent p, A arg) {
      R r = leaf(arg);
      return r;
    }

/* ModId */
    public R visit(clafer.Absyn.ModIdIdent p, A arg) {
      R r = leaf(arg);
      return r;
    }

/* LocId */
    public R visit(clafer.Absyn.LocIdIdent p, A arg) {
      R r = leaf(arg);
      return r;
    }


}
