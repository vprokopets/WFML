package clafer;

/** BNFC-Generated Abstract Visitor */

public class AbstractVisitor<R,A> implements AllVisitor<R,A> {
    /* Module */
    public R visit(clafer.Absyn.ModuleX p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(clafer.Absyn.Module p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* Declaration */
    public R visit(clafer.Absyn.EnumDecl p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.ElementDecl p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(clafer.Absyn.Declaration p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* Clafer */
    public R visit(clafer.Absyn.ClaferX p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(clafer.Absyn.Clafer p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* Constraint */
    public R visit(clafer.Absyn.ConstraintX p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(clafer.Absyn.Constraint p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* Assertion */
    public R visit(clafer.Absyn.AssertionX p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(clafer.Absyn.Assertion p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* Goal */
    public R visit(clafer.Absyn.GoalMinDeprecated p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.GoalMaxDeprecated p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.GoalMinimize p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.GoalMaximize p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(clafer.Absyn.Goal p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* TempModifier */
    public R visit(clafer.Absyn.Initial p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.Final p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.FinalRef p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.FinalTarget p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(clafer.Absyn.TempModifier p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* Transition */
    public R visit(clafer.Absyn.TransitionEmpty p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.TransitionX p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(clafer.Absyn.Transition p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* Abstract */
    public R visit(clafer.Absyn.AbstractEmpty p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.AbstractX p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(clafer.Absyn.Abstract p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* Elements */
    public R visit(clafer.Absyn.ElementsEmpty p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.ElementsList p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(clafer.Absyn.Elements p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* Element */
    public R visit(clafer.Absyn.Subclafer p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.ClaferUse p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.Subconstraint p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.Subgoal p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.SubAssertion p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(clafer.Absyn.Element p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* Super */
    public R visit(clafer.Absyn.SuperEmpty p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.SuperSome p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(clafer.Absyn.Super p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* Reference */
    public R visit(clafer.Absyn.ReferenceEmpty p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.ReferenceSet p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.ReferenceBag p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(clafer.Absyn.Reference p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* Init */
    public R visit(clafer.Absyn.InitEmpty p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.InitSome p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(clafer.Absyn.Init p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* InitHow */
    public R visit(clafer.Absyn.InitConstant p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.InitDefault p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(clafer.Absyn.InitHow p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* GCard */
    public R visit(clafer.Absyn.GCardEmpty p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.GCardXor p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.GCardOr p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.GCardMux p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.GCardOpt p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.GCardInterval p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(clafer.Absyn.GCard p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* Card */
    public R visit(clafer.Absyn.CardEmpty p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.CardLone p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.CardSome p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.CardAny p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.CardNum p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.CardInterval p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(clafer.Absyn.Card p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* NCard */
    public R visit(clafer.Absyn.NCardX p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(clafer.Absyn.NCard p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* ExInteger */
    public R visit(clafer.Absyn.ExIntegerAst p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.ExIntegerNum p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(clafer.Absyn.ExInteger p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* Name */
    public R visit(clafer.Absyn.Path p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(clafer.Absyn.Name p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* Exp */
    public R visit(clafer.Absyn.TransitionExp p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EDeclAllDisj p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EDeclAll p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EDeclQuantDisj p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EDeclQuant p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EImpliesElse p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.LetExp p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.TmpPatNever p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.TmpPatSometime p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.TmpPatLessOrOnce p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.TmpPatAlways p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.TmpPatPrecede p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.TmpPatFollow p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.TmpInitially p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.TmpFinally p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EIff p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EImplies p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EOr p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EXor p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EAnd p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.LtlU p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.TmpUntil p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.LtlW p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.TmpWUntil p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.LtlF p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.TmpEventually p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.LtlG p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.TmpGlobally p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.LtlX p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.TmpNext p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.ENeg p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.ELt p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EGt p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EEq p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.ELte p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EGte p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.ENeq p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EIn p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.ENin p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EQuantExp p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EAdd p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.ESub p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EMul p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EDiv p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.ERem p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EGMax p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EGMin p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.ESum p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EProd p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.ECard p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EMinExp p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EDomain p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.ERange p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EUnion p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EUnionCom p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EDifference p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EIntersection p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EIntersectionDeprecated p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EJoin p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.ClaferId p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EInt p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EDouble p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EReal p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.EStr p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(clafer.Absyn.Exp p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* TransGuard */
    public R visit(clafer.Absyn.TransGuardX p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(clafer.Absyn.TransGuard p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* TransArrow */
    public R visit(clafer.Absyn.SyncTransArrow p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.GuardedSyncTransArrow p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.NextTransArrow p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.GuardedNextTransArrow p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(clafer.Absyn.TransArrow p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* PatternScope */
    public R visit(clafer.Absyn.PatScopeBefore p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.PatScopeAfter p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.PatScopeBetweenAnd p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.PatScopeAfterUntil p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.PatScopeEmpty p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(clafer.Absyn.PatternScope p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* Decl */
    public R visit(clafer.Absyn.DeclX p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(clafer.Absyn.Decl p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* VarBinding */
    public R visit(clafer.Absyn.VarBindingX p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(clafer.Absyn.VarBinding p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* Quant */
    public R visit(clafer.Absyn.QuantNo p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.QuantNot p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.QuantLone p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.QuantOne p, A arg) { return visitDefault(p, arg); }
    public R visit(clafer.Absyn.QuantSome p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(clafer.Absyn.Quant p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* EnumId */
    public R visit(clafer.Absyn.EnumIdIdent p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(clafer.Absyn.EnumId p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* ModId */
    public R visit(clafer.Absyn.ModIdIdent p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(clafer.Absyn.ModId p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* LocId */
    public R visit(clafer.Absyn.LocIdIdent p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(clafer.Absyn.LocId p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }

}
