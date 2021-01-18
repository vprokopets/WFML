package clafer;

public class PrettyPrinter
{
  //For certain applications increasing the initial size of the buffer may improve performance.
  private static final int INITIAL_BUFFER_SIZE = 128;
  private static final int INDENT_WIDTH = 2;
  //You may wish to change the parentheses used in precedence.
  private static final String _L_PAREN = new String("(");
  private static final String _R_PAREN = new String(")");
  //You may wish to change render
  private static void render(String s)
  {
    if (s.equals("{"))
    {
       buf_.append("\n");
       indent();
       buf_.append(s);
       _n_ = _n_ + INDENT_WIDTH;
       buf_.append("\n");
       indent();
    }
    else if (s.equals("(") || s.equals("["))
       buf_.append(s);
    else if (s.equals(")") || s.equals("]"))
    {
       backup();
       buf_.append(s);
       buf_.append(" ");
    }
    else if (s.equals("}"))
    {
       int t;
       _n_ = _n_ - INDENT_WIDTH;
       for(t=0; t<INDENT_WIDTH; t++) {
         backup();
       }
       buf_.append(s);
       buf_.append("\n");
       indent();
    }
    else if (s.equals(","))
    {
       backup();
       buf_.append(s);
       buf_.append(" ");
    }
    else if (s.equals(";"))
    {
       backup();
       buf_.append(s);
       buf_.append("\n");
       indent();
    }
    else if (s.equals("")) return;
    else if (s.trim().equals(""))
    {
       backup();
       buf_.append(s);
    }
    else
    {
       buf_.append(s);
       buf_.append(" ");
    }
  }


  //  print and show methods are defined for each category.
  public static String print(clafer.Absyn.Module foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.Module foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.Declaration foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.Declaration foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.Clafer foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.Clafer foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.Constraint foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.Constraint foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.Assertion foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.Assertion foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.Goal foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.Goal foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.TempModifier foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.TempModifier foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.Transition foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.Transition foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.Abstract foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.Abstract foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.Elements foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.Elements foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.Element foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.Element foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.Super foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.Super foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.Reference foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.Reference foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.Init foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.Init foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.InitHow foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.InitHow foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.GCard foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.GCard foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.Card foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.Card foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.NCard foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.NCard foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.ExInteger foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.ExInteger foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.Name foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.Name foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.Exp foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.Exp foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.TransGuard foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.TransGuard foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.TransArrow foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.TransArrow foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.PatternScope foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.PatternScope foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.Decl foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.Decl foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.VarBinding foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.VarBinding foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.Quant foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.Quant foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.EnumId foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.EnumId foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.ModId foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.ModId foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.LocId foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.LocId foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.ListDeclaration foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.ListDeclaration foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.ListEnumId foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.ListEnumId foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.ListElement foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.ListElement foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.ListExp foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.ListExp foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.ListTempModifier foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.ListTempModifier foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.ListLocId foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.ListLocId foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String print(clafer.Absyn.ListModId foo)
  {
    pp(foo, 0);
    trim();
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  public static String show(clafer.Absyn.ListModId foo)
  {
    sh(foo);
    String temp = buf_.toString();
    buf_.delete(0,buf_.length());
    return temp;
  }
  /***   You shouldn't need to change anything beyond this point.   ***/

  private static void pp(clafer.Absyn.Module foo, int _i_)
  {
    if (foo instanceof clafer.Absyn.ModuleX)
    {
       clafer.Absyn.ModuleX _modulex = (clafer.Absyn.ModuleX) foo;
       if (_i_ > 0) render(_L_PAREN);
       pp(_modulex.listdeclaration_, 0);
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(clafer.Absyn.Declaration foo, int _i_)
  {
    if (foo instanceof clafer.Absyn.EnumDecl)
    {
       clafer.Absyn.EnumDecl _enumdecl = (clafer.Absyn.EnumDecl) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("enum");
       pp(_enumdecl.posident_, 0);
       render("=");
       pp(_enumdecl.listenumid_, 0);
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.ElementDecl)
    {
       clafer.Absyn.ElementDecl _elementdecl = (clafer.Absyn.ElementDecl) foo;
       if (_i_ > 0) render(_L_PAREN);
       pp(_elementdecl.element_, 0);
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(clafer.Absyn.Clafer foo, int _i_)
  {
    if (foo instanceof clafer.Absyn.ClaferX)
    {
       clafer.Absyn.ClaferX _claferx = (clafer.Absyn.ClaferX) foo;
       if (_i_ > 0) render(_L_PAREN);
       pp(_claferx.abstract_, 0);
       pp(_claferx.listtempmodifier_, 0);
       pp(_claferx.gcard_, 0);
       pp(_claferx.posident_, 0);
       pp(_claferx.super_, 0);
       pp(_claferx.reference_, 0);
       pp(_claferx.card_, 0);
       pp(_claferx.init_, 0);
       pp(_claferx.transition_, 0);
       pp(_claferx.elements_, 0);
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(clafer.Absyn.Constraint foo, int _i_)
  {
    if (foo instanceof clafer.Absyn.ConstraintX)
    {
       clafer.Absyn.ConstraintX _constraintx = (clafer.Absyn.ConstraintX) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("[");
       pp(_constraintx.listexp_, 0);
       render("]");
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(clafer.Absyn.Assertion foo, int _i_)
  {
    if (foo instanceof clafer.Absyn.AssertionX)
    {
       clafer.Absyn.AssertionX _assertionx = (clafer.Absyn.AssertionX) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("assert");
       render("[");
       pp(_assertionx.listexp_, 0);
       render("]");
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(clafer.Absyn.Goal foo, int _i_)
  {
    if (foo instanceof clafer.Absyn.GoalMinDeprecated)
    {
       clafer.Absyn.GoalMinDeprecated _goalmindeprecated = (clafer.Absyn.GoalMinDeprecated) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("<<");
       render("min");
       pp(_goalmindeprecated.listexp_, 0);
       render(">>");
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.GoalMaxDeprecated)
    {
       clafer.Absyn.GoalMaxDeprecated _goalmaxdeprecated = (clafer.Absyn.GoalMaxDeprecated) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("<<");
       render("max");
       pp(_goalmaxdeprecated.listexp_, 0);
       render(">>");
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.GoalMinimize)
    {
       clafer.Absyn.GoalMinimize _goalminimize = (clafer.Absyn.GoalMinimize) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("<<");
       render("minimize");
       pp(_goalminimize.listexp_, 0);
       render(">>");
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.GoalMaximize)
    {
       clafer.Absyn.GoalMaximize _goalmaximize = (clafer.Absyn.GoalMaximize) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("<<");
       render("maximize");
       pp(_goalmaximize.listexp_, 0);
       render(">>");
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(clafer.Absyn.TempModifier foo, int _i_)
  {
    if (foo instanceof clafer.Absyn.Initial)
    {
       clafer.Absyn.Initial _initial = (clafer.Absyn.Initial) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("initial");
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.Final)
    {
       clafer.Absyn.Final _final = (clafer.Absyn.Final) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("final");
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.FinalRef)
    {
       clafer.Absyn.FinalRef _finalref = (clafer.Absyn.FinalRef) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("finalref");
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.FinalTarget)
    {
       clafer.Absyn.FinalTarget _finaltarget = (clafer.Absyn.FinalTarget) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("finaltarget");
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(clafer.Absyn.Transition foo, int _i_)
  {
    if (foo instanceof clafer.Absyn.TransitionEmpty)
    {
       clafer.Absyn.TransitionEmpty _transitionempty = (clafer.Absyn.TransitionEmpty) foo;
       if (_i_ > 0) render(_L_PAREN);
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.TransitionX)
    {
       clafer.Absyn.TransitionX _transitionx = (clafer.Absyn.TransitionX) foo;
       if (_i_ > 0) render(_L_PAREN);
       pp(_transitionx.transarrow_, 0);
       pp(_transitionx.exp_, 0);
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(clafer.Absyn.Abstract foo, int _i_)
  {
    if (foo instanceof clafer.Absyn.AbstractEmpty)
    {
       clafer.Absyn.AbstractEmpty _abstractempty = (clafer.Absyn.AbstractEmpty) foo;
       if (_i_ > 0) render(_L_PAREN);
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.AbstractX)
    {
       clafer.Absyn.AbstractX _abstractx = (clafer.Absyn.AbstractX) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("abstract");
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(clafer.Absyn.Elements foo, int _i_)
  {
    if (foo instanceof clafer.Absyn.ElementsEmpty)
    {
       clafer.Absyn.ElementsEmpty _elementsempty = (clafer.Absyn.ElementsEmpty) foo;
       if (_i_ > 0) render(_L_PAREN);
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.ElementsList)
    {
       clafer.Absyn.ElementsList _elementslist = (clafer.Absyn.ElementsList) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("{");
       pp(_elementslist.listelement_, 0);
       render("}");
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(clafer.Absyn.Element foo, int _i_)
  {
    if (foo instanceof clafer.Absyn.Subclafer)
    {
       clafer.Absyn.Subclafer _subclafer = (clafer.Absyn.Subclafer) foo;
       if (_i_ > 0) render(_L_PAREN);
       pp(_subclafer.clafer_, 0);
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.ClaferUse)
    {
       clafer.Absyn.ClaferUse _claferuse = (clafer.Absyn.ClaferUse) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("`");
       pp(_claferuse.name_, 0);
       pp(_claferuse.card_, 0);
       pp(_claferuse.elements_, 0);
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.Subconstraint)
    {
       clafer.Absyn.Subconstraint _subconstraint = (clafer.Absyn.Subconstraint) foo;
       if (_i_ > 0) render(_L_PAREN);
       pp(_subconstraint.constraint_, 0);
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.Subgoal)
    {
       clafer.Absyn.Subgoal _subgoal = (clafer.Absyn.Subgoal) foo;
       if (_i_ > 0) render(_L_PAREN);
       pp(_subgoal.goal_, 0);
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.SubAssertion)
    {
       clafer.Absyn.SubAssertion _subassertion = (clafer.Absyn.SubAssertion) foo;
       if (_i_ > 0) render(_L_PAREN);
       pp(_subassertion.assertion_, 0);
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(clafer.Absyn.Super foo, int _i_)
  {
    if (foo instanceof clafer.Absyn.SuperEmpty)
    {
       clafer.Absyn.SuperEmpty _superempty = (clafer.Absyn.SuperEmpty) foo;
       if (_i_ > 0) render(_L_PAREN);
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.SuperSome)
    {
       clafer.Absyn.SuperSome _supersome = (clafer.Absyn.SuperSome) foo;
       if (_i_ > 0) render(_L_PAREN);
       render(":");
       pp(_supersome.exp_, 26);
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(clafer.Absyn.Reference foo, int _i_)
  {
    if (foo instanceof clafer.Absyn.ReferenceEmpty)
    {
       clafer.Absyn.ReferenceEmpty _referenceempty = (clafer.Absyn.ReferenceEmpty) foo;
       if (_i_ > 0) render(_L_PAREN);
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.ReferenceSet)
    {
       clafer.Absyn.ReferenceSet _referenceset = (clafer.Absyn.ReferenceSet) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("->");
       pp(_referenceset.exp_, 23);
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.ReferenceBag)
    {
       clafer.Absyn.ReferenceBag _referencebag = (clafer.Absyn.ReferenceBag) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("->>");
       pp(_referencebag.exp_, 23);
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(clafer.Absyn.Init foo, int _i_)
  {
    if (foo instanceof clafer.Absyn.InitEmpty)
    {
       clafer.Absyn.InitEmpty _initempty = (clafer.Absyn.InitEmpty) foo;
       if (_i_ > 0) render(_L_PAREN);
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.InitSome)
    {
       clafer.Absyn.InitSome _initsome = (clafer.Absyn.InitSome) foo;
       if (_i_ > 0) render(_L_PAREN);
       pp(_initsome.inithow_, 0);
       pp(_initsome.exp_, 0);
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(clafer.Absyn.InitHow foo, int _i_)
  {
    if (foo instanceof clafer.Absyn.InitConstant)
    {
       clafer.Absyn.InitConstant _initconstant = (clafer.Absyn.InitConstant) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("=");
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.InitDefault)
    {
       clafer.Absyn.InitDefault _initdefault = (clafer.Absyn.InitDefault) foo;
       if (_i_ > 0) render(_L_PAREN);
       render(":=");
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(clafer.Absyn.GCard foo, int _i_)
  {
    if (foo instanceof clafer.Absyn.GCardEmpty)
    {
       clafer.Absyn.GCardEmpty _gcardempty = (clafer.Absyn.GCardEmpty) foo;
       if (_i_ > 0) render(_L_PAREN);
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.GCardXor)
    {
       clafer.Absyn.GCardXor _gcardxor = (clafer.Absyn.GCardXor) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("xor");
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.GCardOr)
    {
       clafer.Absyn.GCardOr _gcardor = (clafer.Absyn.GCardOr) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("or");
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.GCardMux)
    {
       clafer.Absyn.GCardMux _gcardmux = (clafer.Absyn.GCardMux) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("mux");
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.GCardOpt)
    {
       clafer.Absyn.GCardOpt _gcardopt = (clafer.Absyn.GCardOpt) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("opt");
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.GCardInterval)
    {
       clafer.Absyn.GCardInterval _gcardinterval = (clafer.Absyn.GCardInterval) foo;
       if (_i_ > 0) render(_L_PAREN);
       pp(_gcardinterval.ncard_, 0);
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(clafer.Absyn.Card foo, int _i_)
  {
    if (foo instanceof clafer.Absyn.CardEmpty)
    {
       clafer.Absyn.CardEmpty _cardempty = (clafer.Absyn.CardEmpty) foo;
       if (_i_ > 0) render(_L_PAREN);
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.CardLone)
    {
       clafer.Absyn.CardLone _cardlone = (clafer.Absyn.CardLone) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("?");
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.CardSome)
    {
       clafer.Absyn.CardSome _cardsome = (clafer.Absyn.CardSome) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("+");
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.CardAny)
    {
       clafer.Absyn.CardAny _cardany = (clafer.Absyn.CardAny) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("*");
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.CardNum)
    {
       clafer.Absyn.CardNum _cardnum = (clafer.Absyn.CardNum) foo;
       if (_i_ > 0) render(_L_PAREN);
       pp(_cardnum.posinteger_, 0);
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.CardInterval)
    {
       clafer.Absyn.CardInterval _cardinterval = (clafer.Absyn.CardInterval) foo;
       if (_i_ > 0) render(_L_PAREN);
       pp(_cardinterval.ncard_, 0);
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(clafer.Absyn.NCard foo, int _i_)
  {
    if (foo instanceof clafer.Absyn.NCardX)
    {
       clafer.Absyn.NCardX _ncardx = (clafer.Absyn.NCardX) foo;
       if (_i_ > 0) render(_L_PAREN);
       pp(_ncardx.posinteger_, 0);
       render("..");
       pp(_ncardx.exinteger_, 0);
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(clafer.Absyn.ExInteger foo, int _i_)
  {
    if (foo instanceof clafer.Absyn.ExIntegerAst)
    {
       clafer.Absyn.ExIntegerAst _exintegerast = (clafer.Absyn.ExIntegerAst) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("*");
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.ExIntegerNum)
    {
       clafer.Absyn.ExIntegerNum _exintegernum = (clafer.Absyn.ExIntegerNum) foo;
       if (_i_ > 0) render(_L_PAREN);
       pp(_exintegernum.posinteger_, 0);
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(clafer.Absyn.Name foo, int _i_)
  {
    if (foo instanceof clafer.Absyn.Path)
    {
       clafer.Absyn.Path _path = (clafer.Absyn.Path) foo;
       if (_i_ > 0) render(_L_PAREN);
       pp(_path.listmodid_, 0);
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(clafer.Absyn.Exp foo, int _i_)
  {
    if (foo instanceof clafer.Absyn.TransitionExp)
    {
       clafer.Absyn.TransitionExp _transitionexp = (clafer.Absyn.TransitionExp) foo;
       if (_i_ > 0) render(_L_PAREN);
       pp(_transitionexp.exp_1, 1);
       pp(_transitionexp.transarrow_, 0);
       pp(_transitionexp.exp_2, 0);
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EDeclAllDisj)
    {
       clafer.Absyn.EDeclAllDisj _edeclalldisj = (clafer.Absyn.EDeclAllDisj) foo;
       if (_i_ > 1) render(_L_PAREN);
       render("all");
       render("disj");
       pp(_edeclalldisj.decl_, 0);
       render("|");
       pp(_edeclalldisj.exp_, 1);
       if (_i_ > 1) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EDeclAll)
    {
       clafer.Absyn.EDeclAll _edeclall = (clafer.Absyn.EDeclAll) foo;
       if (_i_ > 1) render(_L_PAREN);
       render("all");
       pp(_edeclall.decl_, 0);
       render("|");
       pp(_edeclall.exp_, 1);
       if (_i_ > 1) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EDeclQuantDisj)
    {
       clafer.Absyn.EDeclQuantDisj _edeclquantdisj = (clafer.Absyn.EDeclQuantDisj) foo;
       if (_i_ > 1) render(_L_PAREN);
       pp(_edeclquantdisj.quant_, 0);
       render("disj");
       pp(_edeclquantdisj.decl_, 0);
       render("|");
       pp(_edeclquantdisj.exp_, 1);
       if (_i_ > 1) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EDeclQuant)
    {
       clafer.Absyn.EDeclQuant _edeclquant = (clafer.Absyn.EDeclQuant) foo;
       if (_i_ > 1) render(_L_PAREN);
       pp(_edeclquant.quant_, 0);
       pp(_edeclquant.decl_, 0);
       render("|");
       pp(_edeclquant.exp_, 1);
       if (_i_ > 1) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EImpliesElse)
    {
       clafer.Absyn.EImpliesElse _eimplieselse = (clafer.Absyn.EImpliesElse) foo;
       if (_i_ > 1) render(_L_PAREN);
       render("if");
       pp(_eimplieselse.exp_1, 1);
       render("then");
       pp(_eimplieselse.exp_2, 1);
       render("else");
       pp(_eimplieselse.exp_3, 1);
       if (_i_ > 1) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.LetExp)
    {
       clafer.Absyn.LetExp _letexp = (clafer.Absyn.LetExp) foo;
       if (_i_ > 1) render(_L_PAREN);
       render("let");
       pp(_letexp.varbinding_, 0);
       render("in");
       pp(_letexp.exp_, 1);
       if (_i_ > 1) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.TmpPatNever)
    {
       clafer.Absyn.TmpPatNever _tmppatnever = (clafer.Absyn.TmpPatNever) foo;
       if (_i_ > 2) render(_L_PAREN);
       render("never");
       pp(_tmppatnever.exp_, 3);
       pp(_tmppatnever.patternscope_, 0);
       if (_i_ > 2) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.TmpPatSometime)
    {
       clafer.Absyn.TmpPatSometime _tmppatsometime = (clafer.Absyn.TmpPatSometime) foo;
       if (_i_ > 2) render(_L_PAREN);
       render("sometime");
       pp(_tmppatsometime.exp_, 3);
       pp(_tmppatsometime.patternscope_, 0);
       if (_i_ > 2) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.TmpPatLessOrOnce)
    {
       clafer.Absyn.TmpPatLessOrOnce _tmppatlessoronce = (clafer.Absyn.TmpPatLessOrOnce) foo;
       if (_i_ > 2) render(_L_PAREN);
       render("lonce");
       pp(_tmppatlessoronce.exp_, 3);
       pp(_tmppatlessoronce.patternscope_, 0);
       if (_i_ > 2) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.TmpPatAlways)
    {
       clafer.Absyn.TmpPatAlways _tmppatalways = (clafer.Absyn.TmpPatAlways) foo;
       if (_i_ > 2) render(_L_PAREN);
       render("always");
       pp(_tmppatalways.exp_, 3);
       pp(_tmppatalways.patternscope_, 0);
       if (_i_ > 2) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.TmpPatPrecede)
    {
       clafer.Absyn.TmpPatPrecede _tmppatprecede = (clafer.Absyn.TmpPatPrecede) foo;
       if (_i_ > 2) render(_L_PAREN);
       pp(_tmppatprecede.exp_1, 3);
       render("must");
       render("precede");
       pp(_tmppatprecede.exp_2, 3);
       pp(_tmppatprecede.patternscope_, 0);
       if (_i_ > 2) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.TmpPatFollow)
    {
       clafer.Absyn.TmpPatFollow _tmppatfollow = (clafer.Absyn.TmpPatFollow) foo;
       if (_i_ > 2) render(_L_PAREN);
       pp(_tmppatfollow.exp_1, 3);
       render("must");
       render("follow");
       pp(_tmppatfollow.exp_2, 3);
       pp(_tmppatfollow.patternscope_, 0);
       if (_i_ > 2) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.TmpInitially)
    {
       clafer.Absyn.TmpInitially _tmpinitially = (clafer.Absyn.TmpInitially) foo;
       if (_i_ > 2) render(_L_PAREN);
       render("initially");
       pp(_tmpinitially.exp_, 3);
       if (_i_ > 2) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.TmpFinally)
    {
       clafer.Absyn.TmpFinally _tmpfinally = (clafer.Absyn.TmpFinally) foo;
       if (_i_ > 2) render(_L_PAREN);
       render("finally");
       pp(_tmpfinally.exp_, 3);
       if (_i_ > 2) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EIff)
    {
       clafer.Absyn.EIff _eiff = (clafer.Absyn.EIff) foo;
       if (_i_ > 3) render(_L_PAREN);
       pp(_eiff.exp_1, 3);
       render("<=>");
       pp(_eiff.exp_2, 4);
       if (_i_ > 3) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EImplies)
    {
       clafer.Absyn.EImplies _eimplies = (clafer.Absyn.EImplies) foo;
       if (_i_ > 4) render(_L_PAREN);
       pp(_eimplies.exp_1, 4);
       render("=>");
       pp(_eimplies.exp_2, 5);
       if (_i_ > 4) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EOr)
    {
       clafer.Absyn.EOr _eor = (clafer.Absyn.EOr) foo;
       if (_i_ > 5) render(_L_PAREN);
       pp(_eor.exp_1, 5);
       render("||");
       pp(_eor.exp_2, 6);
       if (_i_ > 5) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EXor)
    {
       clafer.Absyn.EXor _exor = (clafer.Absyn.EXor) foo;
       if (_i_ > 6) render(_L_PAREN);
       pp(_exor.exp_1, 6);
       render("xor");
       pp(_exor.exp_2, 7);
       if (_i_ > 6) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EAnd)
    {
       clafer.Absyn.EAnd _eand = (clafer.Absyn.EAnd) foo;
       if (_i_ > 7) render(_L_PAREN);
       pp(_eand.exp_1, 7);
       render("&&");
       pp(_eand.exp_2, 8);
       if (_i_ > 7) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.LtlU)
    {
       clafer.Absyn.LtlU _ltlu = (clafer.Absyn.LtlU) foo;
       if (_i_ > 8) render(_L_PAREN);
       pp(_ltlu.exp_1, 8);
       render("U");
       pp(_ltlu.exp_2, 9);
       if (_i_ > 8) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.TmpUntil)
    {
       clafer.Absyn.TmpUntil _tmpuntil = (clafer.Absyn.TmpUntil) foo;
       if (_i_ > 8) render(_L_PAREN);
       pp(_tmpuntil.exp_1, 8);
       render("until");
       pp(_tmpuntil.exp_2, 9);
       if (_i_ > 8) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.LtlW)
    {
       clafer.Absyn.LtlW _ltlw = (clafer.Absyn.LtlW) foo;
       if (_i_ > 9) render(_L_PAREN);
       pp(_ltlw.exp_1, 9);
       render("W");
       pp(_ltlw.exp_2, 10);
       if (_i_ > 9) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.TmpWUntil)
    {
       clafer.Absyn.TmpWUntil _tmpwuntil = (clafer.Absyn.TmpWUntil) foo;
       if (_i_ > 9) render(_L_PAREN);
       pp(_tmpwuntil.exp_1, 9);
       render("weakuntil");
       pp(_tmpwuntil.exp_2, 10);
       if (_i_ > 9) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.LtlF)
    {
       clafer.Absyn.LtlF _ltlf = (clafer.Absyn.LtlF) foo;
       if (_i_ > 10) render(_L_PAREN);
       render("F");
       pp(_ltlf.exp_, 10);
       if (_i_ > 10) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.TmpEventually)
    {
       clafer.Absyn.TmpEventually _tmpeventually = (clafer.Absyn.TmpEventually) foo;
       if (_i_ > 10) render(_L_PAREN);
       render("eventually");
       pp(_tmpeventually.exp_, 10);
       if (_i_ > 10) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.LtlG)
    {
       clafer.Absyn.LtlG _ltlg = (clafer.Absyn.LtlG) foo;
       if (_i_ > 10) render(_L_PAREN);
       render("G");
       pp(_ltlg.exp_, 10);
       if (_i_ > 10) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.TmpGlobally)
    {
       clafer.Absyn.TmpGlobally _tmpglobally = (clafer.Absyn.TmpGlobally) foo;
       if (_i_ > 10) render(_L_PAREN);
       render("globally");
       pp(_tmpglobally.exp_, 10);
       if (_i_ > 10) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.LtlX)
    {
       clafer.Absyn.LtlX _ltlx = (clafer.Absyn.LtlX) foo;
       if (_i_ > 10) render(_L_PAREN);
       render("X");
       pp(_ltlx.exp_, 10);
       if (_i_ > 10) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.TmpNext)
    {
       clafer.Absyn.TmpNext _tmpnext = (clafer.Absyn.TmpNext) foo;
       if (_i_ > 10) render(_L_PAREN);
       render("next");
       pp(_tmpnext.exp_, 10);
       if (_i_ > 10) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.ENeg)
    {
       clafer.Absyn.ENeg _eneg = (clafer.Absyn.ENeg) foo;
       if (_i_ > 11) render(_L_PAREN);
       render("!");
       pp(_eneg.exp_, 11);
       if (_i_ > 11) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.ELt)
    {
       clafer.Absyn.ELt _elt = (clafer.Absyn.ELt) foo;
       if (_i_ > 15) render(_L_PAREN);
       pp(_elt.exp_1, 15);
       render("<");
       pp(_elt.exp_2, 16);
       if (_i_ > 15) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EGt)
    {
       clafer.Absyn.EGt _egt = (clafer.Absyn.EGt) foo;
       if (_i_ > 15) render(_L_PAREN);
       pp(_egt.exp_1, 15);
       render(">");
       pp(_egt.exp_2, 16);
       if (_i_ > 15) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EEq)
    {
       clafer.Absyn.EEq _eeq = (clafer.Absyn.EEq) foo;
       if (_i_ > 15) render(_L_PAREN);
       pp(_eeq.exp_1, 15);
       render("=");
       pp(_eeq.exp_2, 16);
       if (_i_ > 15) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.ELte)
    {
       clafer.Absyn.ELte _elte = (clafer.Absyn.ELte) foo;
       if (_i_ > 15) render(_L_PAREN);
       pp(_elte.exp_1, 15);
       render("<=");
       pp(_elte.exp_2, 16);
       if (_i_ > 15) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EGte)
    {
       clafer.Absyn.EGte _egte = (clafer.Absyn.EGte) foo;
       if (_i_ > 15) render(_L_PAREN);
       pp(_egte.exp_1, 15);
       render(">=");
       pp(_egte.exp_2, 16);
       if (_i_ > 15) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.ENeq)
    {
       clafer.Absyn.ENeq _eneq = (clafer.Absyn.ENeq) foo;
       if (_i_ > 15) render(_L_PAREN);
       pp(_eneq.exp_1, 15);
       render("!=");
       pp(_eneq.exp_2, 16);
       if (_i_ > 15) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EIn)
    {
       clafer.Absyn.EIn _ein = (clafer.Absyn.EIn) foo;
       if (_i_ > 15) render(_L_PAREN);
       pp(_ein.exp_1, 15);
       render("in");
       pp(_ein.exp_2, 16);
       if (_i_ > 15) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.ENin)
    {
       clafer.Absyn.ENin _enin = (clafer.Absyn.ENin) foo;
       if (_i_ > 15) render(_L_PAREN);
       pp(_enin.exp_1, 15);
       render("not");
       render("in");
       pp(_enin.exp_2, 16);
       if (_i_ > 15) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EQuantExp)
    {
       clafer.Absyn.EQuantExp _equantexp = (clafer.Absyn.EQuantExp) foo;
       if (_i_ > 16) render(_L_PAREN);
       pp(_equantexp.quant_, 0);
       pp(_equantexp.exp_, 20);
       if (_i_ > 16) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EAdd)
    {
       clafer.Absyn.EAdd _eadd = (clafer.Absyn.EAdd) foo;
       if (_i_ > 17) render(_L_PAREN);
       pp(_eadd.exp_1, 17);
       render("+");
       pp(_eadd.exp_2, 18);
       if (_i_ > 17) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.ESub)
    {
       clafer.Absyn.ESub _esub = (clafer.Absyn.ESub) foo;
       if (_i_ > 17) render(_L_PAREN);
       pp(_esub.exp_1, 17);
       render("-");
       pp(_esub.exp_2, 18);
       if (_i_ > 17) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EMul)
    {
       clafer.Absyn.EMul _emul = (clafer.Absyn.EMul) foo;
       if (_i_ > 18) render(_L_PAREN);
       pp(_emul.exp_1, 18);
       render("*");
       pp(_emul.exp_2, 19);
       if (_i_ > 18) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EDiv)
    {
       clafer.Absyn.EDiv _ediv = (clafer.Absyn.EDiv) foo;
       if (_i_ > 18) render(_L_PAREN);
       pp(_ediv.exp_1, 18);
       render("/");
       pp(_ediv.exp_2, 19);
       if (_i_ > 18) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.ERem)
    {
       clafer.Absyn.ERem _erem = (clafer.Absyn.ERem) foo;
       if (_i_ > 18) render(_L_PAREN);
       pp(_erem.exp_1, 18);
       render("%");
       pp(_erem.exp_2, 19);
       if (_i_ > 18) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EGMax)
    {
       clafer.Absyn.EGMax _egmax = (clafer.Absyn.EGMax) foo;
       if (_i_ > 19) render(_L_PAREN);
       render("max");
       pp(_egmax.exp_, 20);
       if (_i_ > 19) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EGMin)
    {
       clafer.Absyn.EGMin _egmin = (clafer.Absyn.EGMin) foo;
       if (_i_ > 19) render(_L_PAREN);
       render("min");
       pp(_egmin.exp_, 20);
       if (_i_ > 19) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.ESum)
    {
       clafer.Absyn.ESum _esum = (clafer.Absyn.ESum) foo;
       if (_i_ > 20) render(_L_PAREN);
       render("sum");
       pp(_esum.exp_, 21);
       if (_i_ > 20) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EProd)
    {
       clafer.Absyn.EProd _eprod = (clafer.Absyn.EProd) foo;
       if (_i_ > 20) render(_L_PAREN);
       render("product");
       pp(_eprod.exp_, 21);
       if (_i_ > 20) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.ECard)
    {
       clafer.Absyn.ECard _ecard = (clafer.Absyn.ECard) foo;
       if (_i_ > 20) render(_L_PAREN);
       render("#");
       pp(_ecard.exp_, 21);
       if (_i_ > 20) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EMinExp)
    {
       clafer.Absyn.EMinExp _eminexp = (clafer.Absyn.EMinExp) foo;
       if (_i_ > 20) render(_L_PAREN);
       render("-");
       pp(_eminexp.exp_, 21);
       if (_i_ > 20) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EDomain)
    {
       clafer.Absyn.EDomain _edomain = (clafer.Absyn.EDomain) foo;
       if (_i_ > 21) render(_L_PAREN);
       pp(_edomain.exp_1, 21);
       render("<:");
       pp(_edomain.exp_2, 22);
       if (_i_ > 21) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.ERange)
    {
       clafer.Absyn.ERange _erange = (clafer.Absyn.ERange) foo;
       if (_i_ > 22) render(_L_PAREN);
       pp(_erange.exp_1, 22);
       render(":>");
       pp(_erange.exp_2, 23);
       if (_i_ > 22) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EUnion)
    {
       clafer.Absyn.EUnion _eunion = (clafer.Absyn.EUnion) foo;
       if (_i_ > 23) render(_L_PAREN);
       pp(_eunion.exp_1, 23);
       render("++");
       pp(_eunion.exp_2, 24);
       if (_i_ > 23) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EUnionCom)
    {
       clafer.Absyn.EUnionCom _eunioncom = (clafer.Absyn.EUnionCom) foo;
       if (_i_ > 23) render(_L_PAREN);
       pp(_eunioncom.exp_1, 23);
       render(",");
       pp(_eunioncom.exp_2, 24);
       if (_i_ > 23) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EDifference)
    {
       clafer.Absyn.EDifference _edifference = (clafer.Absyn.EDifference) foo;
       if (_i_ > 24) render(_L_PAREN);
       pp(_edifference.exp_1, 24);
       render("--");
       pp(_edifference.exp_2, 25);
       if (_i_ > 24) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EIntersection)
    {
       clafer.Absyn.EIntersection _eintersection = (clafer.Absyn.EIntersection) foo;
       if (_i_ > 25) render(_L_PAREN);
       pp(_eintersection.exp_1, 25);
       render("**");
       pp(_eintersection.exp_2, 26);
       if (_i_ > 25) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EIntersectionDeprecated)
    {
       clafer.Absyn.EIntersectionDeprecated _eintersectiondeprecated = (clafer.Absyn.EIntersectionDeprecated) foo;
       if (_i_ > 26) render(_L_PAREN);
       pp(_eintersectiondeprecated.exp_1, 26);
       render("&");
       pp(_eintersectiondeprecated.exp_2, 27);
       if (_i_ > 26) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EJoin)
    {
       clafer.Absyn.EJoin _ejoin = (clafer.Absyn.EJoin) foo;
       if (_i_ > 26) render(_L_PAREN);
       pp(_ejoin.exp_1, 26);
       render(".");
       pp(_ejoin.exp_2, 27);
       if (_i_ > 26) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.ClaferId)
    {
       clafer.Absyn.ClaferId _claferid = (clafer.Absyn.ClaferId) foo;
       if (_i_ > 27) render(_L_PAREN);
       pp(_claferid.name_, 0);
       if (_i_ > 27) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EInt)
    {
       clafer.Absyn.EInt _eint = (clafer.Absyn.EInt) foo;
       if (_i_ > 27) render(_L_PAREN);
       pp(_eint.posinteger_, 0);
       if (_i_ > 27) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EDouble)
    {
       clafer.Absyn.EDouble _edouble = (clafer.Absyn.EDouble) foo;
       if (_i_ > 27) render(_L_PAREN);
       pp(_edouble.posdouble_, 0);
       if (_i_ > 27) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EReal)
    {
       clafer.Absyn.EReal _ereal = (clafer.Absyn.EReal) foo;
       if (_i_ > 27) render(_L_PAREN);
       pp(_ereal.posreal_, 0);
       if (_i_ > 27) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.EStr)
    {
       clafer.Absyn.EStr _estr = (clafer.Absyn.EStr) foo;
       if (_i_ > 27) render(_L_PAREN);
       pp(_estr.posstring_, 0);
       if (_i_ > 27) render(_R_PAREN);
    }
  }

  private static void pp(clafer.Absyn.TransGuard foo, int _i_)
  {
    if (foo instanceof clafer.Absyn.TransGuardX)
    {
       clafer.Absyn.TransGuardX _transguardx = (clafer.Absyn.TransGuardX) foo;
       if (_i_ > 0) render(_L_PAREN);
       pp(_transguardx.exp_, 1);
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(clafer.Absyn.TransArrow foo, int _i_)
  {
    if (foo instanceof clafer.Absyn.SyncTransArrow)
    {
       clafer.Absyn.SyncTransArrow _synctransarrow = (clafer.Absyn.SyncTransArrow) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("-->>");
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.GuardedSyncTransArrow)
    {
       clafer.Absyn.GuardedSyncTransArrow _guardedsynctransarrow = (clafer.Absyn.GuardedSyncTransArrow) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("-[");
       pp(_guardedsynctransarrow.transguard_, 0);
       render("]->>");
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.NextTransArrow)
    {
       clafer.Absyn.NextTransArrow _nexttransarrow = (clafer.Absyn.NextTransArrow) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("-->");
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.GuardedNextTransArrow)
    {
       clafer.Absyn.GuardedNextTransArrow _guardednexttransarrow = (clafer.Absyn.GuardedNextTransArrow) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("-[");
       pp(_guardednexttransarrow.transguard_, 0);
       render("]->");
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(clafer.Absyn.PatternScope foo, int _i_)
  {
    if (foo instanceof clafer.Absyn.PatScopeBefore)
    {
       clafer.Absyn.PatScopeBefore _patscopebefore = (clafer.Absyn.PatScopeBefore) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("before");
       pp(_patscopebefore.exp_, 11);
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.PatScopeAfter)
    {
       clafer.Absyn.PatScopeAfter _patscopeafter = (clafer.Absyn.PatScopeAfter) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("after");
       pp(_patscopeafter.exp_, 11);
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.PatScopeBetweenAnd)
    {
       clafer.Absyn.PatScopeBetweenAnd _patscopebetweenand = (clafer.Absyn.PatScopeBetweenAnd) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("between");
       pp(_patscopebetweenand.exp_1, 11);
       render("and");
       pp(_patscopebetweenand.exp_2, 11);
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.PatScopeAfterUntil)
    {
       clafer.Absyn.PatScopeAfterUntil _patscopeafteruntil = (clafer.Absyn.PatScopeAfterUntil) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("after");
       pp(_patscopeafteruntil.exp_1, 11);
       render("until");
       pp(_patscopeafteruntil.exp_2, 11);
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.PatScopeEmpty)
    {
       clafer.Absyn.PatScopeEmpty _patscopeempty = (clafer.Absyn.PatScopeEmpty) foo;
       if (_i_ > 0) render(_L_PAREN);
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(clafer.Absyn.Decl foo, int _i_)
  {
    if (foo instanceof clafer.Absyn.DeclX)
    {
       clafer.Absyn.DeclX _declx = (clafer.Absyn.DeclX) foo;
       if (_i_ > 0) render(_L_PAREN);
       pp(_declx.listlocid_, 0);
       render(":");
       pp(_declx.exp_, 21);
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(clafer.Absyn.VarBinding foo, int _i_)
  {
    if (foo instanceof clafer.Absyn.VarBindingX)
    {
       clafer.Absyn.VarBindingX _varbindingx = (clafer.Absyn.VarBindingX) foo;
       if (_i_ > 0) render(_L_PAREN);
       pp(_varbindingx.locid_, 0);
       render("=");
       pp(_varbindingx.name_, 0);
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(clafer.Absyn.Quant foo, int _i_)
  {
    if (foo instanceof clafer.Absyn.QuantNo)
    {
       clafer.Absyn.QuantNo _quantno = (clafer.Absyn.QuantNo) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("no");
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.QuantNot)
    {
       clafer.Absyn.QuantNot _quantnot = (clafer.Absyn.QuantNot) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("not");
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.QuantLone)
    {
       clafer.Absyn.QuantLone _quantlone = (clafer.Absyn.QuantLone) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("lone");
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.QuantOne)
    {
       clafer.Absyn.QuantOne _quantone = (clafer.Absyn.QuantOne) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("one");
       if (_i_ > 0) render(_R_PAREN);
    }
    else     if (foo instanceof clafer.Absyn.QuantSome)
    {
       clafer.Absyn.QuantSome _quantsome = (clafer.Absyn.QuantSome) foo;
       if (_i_ > 0) render(_L_PAREN);
       render("some");
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(clafer.Absyn.EnumId foo, int _i_)
  {
    if (foo instanceof clafer.Absyn.EnumIdIdent)
    {
       clafer.Absyn.EnumIdIdent _enumidident = (clafer.Absyn.EnumIdIdent) foo;
       if (_i_ > 0) render(_L_PAREN);
       pp(_enumidident.posident_, 0);
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(clafer.Absyn.ModId foo, int _i_)
  {
    if (foo instanceof clafer.Absyn.ModIdIdent)
    {
       clafer.Absyn.ModIdIdent _modidident = (clafer.Absyn.ModIdIdent) foo;
       if (_i_ > 0) render(_L_PAREN);
       pp(_modidident.posident_, 0);
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(clafer.Absyn.LocId foo, int _i_)
  {
    if (foo instanceof clafer.Absyn.LocIdIdent)
    {
       clafer.Absyn.LocIdIdent _locidident = (clafer.Absyn.LocIdIdent) foo;
       if (_i_ > 0) render(_L_PAREN);
       pp(_locidident.posident_, 0);
       if (_i_ > 0) render(_R_PAREN);
    }
  }

  private static void pp(clafer.Absyn.ListDeclaration foo, int _i_)
  {
     for (java.util.Iterator<clafer.Absyn.Declaration> it = foo.iterator(); it.hasNext();)
     {
       pp(it.next(), _i_);
       if (it.hasNext()) {
         render("");
       } else {
         render("");
       }
     }  }

  private static void pp(clafer.Absyn.ListEnumId foo, int _i_)
  {
     for (java.util.Iterator<clafer.Absyn.EnumId> it = foo.iterator(); it.hasNext();)
     {
       pp(it.next(), _i_);
       if (it.hasNext()) {
         render("|");
       } else {
         render("");
       }
     }  }

  private static void pp(clafer.Absyn.ListElement foo, int _i_)
  {
     for (java.util.Iterator<clafer.Absyn.Element> it = foo.iterator(); it.hasNext();)
     {
       pp(it.next(), _i_);
       if (it.hasNext()) {
         render("");
       } else {
         render("");
       }
     }  }

  private static void pp(clafer.Absyn.ListExp foo, int _i_)
  {
     for (java.util.Iterator<clafer.Absyn.Exp> it = foo.iterator(); it.hasNext();)
     {
       pp(it.next(), _i_);
       if (it.hasNext()) {
         render("");
       } else {
         render("");
       }
     }  }

  private static void pp(clafer.Absyn.ListTempModifier foo, int _i_)
  {
     for (java.util.Iterator<clafer.Absyn.TempModifier> it = foo.iterator(); it.hasNext();)
     {
       pp(it.next(), _i_);
       if (it.hasNext()) {
         render("");
       } else {
         render("");
       }
     }  }

  private static void pp(clafer.Absyn.ListLocId foo, int _i_)
  {
     for (java.util.Iterator<clafer.Absyn.LocId> it = foo.iterator(); it.hasNext();)
     {
       pp(it.next(), _i_);
       if (it.hasNext()) {
         render(";");
       } else {
         render("");
       }
     }  }

  private static void pp(clafer.Absyn.ListModId foo, int _i_)
  {
     for (java.util.Iterator<clafer.Absyn.ModId> it = foo.iterator(); it.hasNext();)
     {
       pp(it.next(), _i_);
       if (it.hasNext()) {
         render("\");
       } else {
         render("");
       }
     }  }


  private static void sh(clafer.Absyn.Module foo)
  {
    if (foo instanceof clafer.Absyn.ModuleX)
    {
       clafer.Absyn.ModuleX _modulex = (clafer.Absyn.ModuleX) foo;
       render("(");
       render("ModuleX");
       render("[");
       sh(_modulex.listdeclaration_);
       render("]");
       render(")");
    }
  }

  private static void sh(clafer.Absyn.Declaration foo)
  {
    if (foo instanceof clafer.Absyn.EnumDecl)
    {
       clafer.Absyn.EnumDecl _enumdecl = (clafer.Absyn.EnumDecl) foo;
       render("(");
       render("EnumDecl");
       sh(_enumdecl.posident_);
       render("[");
       sh(_enumdecl.listenumid_);
       render("]");
       render(")");
    }
    if (foo instanceof clafer.Absyn.ElementDecl)
    {
       clafer.Absyn.ElementDecl _elementdecl = (clafer.Absyn.ElementDecl) foo;
       render("(");
       render("ElementDecl");
       sh(_elementdecl.element_);
       render(")");
    }
  }

  private static void sh(clafer.Absyn.Clafer foo)
  {
    if (foo instanceof clafer.Absyn.ClaferX)
    {
       clafer.Absyn.ClaferX _claferx = (clafer.Absyn.ClaferX) foo;
       render("(");
       render("ClaferX");
       sh(_claferx.abstract_);
       render("[");
       sh(_claferx.listtempmodifier_);
       render("]");
       sh(_claferx.gcard_);
       sh(_claferx.posident_);
       sh(_claferx.super_);
       sh(_claferx.reference_);
       sh(_claferx.card_);
       sh(_claferx.init_);
       sh(_claferx.transition_);
       sh(_claferx.elements_);
       render(")");
    }
  }

  private static void sh(clafer.Absyn.Constraint foo)
  {
    if (foo instanceof clafer.Absyn.ConstraintX)
    {
       clafer.Absyn.ConstraintX _constraintx = (clafer.Absyn.ConstraintX) foo;
       render("(");
       render("ConstraintX");
       render("[");
       sh(_constraintx.listexp_);
       render("]");
       render(")");
    }
  }

  private static void sh(clafer.Absyn.Assertion foo)
  {
    if (foo instanceof clafer.Absyn.AssertionX)
    {
       clafer.Absyn.AssertionX _assertionx = (clafer.Absyn.AssertionX) foo;
       render("(");
       render("AssertionX");
       render("[");
       sh(_assertionx.listexp_);
       render("]");
       render(")");
    }
  }

  private static void sh(clafer.Absyn.Goal foo)
  {
    if (foo instanceof clafer.Absyn.GoalMinDeprecated)
    {
       clafer.Absyn.GoalMinDeprecated _goalmindeprecated = (clafer.Absyn.GoalMinDeprecated) foo;
       render("(");
       render("GoalMinDeprecated");
       render("[");
       sh(_goalmindeprecated.listexp_);
       render("]");
       render(")");
    }
    if (foo instanceof clafer.Absyn.GoalMaxDeprecated)
    {
       clafer.Absyn.GoalMaxDeprecated _goalmaxdeprecated = (clafer.Absyn.GoalMaxDeprecated) foo;
       render("(");
       render("GoalMaxDeprecated");
       render("[");
       sh(_goalmaxdeprecated.listexp_);
       render("]");
       render(")");
    }
    if (foo instanceof clafer.Absyn.GoalMinimize)
    {
       clafer.Absyn.GoalMinimize _goalminimize = (clafer.Absyn.GoalMinimize) foo;
       render("(");
       render("GoalMinimize");
       render("[");
       sh(_goalminimize.listexp_);
       render("]");
       render(")");
    }
    if (foo instanceof clafer.Absyn.GoalMaximize)
    {
       clafer.Absyn.GoalMaximize _goalmaximize = (clafer.Absyn.GoalMaximize) foo;
       render("(");
       render("GoalMaximize");
       render("[");
       sh(_goalmaximize.listexp_);
       render("]");
       render(")");
    }
  }

  private static void sh(clafer.Absyn.TempModifier foo)
  {
    if (foo instanceof clafer.Absyn.Initial)
    {
       clafer.Absyn.Initial _initial = (clafer.Absyn.Initial) foo;
       render("Initial");
    }
    if (foo instanceof clafer.Absyn.Final)
    {
       clafer.Absyn.Final _final = (clafer.Absyn.Final) foo;
       render("Final");
    }
    if (foo instanceof clafer.Absyn.FinalRef)
    {
       clafer.Absyn.FinalRef _finalref = (clafer.Absyn.FinalRef) foo;
       render("FinalRef");
    }
    if (foo instanceof clafer.Absyn.FinalTarget)
    {
       clafer.Absyn.FinalTarget _finaltarget = (clafer.Absyn.FinalTarget) foo;
       render("FinalTarget");
    }
  }

  private static void sh(clafer.Absyn.Transition foo)
  {
    if (foo instanceof clafer.Absyn.TransitionEmpty)
    {
       clafer.Absyn.TransitionEmpty _transitionempty = (clafer.Absyn.TransitionEmpty) foo;
       render("TransitionEmpty");
    }
    if (foo instanceof clafer.Absyn.TransitionX)
    {
       clafer.Absyn.TransitionX _transitionx = (clafer.Absyn.TransitionX) foo;
       render("(");
       render("TransitionX");
       sh(_transitionx.transarrow_);
       sh(_transitionx.exp_);
       render(")");
    }
  }

  private static void sh(clafer.Absyn.Abstract foo)
  {
    if (foo instanceof clafer.Absyn.AbstractEmpty)
    {
       clafer.Absyn.AbstractEmpty _abstractempty = (clafer.Absyn.AbstractEmpty) foo;
       render("AbstractEmpty");
    }
    if (foo instanceof clafer.Absyn.AbstractX)
    {
       clafer.Absyn.AbstractX _abstractx = (clafer.Absyn.AbstractX) foo;
       render("AbstractX");
    }
  }

  private static void sh(clafer.Absyn.Elements foo)
  {
    if (foo instanceof clafer.Absyn.ElementsEmpty)
    {
       clafer.Absyn.ElementsEmpty _elementsempty = (clafer.Absyn.ElementsEmpty) foo;
       render("ElementsEmpty");
    }
    if (foo instanceof clafer.Absyn.ElementsList)
    {
       clafer.Absyn.ElementsList _elementslist = (clafer.Absyn.ElementsList) foo;
       render("(");
       render("ElementsList");
       render("[");
       sh(_elementslist.listelement_);
       render("]");
       render(")");
    }
  }

  private static void sh(clafer.Absyn.Element foo)
  {
    if (foo instanceof clafer.Absyn.Subclafer)
    {
       clafer.Absyn.Subclafer _subclafer = (clafer.Absyn.Subclafer) foo;
       render("(");
       render("Subclafer");
       sh(_subclafer.clafer_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.ClaferUse)
    {
       clafer.Absyn.ClaferUse _claferuse = (clafer.Absyn.ClaferUse) foo;
       render("(");
       render("ClaferUse");
       sh(_claferuse.name_);
       sh(_claferuse.card_);
       sh(_claferuse.elements_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.Subconstraint)
    {
       clafer.Absyn.Subconstraint _subconstraint = (clafer.Absyn.Subconstraint) foo;
       render("(");
       render("Subconstraint");
       sh(_subconstraint.constraint_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.Subgoal)
    {
       clafer.Absyn.Subgoal _subgoal = (clafer.Absyn.Subgoal) foo;
       render("(");
       render("Subgoal");
       sh(_subgoal.goal_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.SubAssertion)
    {
       clafer.Absyn.SubAssertion _subassertion = (clafer.Absyn.SubAssertion) foo;
       render("(");
       render("SubAssertion");
       sh(_subassertion.assertion_);
       render(")");
    }
  }

  private static void sh(clafer.Absyn.Super foo)
  {
    if (foo instanceof clafer.Absyn.SuperEmpty)
    {
       clafer.Absyn.SuperEmpty _superempty = (clafer.Absyn.SuperEmpty) foo;
       render("SuperEmpty");
    }
    if (foo instanceof clafer.Absyn.SuperSome)
    {
       clafer.Absyn.SuperSome _supersome = (clafer.Absyn.SuperSome) foo;
       render("(");
       render("SuperSome");
       sh(_supersome.exp_);
       render(")");
    }
  }

  private static void sh(clafer.Absyn.Reference foo)
  {
    if (foo instanceof clafer.Absyn.ReferenceEmpty)
    {
       clafer.Absyn.ReferenceEmpty _referenceempty = (clafer.Absyn.ReferenceEmpty) foo;
       render("ReferenceEmpty");
    }
    if (foo instanceof clafer.Absyn.ReferenceSet)
    {
       clafer.Absyn.ReferenceSet _referenceset = (clafer.Absyn.ReferenceSet) foo;
       render("(");
       render("ReferenceSet");
       sh(_referenceset.exp_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.ReferenceBag)
    {
       clafer.Absyn.ReferenceBag _referencebag = (clafer.Absyn.ReferenceBag) foo;
       render("(");
       render("ReferenceBag");
       sh(_referencebag.exp_);
       render(")");
    }
  }

  private static void sh(clafer.Absyn.Init foo)
  {
    if (foo instanceof clafer.Absyn.InitEmpty)
    {
       clafer.Absyn.InitEmpty _initempty = (clafer.Absyn.InitEmpty) foo;
       render("InitEmpty");
    }
    if (foo instanceof clafer.Absyn.InitSome)
    {
       clafer.Absyn.InitSome _initsome = (clafer.Absyn.InitSome) foo;
       render("(");
       render("InitSome");
       sh(_initsome.inithow_);
       sh(_initsome.exp_);
       render(")");
    }
  }

  private static void sh(clafer.Absyn.InitHow foo)
  {
    if (foo instanceof clafer.Absyn.InitConstant)
    {
       clafer.Absyn.InitConstant _initconstant = (clafer.Absyn.InitConstant) foo;
       render("InitConstant");
    }
    if (foo instanceof clafer.Absyn.InitDefault)
    {
       clafer.Absyn.InitDefault _initdefault = (clafer.Absyn.InitDefault) foo;
       render("InitDefault");
    }
  }

  private static void sh(clafer.Absyn.GCard foo)
  {
    if (foo instanceof clafer.Absyn.GCardEmpty)
    {
       clafer.Absyn.GCardEmpty _gcardempty = (clafer.Absyn.GCardEmpty) foo;
       render("GCardEmpty");
    }
    if (foo instanceof clafer.Absyn.GCardXor)
    {
       clafer.Absyn.GCardXor _gcardxor = (clafer.Absyn.GCardXor) foo;
       render("GCardXor");
    }
    if (foo instanceof clafer.Absyn.GCardOr)
    {
       clafer.Absyn.GCardOr _gcardor = (clafer.Absyn.GCardOr) foo;
       render("GCardOr");
    }
    if (foo instanceof clafer.Absyn.GCardMux)
    {
       clafer.Absyn.GCardMux _gcardmux = (clafer.Absyn.GCardMux) foo;
       render("GCardMux");
    }
    if (foo instanceof clafer.Absyn.GCardOpt)
    {
       clafer.Absyn.GCardOpt _gcardopt = (clafer.Absyn.GCardOpt) foo;
       render("GCardOpt");
    }
    if (foo instanceof clafer.Absyn.GCardInterval)
    {
       clafer.Absyn.GCardInterval _gcardinterval = (clafer.Absyn.GCardInterval) foo;
       render("(");
       render("GCardInterval");
       sh(_gcardinterval.ncard_);
       render(")");
    }
  }

  private static void sh(clafer.Absyn.Card foo)
  {
    if (foo instanceof clafer.Absyn.CardEmpty)
    {
       clafer.Absyn.CardEmpty _cardempty = (clafer.Absyn.CardEmpty) foo;
       render("CardEmpty");
    }
    if (foo instanceof clafer.Absyn.CardLone)
    {
       clafer.Absyn.CardLone _cardlone = (clafer.Absyn.CardLone) foo;
       render("CardLone");
    }
    if (foo instanceof clafer.Absyn.CardSome)
    {
       clafer.Absyn.CardSome _cardsome = (clafer.Absyn.CardSome) foo;
       render("CardSome");
    }
    if (foo instanceof clafer.Absyn.CardAny)
    {
       clafer.Absyn.CardAny _cardany = (clafer.Absyn.CardAny) foo;
       render("CardAny");
    }
    if (foo instanceof clafer.Absyn.CardNum)
    {
       clafer.Absyn.CardNum _cardnum = (clafer.Absyn.CardNum) foo;
       render("(");
       render("CardNum");
       sh(_cardnum.posinteger_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.CardInterval)
    {
       clafer.Absyn.CardInterval _cardinterval = (clafer.Absyn.CardInterval) foo;
       render("(");
       render("CardInterval");
       sh(_cardinterval.ncard_);
       render(")");
    }
  }

  private static void sh(clafer.Absyn.NCard foo)
  {
    if (foo instanceof clafer.Absyn.NCardX)
    {
       clafer.Absyn.NCardX _ncardx = (clafer.Absyn.NCardX) foo;
       render("(");
       render("NCardX");
       sh(_ncardx.posinteger_);
       sh(_ncardx.exinteger_);
       render(")");
    }
  }

  private static void sh(clafer.Absyn.ExInteger foo)
  {
    if (foo instanceof clafer.Absyn.ExIntegerAst)
    {
       clafer.Absyn.ExIntegerAst _exintegerast = (clafer.Absyn.ExIntegerAst) foo;
       render("ExIntegerAst");
    }
    if (foo instanceof clafer.Absyn.ExIntegerNum)
    {
       clafer.Absyn.ExIntegerNum _exintegernum = (clafer.Absyn.ExIntegerNum) foo;
       render("(");
       render("ExIntegerNum");
       sh(_exintegernum.posinteger_);
       render(")");
    }
  }

  private static void sh(clafer.Absyn.Name foo)
  {
    if (foo instanceof clafer.Absyn.Path)
    {
       clafer.Absyn.Path _path = (clafer.Absyn.Path) foo;
       render("(");
       render("Path");
       render("[");
       sh(_path.listmodid_);
       render("]");
       render(")");
    }
  }

  private static void sh(clafer.Absyn.Exp foo)
  {
    if (foo instanceof clafer.Absyn.TransitionExp)
    {
       clafer.Absyn.TransitionExp _transitionexp = (clafer.Absyn.TransitionExp) foo;
       render("(");
       render("TransitionExp");
       sh(_transitionexp.exp_1);
       sh(_transitionexp.transarrow_);
       sh(_transitionexp.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EDeclAllDisj)
    {
       clafer.Absyn.EDeclAllDisj _edeclalldisj = (clafer.Absyn.EDeclAllDisj) foo;
       render("(");
       render("EDeclAllDisj");
       sh(_edeclalldisj.decl_);
       sh(_edeclalldisj.exp_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EDeclAll)
    {
       clafer.Absyn.EDeclAll _edeclall = (clafer.Absyn.EDeclAll) foo;
       render("(");
       render("EDeclAll");
       sh(_edeclall.decl_);
       sh(_edeclall.exp_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EDeclQuantDisj)
    {
       clafer.Absyn.EDeclQuantDisj _edeclquantdisj = (clafer.Absyn.EDeclQuantDisj) foo;
       render("(");
       render("EDeclQuantDisj");
       sh(_edeclquantdisj.quant_);
       sh(_edeclquantdisj.decl_);
       sh(_edeclquantdisj.exp_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EDeclQuant)
    {
       clafer.Absyn.EDeclQuant _edeclquant = (clafer.Absyn.EDeclQuant) foo;
       render("(");
       render("EDeclQuant");
       sh(_edeclquant.quant_);
       sh(_edeclquant.decl_);
       sh(_edeclquant.exp_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EImpliesElse)
    {
       clafer.Absyn.EImpliesElse _eimplieselse = (clafer.Absyn.EImpliesElse) foo;
       render("(");
       render("EImpliesElse");
       sh(_eimplieselse.exp_1);
       sh(_eimplieselse.exp_2);
       sh(_eimplieselse.exp_3);
       render(")");
    }
    if (foo instanceof clafer.Absyn.LetExp)
    {
       clafer.Absyn.LetExp _letexp = (clafer.Absyn.LetExp) foo;
       render("(");
       render("LetExp");
       sh(_letexp.varbinding_);
       sh(_letexp.exp_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.TmpPatNever)
    {
       clafer.Absyn.TmpPatNever _tmppatnever = (clafer.Absyn.TmpPatNever) foo;
       render("(");
       render("TmpPatNever");
       sh(_tmppatnever.exp_);
       sh(_tmppatnever.patternscope_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.TmpPatSometime)
    {
       clafer.Absyn.TmpPatSometime _tmppatsometime = (clafer.Absyn.TmpPatSometime) foo;
       render("(");
       render("TmpPatSometime");
       sh(_tmppatsometime.exp_);
       sh(_tmppatsometime.patternscope_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.TmpPatLessOrOnce)
    {
       clafer.Absyn.TmpPatLessOrOnce _tmppatlessoronce = (clafer.Absyn.TmpPatLessOrOnce) foo;
       render("(");
       render("TmpPatLessOrOnce");
       sh(_tmppatlessoronce.exp_);
       sh(_tmppatlessoronce.patternscope_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.TmpPatAlways)
    {
       clafer.Absyn.TmpPatAlways _tmppatalways = (clafer.Absyn.TmpPatAlways) foo;
       render("(");
       render("TmpPatAlways");
       sh(_tmppatalways.exp_);
       sh(_tmppatalways.patternscope_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.TmpPatPrecede)
    {
       clafer.Absyn.TmpPatPrecede _tmppatprecede = (clafer.Absyn.TmpPatPrecede) foo;
       render("(");
       render("TmpPatPrecede");
       sh(_tmppatprecede.exp_1);
       sh(_tmppatprecede.exp_2);
       sh(_tmppatprecede.patternscope_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.TmpPatFollow)
    {
       clafer.Absyn.TmpPatFollow _tmppatfollow = (clafer.Absyn.TmpPatFollow) foo;
       render("(");
       render("TmpPatFollow");
       sh(_tmppatfollow.exp_1);
       sh(_tmppatfollow.exp_2);
       sh(_tmppatfollow.patternscope_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.TmpInitially)
    {
       clafer.Absyn.TmpInitially _tmpinitially = (clafer.Absyn.TmpInitially) foo;
       render("(");
       render("TmpInitially");
       sh(_tmpinitially.exp_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.TmpFinally)
    {
       clafer.Absyn.TmpFinally _tmpfinally = (clafer.Absyn.TmpFinally) foo;
       render("(");
       render("TmpFinally");
       sh(_tmpfinally.exp_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EIff)
    {
       clafer.Absyn.EIff _eiff = (clafer.Absyn.EIff) foo;
       render("(");
       render("EIff");
       sh(_eiff.exp_1);
       sh(_eiff.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EImplies)
    {
       clafer.Absyn.EImplies _eimplies = (clafer.Absyn.EImplies) foo;
       render("(");
       render("EImplies");
       sh(_eimplies.exp_1);
       sh(_eimplies.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EOr)
    {
       clafer.Absyn.EOr _eor = (clafer.Absyn.EOr) foo;
       render("(");
       render("EOr");
       sh(_eor.exp_1);
       sh(_eor.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EXor)
    {
       clafer.Absyn.EXor _exor = (clafer.Absyn.EXor) foo;
       render("(");
       render("EXor");
       sh(_exor.exp_1);
       sh(_exor.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EAnd)
    {
       clafer.Absyn.EAnd _eand = (clafer.Absyn.EAnd) foo;
       render("(");
       render("EAnd");
       sh(_eand.exp_1);
       sh(_eand.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.LtlU)
    {
       clafer.Absyn.LtlU _ltlu = (clafer.Absyn.LtlU) foo;
       render("(");
       render("LtlU");
       sh(_ltlu.exp_1);
       sh(_ltlu.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.TmpUntil)
    {
       clafer.Absyn.TmpUntil _tmpuntil = (clafer.Absyn.TmpUntil) foo;
       render("(");
       render("TmpUntil");
       sh(_tmpuntil.exp_1);
       sh(_tmpuntil.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.LtlW)
    {
       clafer.Absyn.LtlW _ltlw = (clafer.Absyn.LtlW) foo;
       render("(");
       render("LtlW");
       sh(_ltlw.exp_1);
       sh(_ltlw.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.TmpWUntil)
    {
       clafer.Absyn.TmpWUntil _tmpwuntil = (clafer.Absyn.TmpWUntil) foo;
       render("(");
       render("TmpWUntil");
       sh(_tmpwuntil.exp_1);
       sh(_tmpwuntil.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.LtlF)
    {
       clafer.Absyn.LtlF _ltlf = (clafer.Absyn.LtlF) foo;
       render("(");
       render("LtlF");
       sh(_ltlf.exp_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.TmpEventually)
    {
       clafer.Absyn.TmpEventually _tmpeventually = (clafer.Absyn.TmpEventually) foo;
       render("(");
       render("TmpEventually");
       sh(_tmpeventually.exp_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.LtlG)
    {
       clafer.Absyn.LtlG _ltlg = (clafer.Absyn.LtlG) foo;
       render("(");
       render("LtlG");
       sh(_ltlg.exp_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.TmpGlobally)
    {
       clafer.Absyn.TmpGlobally _tmpglobally = (clafer.Absyn.TmpGlobally) foo;
       render("(");
       render("TmpGlobally");
       sh(_tmpglobally.exp_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.LtlX)
    {
       clafer.Absyn.LtlX _ltlx = (clafer.Absyn.LtlX) foo;
       render("(");
       render("LtlX");
       sh(_ltlx.exp_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.TmpNext)
    {
       clafer.Absyn.TmpNext _tmpnext = (clafer.Absyn.TmpNext) foo;
       render("(");
       render("TmpNext");
       sh(_tmpnext.exp_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.ENeg)
    {
       clafer.Absyn.ENeg _eneg = (clafer.Absyn.ENeg) foo;
       render("(");
       render("ENeg");
       sh(_eneg.exp_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.ELt)
    {
       clafer.Absyn.ELt _elt = (clafer.Absyn.ELt) foo;
       render("(");
       render("ELt");
       sh(_elt.exp_1);
       sh(_elt.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EGt)
    {
       clafer.Absyn.EGt _egt = (clafer.Absyn.EGt) foo;
       render("(");
       render("EGt");
       sh(_egt.exp_1);
       sh(_egt.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EEq)
    {
       clafer.Absyn.EEq _eeq = (clafer.Absyn.EEq) foo;
       render("(");
       render("EEq");
       sh(_eeq.exp_1);
       sh(_eeq.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.ELte)
    {
       clafer.Absyn.ELte _elte = (clafer.Absyn.ELte) foo;
       render("(");
       render("ELte");
       sh(_elte.exp_1);
       sh(_elte.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EGte)
    {
       clafer.Absyn.EGte _egte = (clafer.Absyn.EGte) foo;
       render("(");
       render("EGte");
       sh(_egte.exp_1);
       sh(_egte.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.ENeq)
    {
       clafer.Absyn.ENeq _eneq = (clafer.Absyn.ENeq) foo;
       render("(");
       render("ENeq");
       sh(_eneq.exp_1);
       sh(_eneq.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EIn)
    {
       clafer.Absyn.EIn _ein = (clafer.Absyn.EIn) foo;
       render("(");
       render("EIn");
       sh(_ein.exp_1);
       sh(_ein.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.ENin)
    {
       clafer.Absyn.ENin _enin = (clafer.Absyn.ENin) foo;
       render("(");
       render("ENin");
       sh(_enin.exp_1);
       sh(_enin.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EQuantExp)
    {
       clafer.Absyn.EQuantExp _equantexp = (clafer.Absyn.EQuantExp) foo;
       render("(");
       render("EQuantExp");
       sh(_equantexp.quant_);
       sh(_equantexp.exp_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EAdd)
    {
       clafer.Absyn.EAdd _eadd = (clafer.Absyn.EAdd) foo;
       render("(");
       render("EAdd");
       sh(_eadd.exp_1);
       sh(_eadd.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.ESub)
    {
       clafer.Absyn.ESub _esub = (clafer.Absyn.ESub) foo;
       render("(");
       render("ESub");
       sh(_esub.exp_1);
       sh(_esub.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EMul)
    {
       clafer.Absyn.EMul _emul = (clafer.Absyn.EMul) foo;
       render("(");
       render("EMul");
       sh(_emul.exp_1);
       sh(_emul.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EDiv)
    {
       clafer.Absyn.EDiv _ediv = (clafer.Absyn.EDiv) foo;
       render("(");
       render("EDiv");
       sh(_ediv.exp_1);
       sh(_ediv.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.ERem)
    {
       clafer.Absyn.ERem _erem = (clafer.Absyn.ERem) foo;
       render("(");
       render("ERem");
       sh(_erem.exp_1);
       sh(_erem.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EGMax)
    {
       clafer.Absyn.EGMax _egmax = (clafer.Absyn.EGMax) foo;
       render("(");
       render("EGMax");
       sh(_egmax.exp_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EGMin)
    {
       clafer.Absyn.EGMin _egmin = (clafer.Absyn.EGMin) foo;
       render("(");
       render("EGMin");
       sh(_egmin.exp_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.ESum)
    {
       clafer.Absyn.ESum _esum = (clafer.Absyn.ESum) foo;
       render("(");
       render("ESum");
       sh(_esum.exp_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EProd)
    {
       clafer.Absyn.EProd _eprod = (clafer.Absyn.EProd) foo;
       render("(");
       render("EProd");
       sh(_eprod.exp_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.ECard)
    {
       clafer.Absyn.ECard _ecard = (clafer.Absyn.ECard) foo;
       render("(");
       render("ECard");
       sh(_ecard.exp_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EMinExp)
    {
       clafer.Absyn.EMinExp _eminexp = (clafer.Absyn.EMinExp) foo;
       render("(");
       render("EMinExp");
       sh(_eminexp.exp_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EDomain)
    {
       clafer.Absyn.EDomain _edomain = (clafer.Absyn.EDomain) foo;
       render("(");
       render("EDomain");
       sh(_edomain.exp_1);
       sh(_edomain.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.ERange)
    {
       clafer.Absyn.ERange _erange = (clafer.Absyn.ERange) foo;
       render("(");
       render("ERange");
       sh(_erange.exp_1);
       sh(_erange.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EUnion)
    {
       clafer.Absyn.EUnion _eunion = (clafer.Absyn.EUnion) foo;
       render("(");
       render("EUnion");
       sh(_eunion.exp_1);
       sh(_eunion.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EUnionCom)
    {
       clafer.Absyn.EUnionCom _eunioncom = (clafer.Absyn.EUnionCom) foo;
       render("(");
       render("EUnionCom");
       sh(_eunioncom.exp_1);
       sh(_eunioncom.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EDifference)
    {
       clafer.Absyn.EDifference _edifference = (clafer.Absyn.EDifference) foo;
       render("(");
       render("EDifference");
       sh(_edifference.exp_1);
       sh(_edifference.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EIntersection)
    {
       clafer.Absyn.EIntersection _eintersection = (clafer.Absyn.EIntersection) foo;
       render("(");
       render("EIntersection");
       sh(_eintersection.exp_1);
       sh(_eintersection.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EIntersectionDeprecated)
    {
       clafer.Absyn.EIntersectionDeprecated _eintersectiondeprecated = (clafer.Absyn.EIntersectionDeprecated) foo;
       render("(");
       render("EIntersectionDeprecated");
       sh(_eintersectiondeprecated.exp_1);
       sh(_eintersectiondeprecated.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EJoin)
    {
       clafer.Absyn.EJoin _ejoin = (clafer.Absyn.EJoin) foo;
       render("(");
       render("EJoin");
       sh(_ejoin.exp_1);
       sh(_ejoin.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.ClaferId)
    {
       clafer.Absyn.ClaferId _claferid = (clafer.Absyn.ClaferId) foo;
       render("(");
       render("ClaferId");
       sh(_claferid.name_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EInt)
    {
       clafer.Absyn.EInt _eint = (clafer.Absyn.EInt) foo;
       render("(");
       render("EInt");
       sh(_eint.posinteger_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EDouble)
    {
       clafer.Absyn.EDouble _edouble = (clafer.Absyn.EDouble) foo;
       render("(");
       render("EDouble");
       sh(_edouble.posdouble_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EReal)
    {
       clafer.Absyn.EReal _ereal = (clafer.Absyn.EReal) foo;
       render("(");
       render("EReal");
       sh(_ereal.posreal_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.EStr)
    {
       clafer.Absyn.EStr _estr = (clafer.Absyn.EStr) foo;
       render("(");
       render("EStr");
       sh(_estr.posstring_);
       render(")");
    }
  }

  private static void sh(clafer.Absyn.TransGuard foo)
  {
    if (foo instanceof clafer.Absyn.TransGuardX)
    {
       clafer.Absyn.TransGuardX _transguardx = (clafer.Absyn.TransGuardX) foo;
       render("(");
       render("TransGuardX");
       sh(_transguardx.exp_);
       render(")");
    }
  }

  private static void sh(clafer.Absyn.TransArrow foo)
  {
    if (foo instanceof clafer.Absyn.SyncTransArrow)
    {
       clafer.Absyn.SyncTransArrow _synctransarrow = (clafer.Absyn.SyncTransArrow) foo;
       render("SyncTransArrow");
    }
    if (foo instanceof clafer.Absyn.GuardedSyncTransArrow)
    {
       clafer.Absyn.GuardedSyncTransArrow _guardedsynctransarrow = (clafer.Absyn.GuardedSyncTransArrow) foo;
       render("(");
       render("GuardedSyncTransArrow");
       sh(_guardedsynctransarrow.transguard_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.NextTransArrow)
    {
       clafer.Absyn.NextTransArrow _nexttransarrow = (clafer.Absyn.NextTransArrow) foo;
       render("NextTransArrow");
    }
    if (foo instanceof clafer.Absyn.GuardedNextTransArrow)
    {
       clafer.Absyn.GuardedNextTransArrow _guardednexttransarrow = (clafer.Absyn.GuardedNextTransArrow) foo;
       render("(");
       render("GuardedNextTransArrow");
       sh(_guardednexttransarrow.transguard_);
       render(")");
    }
  }

  private static void sh(clafer.Absyn.PatternScope foo)
  {
    if (foo instanceof clafer.Absyn.PatScopeBefore)
    {
       clafer.Absyn.PatScopeBefore _patscopebefore = (clafer.Absyn.PatScopeBefore) foo;
       render("(");
       render("PatScopeBefore");
       sh(_patscopebefore.exp_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.PatScopeAfter)
    {
       clafer.Absyn.PatScopeAfter _patscopeafter = (clafer.Absyn.PatScopeAfter) foo;
       render("(");
       render("PatScopeAfter");
       sh(_patscopeafter.exp_);
       render(")");
    }
    if (foo instanceof clafer.Absyn.PatScopeBetweenAnd)
    {
       clafer.Absyn.PatScopeBetweenAnd _patscopebetweenand = (clafer.Absyn.PatScopeBetweenAnd) foo;
       render("(");
       render("PatScopeBetweenAnd");
       sh(_patscopebetweenand.exp_1);
       sh(_patscopebetweenand.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.PatScopeAfterUntil)
    {
       clafer.Absyn.PatScopeAfterUntil _patscopeafteruntil = (clafer.Absyn.PatScopeAfterUntil) foo;
       render("(");
       render("PatScopeAfterUntil");
       sh(_patscopeafteruntil.exp_1);
       sh(_patscopeafteruntil.exp_2);
       render(")");
    }
    if (foo instanceof clafer.Absyn.PatScopeEmpty)
    {
       clafer.Absyn.PatScopeEmpty _patscopeempty = (clafer.Absyn.PatScopeEmpty) foo;
       render("PatScopeEmpty");
    }
  }

  private static void sh(clafer.Absyn.Decl foo)
  {
    if (foo instanceof clafer.Absyn.DeclX)
    {
       clafer.Absyn.DeclX _declx = (clafer.Absyn.DeclX) foo;
       render("(");
       render("DeclX");
       render("[");
       sh(_declx.listlocid_);
       render("]");
       sh(_declx.exp_);
       render(")");
    }
  }

  private static void sh(clafer.Absyn.VarBinding foo)
  {
    if (foo instanceof clafer.Absyn.VarBindingX)
    {
       clafer.Absyn.VarBindingX _varbindingx = (clafer.Absyn.VarBindingX) foo;
       render("(");
       render("VarBindingX");
       sh(_varbindingx.locid_);
       sh(_varbindingx.name_);
       render(")");
    }
  }

  private static void sh(clafer.Absyn.Quant foo)
  {
    if (foo instanceof clafer.Absyn.QuantNo)
    {
       clafer.Absyn.QuantNo _quantno = (clafer.Absyn.QuantNo) foo;
       render("QuantNo");
    }
    if (foo instanceof clafer.Absyn.QuantNot)
    {
       clafer.Absyn.QuantNot _quantnot = (clafer.Absyn.QuantNot) foo;
       render("QuantNot");
    }
    if (foo instanceof clafer.Absyn.QuantLone)
    {
       clafer.Absyn.QuantLone _quantlone = (clafer.Absyn.QuantLone) foo;
       render("QuantLone");
    }
    if (foo instanceof clafer.Absyn.QuantOne)
    {
       clafer.Absyn.QuantOne _quantone = (clafer.Absyn.QuantOne) foo;
       render("QuantOne");
    }
    if (foo instanceof clafer.Absyn.QuantSome)
    {
       clafer.Absyn.QuantSome _quantsome = (clafer.Absyn.QuantSome) foo;
       render("QuantSome");
    }
  }

  private static void sh(clafer.Absyn.EnumId foo)
  {
    if (foo instanceof clafer.Absyn.EnumIdIdent)
    {
       clafer.Absyn.EnumIdIdent _enumidident = (clafer.Absyn.EnumIdIdent) foo;
       render("(");
       render("EnumIdIdent");
       sh(_enumidident.posident_);
       render(")");
    }
  }

  private static void sh(clafer.Absyn.ModId foo)
  {
    if (foo instanceof clafer.Absyn.ModIdIdent)
    {
       clafer.Absyn.ModIdIdent _modidident = (clafer.Absyn.ModIdIdent) foo;
       render("(");
       render("ModIdIdent");
       sh(_modidident.posident_);
       render(")");
    }
  }

  private static void sh(clafer.Absyn.LocId foo)
  {
    if (foo instanceof clafer.Absyn.LocIdIdent)
    {
       clafer.Absyn.LocIdIdent _locidident = (clafer.Absyn.LocIdIdent) foo;
       render("(");
       render("LocIdIdent");
       sh(_locidident.posident_);
       render(")");
    }
  }

  private static void sh(clafer.Absyn.ListDeclaration foo)
  {
     for (java.util.Iterator<clafer.Absyn.Declaration> it = foo.iterator(); it.hasNext();)
     {
       sh(it.next());
       if (it.hasNext())
         render(",");
     }
  }

  private static void sh(clafer.Absyn.ListEnumId foo)
  {
     for (java.util.Iterator<clafer.Absyn.EnumId> it = foo.iterator(); it.hasNext();)
     {
       sh(it.next());
       if (it.hasNext())
         render(",");
     }
  }

  private static void sh(clafer.Absyn.ListElement foo)
  {
     for (java.util.Iterator<clafer.Absyn.Element> it = foo.iterator(); it.hasNext();)
     {
       sh(it.next());
       if (it.hasNext())
         render(",");
     }
  }

  private static void sh(clafer.Absyn.ListExp foo)
  {
     for (java.util.Iterator<clafer.Absyn.Exp> it = foo.iterator(); it.hasNext();)
     {
       sh(it.next());
       if (it.hasNext())
         render(",");
     }
  }

  private static void sh(clafer.Absyn.ListTempModifier foo)
  {
     for (java.util.Iterator<clafer.Absyn.TempModifier> it = foo.iterator(); it.hasNext();)
     {
       sh(it.next());
       if (it.hasNext())
         render(",");
     }
  }

  private static void sh(clafer.Absyn.ListLocId foo)
  {
     for (java.util.Iterator<clafer.Absyn.LocId> it = foo.iterator(); it.hasNext();)
     {
       sh(it.next());
       if (it.hasNext())
         render(",");
     }
  }

  private static void sh(clafer.Absyn.ListModId foo)
  {
     for (java.util.Iterator<clafer.Absyn.ModId> it = foo.iterator(); it.hasNext();)
     {
       sh(it.next());
       if (it.hasNext())
         render(",");
     }
  }


  private static void pp(Integer n, int _i_) { buf_.append(n); buf_.append(" "); }
  private static void pp(Double d, int _i_) { buf_.append(String.format(java.util.Locale.ROOT, "%.15g ", d)); }
  private static void pp(String s, int _i_) { buf_.append(s); buf_.append(" "); }
  private static void pp(Character c, int _i_) { buf_.append("'" + c.toString() + "'"); buf_.append(" "); }
  private static void sh(Integer n) { render(n.toString()); }
  private static void sh(Double d) { render(String.format(java.util.Locale.ROOT, "%.15g", d)); }
  private static void sh(Character c) { render("'" + c.toString() + "'"); }
  private static void sh(String s) { printQuoted(s); }
  private static void printQuoted(String s) { render("\"" + s + "\""); }
  private static void indent()
  {
    int n = _n_;
    while (n > 0)
    {
      buf_.append(' ');
      n--;
    }
  }
  private static void backup()
  {
    int prev = buf_.length() - 1;
    if (buf_.charAt(prev) == ' ')
      buf_.setLength(prev);
  }
  private static void trim()
  {
    // Trim initial spaces
    int end = 0;
    int len = buf_.length();
    while (end < len && buf_.charAt(end) == ' ')
      end++;
    buf_.delete(0, end);
    // Trim trailing spaces
    end = buf_.length();
    while (end > 0 && buf_.charAt(end-1) == ' ')
      end--;
    buf_.setLength(end);
  }
  private static int _n_ = 0;
  private static StringBuilder buf_ = new StringBuilder(INITIAL_BUFFER_SIZE);
}

