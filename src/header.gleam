import gleam/int
import gleam/list
import gleam/string

pub type Pretty(a) {
  Pretty(go: fn(a) -> String)
}

pub type Pos {
  Pos(src: String, line: Int, col: Int)
}

pub fn pretty_pos(pos: Pos) -> String {
  int.to_string(pos.line) <> ":" <> int.to_string(pos.col)
}

pub const pr_pos = Pretty(pretty_pos)

pub type BinderMode {
  ZeroMode
  ManyMode
  TypeMode
}

pub type Sort {
  TypeSort
  KindSort
}

pub type SyntaxParam {
  SyntaxParam(mode: BinderMode, name: String, ty: Syntax)
}

pub fn pretty_syntax_param(param: SyntaxParam) -> String {
  case param.mode {
    ZeroMode -> "{" <> param.name <> ": " <> pretty_syntax(param.ty) <> "}"
    ManyMode -> "(" <> param.name <> ": " <> pretty_syntax(param.ty) <> ")"
    TypeMode -> "<" <> param.name <> ": " <> pretty_syntax(param.ty) <> ">"
  }
}

pub const pr_syntax_param = Pretty(pretty_syntax_param)

pub type Syntax {
  LambdaSyntax(BinderMode, String, Syntax, Syntax, pos: Pos)
  IdentSyntax(String, pos: Pos)
  AppSyntax(BinderMode, Syntax, Syntax, pos: Pos)
  ImmedAppSyntax(String, List(SyntaxParam), Syntax, Syntax, Syntax, pos: Pos)
  NatSyntax(Int, pos: Pos)
  NatTypeSyntax(pos: Pos)
  SortSyntax(Sort, pos: Pos)
  PiSyntax(BinderMode, String, Syntax, Syntax, pos: Pos)
  JSyntax(Syntax, Syntax, Syntax, Syntax, Syntax, pos: Pos)
  IntersectionTypeSyntax(String, Syntax, Syntax, pos: Pos)
  IntersectionSyntax(Syntax, Syntax, Syntax, pos: Pos)
  FstSyntax(Syntax, pos: Pos)
  SndSyntax(Syntax, pos: Pos)
  EqSyntax(Syntax, Syntax, Syntax, pos: Pos)
  ReflSyntax(Syntax, Syntax, pos: Pos)
  CastSyntax(Syntax, Syntax, Syntax, pos: Pos)
  ExFalsoSyntax(Syntax, pos: Pos)
}

pub fn pretty_syntax(s: Syntax) -> String {
  case s {
    LambdaSyntax(mode, x, t, e, _) ->
      pretty_syntax_param(SyntaxParam(mode, x, t)) <> "-> " <> pretty_syntax(e)
    IdentSyntax(name, _) -> name
    AppSyntax(ManyMode, foo, bar, _) ->
      "(" <> pretty_syntax(foo) <> ")(" <> pretty_syntax(bar) <> ")"
    AppSyntax(ZeroMode, foo, bar, _) ->
      "(" <> pretty_syntax(foo) <> "){" <> pretty_syntax(bar) <> "}"
    AppSyntax(TypeMode, foo, bar, _) ->
      "(" <> pretty_syntax(foo) <> ")<" <> pretty_syntax(bar) <> ">"
    ImmedAppSyntax(x, [], t, v, scope, _) ->
      "let "
      <> x
      <> ": "
      <> pretty_syntax(t)
      <> " = "
      <> pretty_syntax(v)
      <> " in "
      <> pretty_syntax(scope)
    ImmedAppSyntax(x, params, t, v, scope, _) ->
      "let "
      <> x
      <> "("
      <> string.join(list.map(params, pretty_syntax_param), ", ")
      <> "): "
      <> pretty_syntax(t)
      <> " = "
      <> pretty_syntax(v)
      <> " in "
      <> pretty_syntax(scope)
    NatSyntax(n, _) -> int.to_string(n)
    NatTypeSyntax(_) -> "Nat"
    SortSyntax(TypeSort, _) -> "Type"
    SortSyntax(KindSort, _) -> "Kind"
    PiSyntax(mode, x, t, u, _) ->
      pretty_syntax_param(SyntaxParam(mode, x, t)) <> "=> " <> pretty_syntax(u)
    JSyntax(a, b, e, at, prop, _) ->
      "J("
      <> pretty_syntax(a)
      <> ", "
      <> pretty_syntax(b)
      <> ", "
      <> pretty_syntax(e)
      <> ", "
      <> pretty_syntax(at)
      <> ", "
      <> pretty_syntax(prop)
      <> ")"
    IntersectionTypeSyntax(x, t, u, _) ->
      pretty_syntax_param(SyntaxParam(ManyMode, x, t))
      <> "& "
      <> pretty_syntax(u)
    IntersectionSyntax(l, r, t, _) ->
      "["
      <> pretty_syntax(l)
      <> ", "
      <> pretty_syntax(r)
      <> "; "
      <> pretty_syntax(t)
      <> "]"
    FstSyntax(a, _) -> ".1(" <> pretty_syntax(a) <> ")"
    SndSyntax(a, _) -> ".2(" <> pretty_syntax(a) <> ")"
    EqSyntax(a, b, t, _) ->
      "("
      <> pretty_syntax(a)
      <> ") =["
      <> pretty_syntax(t)
      <> "] ("
      <> pretty_syntax(b)
      <> ")"
    ReflSyntax(a, t, _) ->
      "refl(" <> pretty_syntax(a) <> "; " <> pretty_syntax(t) <> ")"
    CastSyntax(a, b, eq, _) ->
      "cast("
      <> pretty_syntax(a)
      <> ", "
      <> pretty_syntax(b)
      <> ", "
      <> pretty_syntax(eq)
      <> ")"
    ExFalsoSyntax(a, _) -> "exfalso(" <> pretty_syntax(a) <> ")"
  }
}

pub const pr_syntax = Pretty(pretty_syntax)

pub type Binder {
  Lambda(mode: BinderMode)
  Pi(mode: BinderMode)
  InterT(mode: BinderMode)
  // always ZeroMode
}

pub type Ctor0 {
  Diamond
  Sort(Sort)
  NatT
  Nat(Int)
}

pub type Ctor1 {
  Fst
  Snd
  ExFalso
}

pub type Ctor2 {
  App(BinderMode)
  Refl
}

pub type Ctor3 {
  Inter
  Eq
  Cast
}

pub type Ctor5 {
  J
}

pub type Term {
  Ident(BinderMode, Sort, Int, String, pos: Pos)
  Binder(Binder, String, Term, Term, pos: Pos)
  Ctor0(Ctor0, pos: Pos)
  Ctor1(Ctor1, Term, pos: Pos)
  Ctor2(Ctor2, Term, Term, pos: Pos)
  Ctor3(Ctor3, Term, Term, Term, pos: Pos)
  Ctor5(Ctor5, Term, Term, Term, Term, Term, pos: Pos)
}

pub fn pretty_param(mode: BinderMode, x: String, t: Term) -> String {
  case mode {
    ManyMode -> "(" <> x <> ": " <> pretty_term(t) <> ")"
    ZeroMode -> "{" <> x <> ": " <> pretty_term(t) <> "}"
    TypeMode -> "<" <> x <> ": " <> pretty_term(t) <> ">"
  }
}

pub fn pretty_term(term: Term) -> String {
  case term {
    Ident(_, _, _, s, _) -> s
    Binder(Lambda(mode), x, t, e, _) ->
      pretty_param(mode, x, t) <> "-> " <> pretty_term(e)
    Binder(Pi(mode), x, t, u, _) ->
      pretty_param(mode, x, t) <> "=> " <> pretty_term(u)
    Binder(InterT(mode), x, t, u, _) ->
      pretty_param(mode, x, t) <> "& " <> pretty_term(u)
    Ctor0(Diamond, _) -> "Diamond"
    Ctor0(Sort(TypeSort), _) -> "Type"
    Ctor0(Sort(KindSort), _) -> "Kind"
    Ctor0(NatT, _) -> "Nat"
    Ctor0(Nat(n), _) -> int.to_string(n)
    Ctor1(Fst, a, _) -> ".1(" <> pretty_term(a) <> ")"
    Ctor1(Snd, a, _) -> ".2(" <> pretty_term(a) <> ")"
    Ctor1(ExFalso, a, _) -> "exfalso(" <> pretty_term(a) <> ")"
    Ctor2(App(mode), foo, bar, _) ->
      "("
      <> pretty_term(foo)
      <> ")"
      <> case mode {
        ManyMode -> "(" <> pretty_term(bar) <> ")"
        ZeroMode -> "{" <> pretty_term(bar) <> "}"
        TypeMode -> "<" <> pretty_term(bar) <> ">"
      }
    Ctor2(Refl, a, t, _) ->
      "refl(" <> pretty_term(a) <> "; " <> pretty_term(t) <> ")"
    Ctor3(Inter, a, b, t, _) ->
      "["
      <> pretty_term(a)
      <> ", "
      <> pretty_term(b)
      <> "; "
      <> pretty_term(t)
      <> "]"
    Ctor3(Eq, a, b, t, _) ->
      "("
      <> pretty_term(a)
      <> ") =["
      <> pretty_term(t)
      <> "] ("
      <> pretty_term(b)
      <> ")"
    Ctor3(Cast, a, b, eq, _) ->
      "cast("
      <> pretty_term(a)
      <> ", "
      <> pretty_term(b)
      <> ", "
      <> pretty_term(eq)
      <> ")"
    Ctor5(J, a, b, eq, at, p, _) ->
      "J("
      <> pretty_term(a)
      <> ", "
      <> pretty_term(b)
      <> ", "
      <> pretty_term(eq)
      <> ", "
      <> pretty_term(at)
      <> ", "
      <> pretty_term(p)
      <> ")"
  }
}
