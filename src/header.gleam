import gleam/int

pub type Pos {
  Pos(src: String, line: Int, col: Int)
}

pub fn pretty_pos(pos: Pos) -> String {
  int.to_string(pos.line) <> ":" <> int.to_string(pos.col)
}

pub type BinderMode {
  ZeroMode
  ManyMode
  TypeMode
}

pub fn pretty_mode(m: BinderMode) -> String {
  case m {
    ZeroMode -> "erased"
    ManyMode -> "relevant"
    TypeMode -> "type-abstraction"
  }
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

pub type Syntax {
  LambdaSyntax(BinderMode, String, Result(Syntax, Nil), Syntax, pos: Pos)
  IdentSyntax(String, pos: Pos)
  AppSyntax(BinderMode, Syntax, Syntax, pos: Pos)
  LetSyntax(String, Syntax, Syntax, Syntax, pos: Pos)
  DefSyntax(String, Syntax, Syntax, Syntax, pos: Pos)
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

pub fn get_pos(s: Syntax) -> Pos {
  case s {
    LambdaSyntax(_, _, _, _, pos) -> pos
    IdentSyntax(_, pos) -> pos
    AppSyntax(_, _, _, pos) -> pos
    LetSyntax(_, _, _, _, pos) -> pos
    DefSyntax(_, _, _, _, pos) -> pos
    NatSyntax(_, pos) -> pos
    NatTypeSyntax(pos) -> pos
    SortSyntax(_, pos) -> pos
    PiSyntax(_, _, _, _, pos) -> pos
    JSyntax(_, _, _, _, _, pos) -> pos
    IntersectionTypeSyntax(_, _, _, pos) -> pos
    IntersectionSyntax(_, _, _, pos) -> pos
    FstSyntax(_, pos) -> pos
    SndSyntax(_, pos) -> pos
    EqSyntax(_, _, _, pos) -> pos
    ReflSyntax(_, _, pos) -> pos
    CastSyntax(_, _, _, pos) -> pos
    ExFalsoSyntax(_, pos) -> pos
  }
}

pub fn pretty_syntax(s: Syntax) -> String {
  case s {
    LambdaSyntax(mode, x, Ok(t), e, _) ->
      pretty_syntax_param(SyntaxParam(mode, x, t)) <> "-> " <> pretty_syntax(e)
    LambdaSyntax(mode, x, Error(Nil), e, _) -> {
      let outer = "-> " <> pretty_syntax(e)
      case mode {
        ManyMode -> "(" <> x <> ")" <> outer
        ZeroMode -> "{" <> x <> "}" <> outer
        TypeMode -> "<" <> x <> ">" <> outer
      }
    }
    IdentSyntax(name, _) -> name
    AppSyntax(ManyMode, foo, bar, _) ->
      "(" <> pretty_syntax(foo) <> ")(" <> pretty_syntax(bar) <> ")"
    AppSyntax(ZeroMode, foo, bar, _) ->
      "(" <> pretty_syntax(foo) <> "){" <> pretty_syntax(bar) <> "}"
    AppSyntax(TypeMode, foo, bar, _) ->
      "(" <> pretty_syntax(foo) <> ")<" <> pretty_syntax(bar) <> ">"
    LetSyntax(x, t, v, scope, _) ->
      "let "
      <> x
      <> ": "
      <> pretty_syntax(t)
      <> " = "
      <> pretty_syntax(v)
      <> " in "
      <> pretty_syntax(scope)
    DefSyntax(x, t, v, scope, _) ->
      "def "
      <> x
      <> ": "
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

pub type Index {
  Index(int: Int)
}

pub type Level {
  Level(int: Int)
}

pub fn lvl_to_idx(size: Level, lvl: Level) -> Index {
  Index(size.int - lvl.int - 1)
}

pub type Binder {
  Lambda(mode: BinderMode)
  Pi(mode: BinderMode, ty: Term)
  InterT(ty: Term)
  Let(mode: BinderMode, val: Term)
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
  Ident(BinderMode, Index, String, pos: Pos)
  Binder(Binder, String, Term, pos: Pos)
  Ctor0(Ctor0, pos: Pos)
  Ctor1(Ctor1, Term, pos: Pos)
  Ctor2(Ctor2, Term, Term, pos: Pos)
  Ctor3(Ctor3, Term, Term, Term, pos: Pos)
  Ctor5(Ctor5, Term, Term, Term, Term, Term, pos: Pos)
}

pub fn pretty_param(
  mode: BinderMode,
  x: String,
  mb_t: Result(Term, Nil),
) -> String {
  let inner = case mb_t {
    Ok(t) -> x <> ": " <> pretty_term(t)
    Error(Nil) -> x
  }
  case mode {
    ManyMode -> "(" <> inner <> ")"
    ZeroMode -> "{" <> inner <> "}"
    TypeMode -> "<" <> inner <> ">"
  }
}

pub fn pretty_term(term: Term) -> String {
  case term {
    Ident(_, _, s, _) -> s
    Binder(Lambda(mode), x, e, _) ->
      pretty_param(mode, x, Error(Nil)) <> "-> " <> pretty_term(e)
    Binder(Pi(ManyMode, t), "_", u, _) ->
      "(" <> pretty_term(t) <> ")=>" <> pretty_term(u)
    Binder(Pi(mode, t), x, u, _) ->
      pretty_param(mode, x, Ok(t)) <> "=> " <> pretty_term(u)
    Binder(InterT(t), x, u, _) ->
      pretty_param(ManyMode, x, Ok(t)) <> "& " <> pretty_term(u)
    Binder(Let(mode, v), x, e, _) ->
      "let "
      <> pretty_param(mode, x, Error(Nil))
      <> " = "
      <> pretty_term(v)
      <> " in "
      <> pretty_term(e)
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

pub fn inc(lvl: Level) -> Level {
  Level(lvl.int + 1)
}

pub type Virtual {
  VNeutral(Neutral)
  VSort(Sort)
  VNat(Int)
  VNatType
  VPi(String, BinderMode, Virtual, fn(Virtual) -> Virtual)
  VLambda(String, BinderMode, fn(Virtual) -> Virtual)
}

pub type Neutral {
  VIdent(String, BinderMode, Level)
  VApp(Neutral, Virtual)
}

fn pretty_neutral(n: Neutral) -> String {
  case n {
    VIdent(x, _, _) -> x
    VApp(m, v) -> "(" <> pretty_neutral(m) <> ")(" <> pretty_virtual(v) <> ")"
  }
}

pub fn pretty_virtual(v: Virtual) -> String {
  case v {
    VNeutral(n) -> pretty_neutral(n)
    VSort(TypeSort) -> "Type"
    VSort(KindSort) -> "Kind"
    VNat(n) -> int.to_string(n)
    VNatType -> "Nat"
    VPi("_", mode, a, b) ->
      "("
      <> pretty_virtual(a)
      <> ")=> "
      <> pretty_virtual(b(VNeutral(VIdent("_", mode, Level(0)))))
    VPi(x, mode, a, b) ->
      "("
      <> x
      <> ": "
      <> pretty_virtual(a)
      <> ")=> "
      <> pretty_virtual(b(VNeutral(VIdent(x, mode, Level(0)))))
    VLambda(x, mode, f) ->
      "("
      <> x
      <> ")-> "
      <> pretty_virtual(f(VNeutral(VIdent(x, mode, Level(0)))))
  }
}
