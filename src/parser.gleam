import gleam/int
import gleam/list
import gleam/string
import header.{
  type BinderMode, type Pos, type Syntax, type SyntaxParam, AppSyntax,
  IdentSyntax, ImmedAppSyntax, IntersectionTypeSyntax, LambdaSyntax, ManyMode,
  NatSyntax, NatTypeSyntax, PiSyntax, Pos, SortSyntax, SyntaxParam, TypeMode,
  TypeSort, ZeroMode,
}

pub type Parser(a) {
  Parser(
    run: fn(Pos, String, List(String)) ->
      Result(#(Pos, List(String), a), Failure),
  )
}

pub type Failure {
  Bubbler(msg: String, pos: Pos, expected: String)
  Normal(msg: String, pos: Pos, expected: String)
}

pub fn parse(src: String, parser: Parser(a)) -> Result(a, String) {
  case parser.run(Pos(src, 1, 1), "", string.to_graphemes(src)) {
    Ok(#(_, _, a)) -> Ok(a)
    Error(err) ->
      case err.expected {
        "" -> Error(err.msg <> " at " <> header.pretty_pos(err.pos))
        _ ->
          Error(
            err.msg
            <> " at "
            <> header.pretty_pos(err.pos)
            <> ", expected "
            <> err.expected,
          )
      }
  }
}

pub fn satisfy(pred: fn(String) -> Bool) -> Parser(String) {
  Parser(fn(pos, expected, chars) {
    case chars {
      [] -> Error(Normal("unexpected EOF", pos, expected))
      [c, ..rest] ->
        case pred(c) {
          True ->
            case c {
              "\n" -> Ok(#(Pos(pos.src, pos.line + 1, 0), rest, c))
              _ -> Ok(#(Pos(pos.src, pos.line, pos.col + 1), rest, c))
            }
          False ->
            case c {
              "\n" -> Error(Normal("unexpected newline", pos, expected))
              _ -> Error(Normal("unexpected " <> c, pos, expected))
            }
        }
    }
  })
}

pub fn map(parser: Parser(a), f: fn(a) -> b) -> Parser(b) {
  Parser(fn(pos, expected, chars) {
    case parser.run(pos, expected, chars) {
      Ok(#(pos2, rest, a)) -> Ok(#(pos2, rest, f(a)))
      Error(e) -> Error(e)
    }
  })
}

pub fn either(p1: Parser(a), p2: Parser(a)) -> Parser(a) {
  Parser(fn(pos, expected, chars) {
    case p1.run(pos, expected, chars) {
      Ok(out) -> Ok(out)
      Error(Normal(_, _, _)) -> p2.run(pos, expected, chars)
      Error(Bubbler(_, _, _)) as e -> e
    }
  })
}

pub fn many0(parser: Parser(a)) -> Parser(List(a)) {
  Parser(fn(pos, expected, chars) {
    case parser.run(pos, expected, chars) {
      Ok(#(pos2, rest, a)) ->
        case many0(parser).run(pos2, expected, rest) {
          Ok(#(pos3, rest2, others)) -> Ok(#(pos3, rest2, [a, ..others]))
          Error(Normal(_, _, _)) -> panic as "many0 returned normal failure"
          Error(Bubbler(_, _, _)) as e -> e
        }
      Error(Normal(_, _, _)) -> Ok(#(pos, chars, []))
      Error(Bubbler(_, _, _) as e) -> Error(e)
    }
  })
}

pub fn do(p1: Parser(a), f: fn(a) -> Parser(b)) -> Parser(b) {
  Parser(fn(pos, expected, chars) {
    case p1.run(pos, expected, chars) {
      Ok(#(pos2, rest, a)) -> f(a).run(pos2, expected, rest)
      Error(e) -> Error(e)
    }
  })
}

pub fn return(a: a) -> Parser(a) {
  Parser(fn(pos, _, chars) { Ok(#(pos, chars, a)) })
}

pub fn many(parser: Parser(a)) -> Parser(List(a)) {
  use first <- do(parser)
  use rest <- do(many0(parser))
  return([first, ..rest])
}

pub fn label(parser: Parser(a), expected: String) -> Parser(a) {
  Parser(fn(pos, _, chars) {
    case parser.run(pos, expected, chars) {
      Ok(out) -> Ok(out)
      Error(Normal(msg, p, _)) -> Error(Normal(msg, p, expected))
      e -> e
    }
  })
}

pub fn commit(k: fn() -> Parser(a)) -> Parser(a) {
  Parser(fn(pos, expected, chars) {
    case k().run(pos, expected, chars) {
      Ok(out) -> Ok(out)
      Error(Normal(msg, p, e)) | Error(Bubbler(msg, p, e)) ->
        Error(Bubbler(msg, p, e))
    }
  })
}

pub fn char(c: String) -> Parser(String) {
  label(satisfy(fn(c2) { c == c2 }), c)
}

pub fn lowercase() -> Parser(String) {
  satisfy(fn(c) {
    string.contains(does: "abcdefghijklmnopqrstuvwxyz", contain: c)
  })
}

pub fn uppercase() -> Parser(String) {
  satisfy(fn(c) {
    string.contains(does: "ABCDEFGHIJKLMNOPQRSTUVWXYZ", contain: c)
  })
}

pub fn digit() -> Parser(String) {
  satisfy(fn(c) { string.contains(does: "1234567890", contain: c) })
}

pub fn alphanum() -> Parser(String) {
  either(lowercase(), either(uppercase(), digit()))
}

pub fn get_pos() -> Parser(Pos) {
  Parser(fn(pos, _, chars) { Ok(#(pos, chars, pos)) })
}

pub fn lazy(thunk: fn() -> Parser(a)) -> Parser(a) {
  Parser(fn(pos, expected, chars) { thunk().run(pos, expected, chars) })
}

pub fn any_of(parsers: List(Parser(a))) -> Parser(a) {
  case parsers {
    [] -> panic as "any_of on empty parser list"
    [p] -> p
    [p, ..rest] -> either(p, any_of(rest))
  }
}

pub fn string(s: String) -> Parser(String) {
  // this function is hilariously slow
  // thou shalt not prematurely optimize
  // it works, okay
  case string.pop_grapheme(s) {
    Ok(#(c, "")) -> char(c)
    Ok(#(c, rest)) -> do(char(c), fn(_) { map(string(rest), fn(_) { s }) })
    Error(_) -> panic as "empty string"
  }
}

pub fn maybe(parser: Parser(a)) -> Parser(Result(a, Nil)) {
  Parser(fn(pos, expected, chars) {
    case parser.run(pos, expected, chars) {
      Ok(#(pos2, rest, a)) -> Ok(#(pos2, rest, Ok(a)))
      Error(Normal(_, _, _)) -> Ok(#(pos, chars, Error(Nil)))
      Error(Bubbler(_, _, _) as e) -> Error(e)
    }
  })
}

pub fn keyword(s: String) {
  use _ <- do(string(s))
  Parser(fn(pos, expected, chars) {
    case any_of([lowercase(), uppercase(), digit()]).run(pos, expected, chars) {
      Ok(#(_, _, c)) -> Error(Normal("unexpected " <> c, pos, expected))
      Error(_) -> Ok(#(pos, chars, s))
    }
  })
}

pub fn ws(k: fn() -> Parser(a)) -> Parser(a) {
  use _ <- do(many0(any_of([char(" "), char("\n"), char("\t")])))
  k()
}

pub fn ident_string() -> Parser(String) {
  use first <- do(lowercase())
  use rest <- do(many0(either(char("_"), alphanum())))
  return(first <> string.concat(rest))
}

pub fn pattern_string() -> Parser(String) {
  either(ident_string(), {
    use _ <- do(char("_"))
    use res <- do(maybe(ident_string()))
    case res {
      Ok(s) -> return("_" <> s)
      Error(_) -> return("_")
    }
  })
}

pub fn ident() -> Parser(Syntax) {
  use pos <- do(get_pos())
  use s <- do(ident_string())
  return(IdentSyntax(s, pos))
}

pub fn nat() -> Parser(Syntax) {
  use pos <- do(get_pos())
  use n_str <- do(many(digit()))
  let assert Ok(n) = int.parse(string.concat(n_str))
  return(NatSyntax(n, pos))
}

pub fn nat_type() -> Parser(Syntax) {
  use pos <- do(get_pos())
  use _ <- do(keyword("Nat"))
  return(NatTypeSyntax(pos))
}

pub fn type_type() -> Parser(Syntax) {
  use pos <- do(get_pos())
  use _ <- do(keyword("Type"))
  return(SortSyntax(TypeSort, pos))
}

pub fn zero_or_type_binder() -> Parser(Syntax) {
  use pos <- do(get_pos())
  use res <- do(either(char("<"), char("{")))
  use <- commit()
  use <- ws()
  use x <- do(pattern_string())
  use <- ws()
  use _ <- do(char(":"))
  use t <- do(lazy(expr))
  use mode <- do(case res {
    "{" -> {
      use _ <- do(char("}"))
      return(ZeroMode)
    }
    "<" -> {
      use _ <- do(char(">"))
      return(TypeMode)
    }
    _ -> panic as "impossible binder mode"
  })
  use <- ws()
  use res <- do(either(string("->"), string("=>")))
  use u <- do(lazy(expr))
  case res {
    "->" -> return(LambdaSyntax(mode, x, t, u, pos))
    "=>" -> return(PiSyntax(mode, x, t, u, pos))
    _ -> panic as "impossible zero or type binder"
  }
}

pub fn parens() -> Parser(Syntax) {
  use pos <- do(get_pos())
  use _ <- do(char("("))
  use <- ws()
  use res <- do(
    maybe({
      use x <- do(pattern_string())
      use <- ws()
      use _ <- do(char(":"))
      return(x)
    }),
  )
  case res {
    Ok(x) -> {
      use <- commit()
      use t <- do(lazy(expr))
      use _ <- do(char(")"))
      use <- ws()
      use res <- do(label(
        any_of([string("->"), string("=>"), string("&")]),
        "binder",
      ))
      use body <- do(lazy(expr))
      case res {
        "->" -> {
          return(LambdaSyntax(ManyMode, x, t, body, pos))
        }
        "=>" -> {
          return(PiSyntax(ManyMode, x, t, body, pos))
        }
        "&" -> {
          return(IntersectionTypeSyntax(x, t, body, pos))
        }
        _ -> panic as "impossible binder"
      }
    }
    Error(_) -> {
      use e <- do(lazy(expr))
      use _ <- do(char(")"))
      return(e)
    }
  }
}

pub fn parse_param() -> Parser(SyntaxParam) {
  use <- ws()
  use res <- do(any_of([char("("), char("{"), char("<")]))
  use <- ws()
  use <- commit()
  use x <- do(pattern_string())
  use <- ws()
  use _ <- do(char(":"))
  use t <- do(lazy(expr))
  case res {
    "(" -> {
      use _ <- do(char(")"))
      return(SyntaxParam(ManyMode, x, t))
    }
    "{" -> {
      use _ <- do(char("}"))
      return(SyntaxParam(ZeroMode, x, t))
    }
    "<" -> {
      use _ <- do(char(">"))
      return(SyntaxParam(TypeMode, x, t))
    }
    _ -> panic as "impossible param mode"
  }
}

fn build_pi(pos: Pos, params: List(SyntaxParam), rett: Syntax) -> Syntax {
  case params {
    [] -> rett
    [param, ..rest] ->
      PiSyntax(param.mode, param.name, param.ty, build_pi(pos, rest, rett), pos)
  }
}

fn build_lambda(pos: Pos, params: List(SyntaxParam), body: Syntax) -> Syntax {
  case params {
    [] -> body
    [param, ..rest] ->
      LambdaSyntax(
        param.mode,
        param.name,
        param.ty,
        build_lambda(pos, rest, body),
        pos,
      )
  }
}

pub fn let_binding() -> Parser(Syntax) {
  use pos <- do(get_pos())
  use _ <- do(keyword("let"))
  use <- ws()
  use <- commit()
  use x <- do(pattern_string())
  use <- ws()
  use params <- do(many0(parse_param()))
  use <- ws()
  use _ <- do(char(":"))
  use t <- do(lazy(expr))
  use _ <- do(char("="))
  use v <- do(lazy(expr))
  use _ <- do(keyword("in"))
  use e <- do(lazy(expr))
  return(ImmedAppSyntax(
    x,
    build_pi(pos, params, t),
    v,
    build_lambda(pos, params, e),
    pos,
  ))
}

pub type Suffix {
  AppSuffix(BinderMode, Syntax, pos: Pos)
}

pub fn expr() -> Parser(Syntax) {
  use <- ws()
  use e <- do(label(
    any_of([
      nat_type(),
      type_type(),
      nat(),
      parens(),
      zero_or_type_binder(),
      let_binding(),
      ident(),
    ]),
    "expression",
  ))
  use <- ws()
  use suffices <- do(
    many0({
      use <- ws()
      any_of([
        {
          use pos <- do(get_pos())
          use _ <- do(char("("))
          use <- commit()
          use arg <- do(lazy(expr))
          use _ <- do(char(")"))
          return(AppSuffix(ManyMode, arg, pos))
        },
        {
          use pos <- do(get_pos())
          use _ <- do(char("{"))
          use <- commit()
          use arg <- do(lazy(expr))
          use _ <- do(char("}"))
          return(AppSuffix(ZeroMode, arg, pos))
        },
        {
          use pos <- do(get_pos())
          use _ <- do(char("<"))
          use <- commit()
          use arg <- do(lazy(expr))
          use _ <- do(char(">"))
          return(AppSuffix(TypeMode, arg, pos))
        },
      ])
    }),
  )
  let e = case suffices {
    [] -> e
    _ ->
      list.fold(suffices, e, fn(ex, suffix) {
        case suffix {
          AppSuffix(mode, arg, pos) -> AppSyntax(mode, ex, arg, pos)
        }
      })
  }
  use <- ws()
  return(e)
}
