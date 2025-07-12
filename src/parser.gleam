import gleam/int
import gleam/list
import gleam/string
import header.{
  type BinderMode, type Pos, type Syntax, type SyntaxParam, AppSyntax, DefSyntax,
  IdentSyntax, IntersectionTypeSyntax, LambdaSyntax, LetSyntax, ManyMode,
  NatSyntax, NatTypeSyntax, PiSyntax, Pos, SortSyntax, SyntaxParam, TypeMode,
  TypeSort, ZeroMode,
}

pub type Parser(a) {
  Parser(run: fn(Pos, List(String)) -> Result(#(Pos, List(String), a), Failure))
}

pub type Failure {
  Bubbler(msg: String, pos: Pos, expected: String)
  Normal(msg: String, pos: Pos, expected: String)
}

pub fn parse(src: String, parser: Parser(a)) -> Result(a, String) {
  case parser.run(Pos(src, 1, 1), string.to_graphemes(src)) {
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
  Parser(fn(pos, chars) {
    case chars {
      [] -> Error(Normal("unexpected EOF", pos, ""))
      [c, ..rest] ->
        case pred(c) {
          True ->
            case c {
              "\n" -> Ok(#(Pos(pos.src, pos.line + 1, 0), rest, c))
              _ -> Ok(#(Pos(pos.src, pos.line, pos.col + 1), rest, c))
            }
          False ->
            case c {
              "\n" -> Error(Normal("unexpected newline", pos, ""))
              _ -> Error(Normal("unexpected " <> c, pos, ""))
            }
        }
    }
  })
}

pub fn map(parser: Parser(a), f: fn(a) -> b) -> Parser(b) {
  Parser(fn(pos, chars) {
    case parser.run(pos, chars) {
      Ok(#(pos2, rest, a)) -> Ok(#(pos2, rest, f(a)))
      Error(e) -> Error(e)
    }
  })
}

pub fn either(p1: Parser(a), p2: Parser(a)) -> Parser(a) {
  Parser(fn(pos, chars) {
    case p1.run(pos, chars) {
      Ok(out) -> Ok(out)
      Error(Normal(_, _, _)) -> p2.run(pos, chars)
      Error(Bubbler(_, _, _)) as e -> e
    }
  })
}

pub fn many0(parser: Parser(a)) -> Parser(List(a)) {
  Parser(fn(pos, chars) {
    case parser.run(pos, chars) {
      Ok(#(pos2, rest, a)) ->
        case many0(parser).run(pos2, rest) {
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
  Parser(fn(pos, chars) {
    case p1.run(pos, chars) {
      Ok(#(pos2, rest, a)) -> f(a).run(pos2, rest)
      Error(e) -> Error(e)
    }
  })
}

pub fn return(a: a) -> Parser(a) {
  Parser(fn(pos, chars) { Ok(#(pos, chars, a)) })
}

pub fn many(parser: Parser(a)) -> Parser(List(a)) {
  use first <- do(parser)
  use rest <- do(many0(parser))
  return([first, ..rest])
}

pub fn label(parser: Parser(a), expected: String) -> Parser(a) {
  Parser(fn(pos, chars) {
    case parser.run(pos, chars) {
      Ok(out) -> Ok(out)
      Error(Normal(msg, p, _)) -> Error(Normal(msg, p, expected))
      e -> e
    }
  })
}

pub fn commit(k: fn() -> Parser(a)) -> Parser(a) {
  Parser(fn(pos, chars) {
    case k().run(pos, chars) {
      Ok(out) -> Ok(out)
      Error(Normal(msg, p, e)) | Error(Bubbler(msg, p, e)) ->
        Error(Bubbler(msg, p, e))
    }
  })
}

pub fn char(c: String) -> Parser(String) {
  satisfy(fn(c2) { c == c2 }) |> label(c)
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
  Parser(fn(pos, chars) { Ok(#(pos, chars, pos)) })
}

pub fn lazy(thunk: fn() -> Parser(a)) -> Parser(a) {
  Parser(fn(pos, chars) { thunk().run(pos, chars) })
}

pub fn any_of(parsers: List(Parser(a))) -> Parser(a) {
  case parsers {
    [] -> panic as "any_of on empty parser list"
    [p] -> p
    [p, ..rest] -> either(p, any_of(rest))
  }
}

pub fn string(s: String) -> Parser(String) {
  map(string_helper(s), fn(_) { s })
  |> label(s)
}

fn string_helper(s: String) -> Parser(String) {
  case string.pop_grapheme(s) {
    Ok(#(c, "")) -> char(c)
    Ok(#(c, rest)) -> do(char(c), fn(_) { string(rest) })
    Error(_) -> panic as "empty string"
  }
}

pub fn maybe(parser: Parser(a)) -> Parser(Result(a, Nil)) {
  Parser(fn(pos, chars) {
    case parser.run(pos, chars) {
      Ok(#(pos2, rest, a)) -> Ok(#(pos2, rest, Ok(a)))
      Error(Normal(_, _, _)) -> Ok(#(pos, chars, Error(Nil)))
      Error(Bubbler(_, _, _) as e) -> Error(e)
    }
  })
}

pub fn keyword(s: String) {
  use _ <- do(string(s))
  Parser(fn(pos, chars) {
    case any_of([lowercase(), uppercase(), digit()]).run(pos, chars) {
      Ok(#(_, _, c)) -> Error(Normal("unexpected " <> c, pos, s))
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
  |> label("identifier")
}

pub fn ident() -> Parser(Syntax) {
  use pos <- do(get_pos())
  use s <- do(ident_string())
  use <- ws()
  use mb_lam <- do(maybe(string("->")))
  case mb_lam {
    Ok(_) -> {
      use <- commit()
      use body <- do(lazy(expr))
      return(LambdaSyntax(ManyMode, s, Error(Nil), body, pos))
    }
    Error(Nil) -> return(IdentSyntax(s, pos))
  }
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

pub fn relevant_but_ignored() -> Parser(Syntax) {
  use pos <- do(get_pos())
  use x <- do(pattern_string())
  use <- commit()
  use <- ws()
  use _ <- do(string("->"))
  use e <- do(lazy(expr))
  return(LambdaSyntax(ManyMode, x, Error(Nil), e, pos))
}

pub fn zero_or_type_binder() -> Parser(Syntax) {
  use pos <- do(get_pos())
  use res <- do(either(char("<"), char("{")))
  let #(mode, end) = case res {
    "{" -> #(ZeroMode, char("}"))
    "<" -> #(TypeMode, char(">"))
    _ -> panic as "impossible binder mode"
  }
  use <- commit()
  use <- ws()
  use x_pos <- do(get_pos())
  use mb_x <- do(
    maybe(either(map(pattern_string(), Ok), map(ident_string(), Error))),
  )
  case mb_x {
    Ok(id) -> {
      use <- ws()
      use res <- do(maybe(char(":")))
      case res {
        Ok(_) -> {
          let x = case id {
            Ok(x) -> x
            Error(x) -> x
          }
          use t <- do(lazy(expr))
          use _ <- do(end)
          use <- ws()
          use res <- do(either(string("->"), string("=>")))
          use u <- do(lazy(expr))
          case res {
            "->" -> return(LambdaSyntax(mode, x, Ok(t), u, pos))
            "=>" -> return(PiSyntax(mode, x, t, u, pos))
            _ -> panic as "impossible zero or type binder"
          }
        }
        Error(_) -> {
          use _ <- do(end)
          use <- ws()
          case id {
            Ok(x) -> {
              use _ <- do(string("->"))
              use e <- do(lazy(expr))
              return(LambdaSyntax(mode, x, Error(Nil), e, pos))
            }
            Error(x) -> {
              use arrow <- do(either(string("->"), string("=>")))
              use e <- do(lazy(expr))
              case arrow {
                "->" -> return(LambdaSyntax(mode, x, Error(Nil), e, pos))
                "=>" ->
                  return(PiSyntax(mode, "_", IdentSyntax(x, x_pos), e, pos))
                _ -> panic as "impossible zero or type binder"
              }
            }
          }
        }
      }
    }
    Error(Nil) -> {
      use t <- do(lazy(expr))
      use _ <- do(end)
      use <- ws()
      use _ <- do(string("=>"))
      use u <- do(lazy(expr))
      return(PiSyntax(mode, "_", t, u, pos))
    }
  }
}

pub fn parens() -> Parser(Syntax) {
  use pos <- do(get_pos())
  use _ <- do(char("("))
  use <- commit()
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
          return(LambdaSyntax(ManyMode, x, Ok(t), body, pos))
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
      use e <- do(lazy(expr) |> label("expression or binding"))
      use _ <- do(
        char(")")
        |> label(case e {
          IdentSyntax(_, _) -> ": or )"
          _ -> ")"
        }),
      )
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
    [param, ..rest] -> {
      PiSyntax(param.mode, param.name, param.ty, build_pi(pos, rest, rett), pos)
    }
  }
}

fn build_lambda(pos: Pos, params: List(SyntaxParam), body: Syntax) -> Syntax {
  case params {
    [] -> body
    [param, ..rest] ->
      LambdaSyntax(
        param.mode,
        param.name,
        Ok(param.ty),
        build_lambda(pos, rest, body),
        pos,
      )
  }
}

pub fn let_binding() -> Parser(Syntax) {
  use pos <- do(get_pos())
  use res <- do(either(keyword("let"), keyword("def")))
  use <- ws()
  use <- commit()
  use x <- do(pattern_string())
  use <- ws()
  use params <- do(many0(parse_param()))
  use <- ws()
  use _ <- do(char(":") |> label(": or parameter"))
  use t <- do(lazy(expr))
  use _ <- do(char("="))
  use v <- do(lazy(expr))
  use _ <- do(keyword("in"))
  use e <- do(lazy(expr))
  let t = build_pi(pos, params, t)
  let v = build_lambda(pos, params, v)
  case res {
    "let" -> return(LetSyntax(x, t, v, e, pos))
    "def" -> return(DefSyntax(x, t, v, e, pos))
    _ -> panic as "impossible binder"
  }
}

pub type Suffix {
  AppSuffix(BinderMode, Syntax, pos: Pos)
  PiSuffix(Syntax, pos: Pos)
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
      relevant_but_ignored(),
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
        {
          use pos <- do(get_pos())
          use _ <- do(string("=>"))
          use <- commit()
          use rett <- do(lazy(expr))
          return(PiSuffix(rett, pos))
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
          PiSuffix(rett, pos) -> PiSyntax(ManyMode, "_", ex, rett, pos)
        }
      })
  }
  use <- ws()
  return(e)
}
