import gleam/int
import gleam/string
import header.{type Pos, type Syntax, IdentSyntax, Pos, NatSyntax}

pub type Parser(a) {
  Parser(
    run: fn(Pos, String, List(String)) ->
      Result(#(Pos, List(String), a), Failure),
  )
}

pub type Failure {
  Bubbler(msg: String)
  Normal(msg: String)
}

pub fn parse(src: String, parser: Parser(a)) -> Result(a, String) {
  case parser.run(Pos(src, 0, 0), "", string.to_graphemes(src)) {
    Ok(#(_, _, a)) -> Ok(a)
    Error(err) -> Error(err.msg)
  }
}

fn error_msg(err: String, expected: String) -> Result(a, Failure) {
  case expected {
    "" -> Error(Normal(err))
    _ -> Error(Normal(err <> ", expected " <> expected))
  }
}

pub fn satisfy(pred: fn(String) -> Bool) -> Parser(String) {
  Parser(fn(pos, expected, chars) {
    case chars {
      [] -> error_msg("unexpected EOF", expected)
      [c, ..rest] ->
        case pred(c) {
          True ->
            case c {
              "\n" -> Ok(#(Pos(pos.src, pos.line + 1, 0), rest, c))
              _ -> Ok(#(Pos(pos.src, pos.line, pos.col + 1), rest, c))
            }
          False -> error_msg("unexpected newline", expected)
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
      Error(Normal(_)) -> p2.run(pos, expected, chars)
      Error(Bubbler(_)) as e -> e
    }
  })
}

pub fn many0(parser: Parser(a)) -> Parser(List(a)) {
  Parser(fn(pos, expected, chars) {
    case parser.run(pos, expected, chars) {
      Ok(#(pos2, rest, a)) ->
        case many0(parser).run(pos2, expected, rest) {
          Ok(#(pos3, rest2, others)) -> Ok(#(pos3, rest2, [a, ..others]))
          Error(Normal(_)) -> panic as "many0 returned normal failure"
          Error(Bubbler(_)) as e -> e
        }
      Error(Normal(_)) -> Ok(#(pos, chars, []))
      Error(Bubbler(_) as e) -> Error(e)
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
  Parser(fn(pos, _, chars) { parser.run(pos, expected, chars) })
}

pub fn commit(k: fn() -> Parser(a)) -> Parser(a) {
  Parser(fn(pos, expected, chars) {
    case k().run(pos, expected, chars) {
      Ok(out) -> Ok(out)
      Error(Normal(e)) | Error(Bubbler(e)) -> Error(Bubbler(e))
    }
  })
}

pub fn char(c: String) -> Parser(String) {
  satisfy(fn(c2) { c == c2 })
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

pub fn ws(k: fn() -> Parser(a)) -> Parser(a) {
  use _ <- do(many0(any_of([char(" "), char("\n"), char("\t")])))
  k()
}

pub fn ident_string() -> Parser(String) {
  use first <- do(lowercase())
  use rest <- do(many0(either(char("_"), alphanum())))
  return(first <> string.concat(rest))
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

pub fn expr() -> Parser(Syntax) {
  use <- ws()
  use e <- do(any_of([ident(), nat()]))
  use <- ws()
  return(e)
}
