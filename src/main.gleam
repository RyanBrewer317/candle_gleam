import header
import parser

pub fn main() -> Nil {
  let code = "let id{t: Type}(x: t): t = x in id{Nat}(3)"
  echo code
  let _ =
    echo parser.parse(code, parser.map(parser.expr(), header.pretty_syntax))
  Nil
}
