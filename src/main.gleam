import header
import parser

pub fn main() -> Nil {
  let code = "(f: (n: Nat)=>Nat) -> f(3)"
  echo code
  let _ =
    echo parser.parse(code, parser.map(parser.expr(), header.pretty_syntax))
  Nil
}
