import parser

pub fn main() -> Nil {
  let _ = echo parser.parse("77h_1Ell*o world", parser.expr())
  Nil
}
