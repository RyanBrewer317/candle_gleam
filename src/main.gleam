import elab
import gleam/io
import gleam/result
import header
import parser

fn go() {
  let code =
    "
let zero{t: Type}(z: t)(s: t=>t): t = z in
let succ{t: Type}(n: t=>(t=>t)=>t)(z: t)(s: t=>t): t = s(n(z)(s)) in
let three{t: Type}: t=>(t=>t)=>t = succ{t}(succ{t}(succ{t}(zero{t}))) in
let nil{t: Type}(n: t)(c: Nat=>t=>t): t = n in
let cons{t: Type}(a: Nat)(v: t=>(Nat=>t=>t)=>t)(n: t)(c: Nat=>t=>t): t = c(a)(v(n)(c)) in
let one_two{t: Type}: t=>(Nat=>t=>t)=>t = cons{t}(1)(cons{t}(2)(nil{t})) in
one_two{Nat}
  (0)
  ((h: Nat)-> (t: Nat)-> h)
  "
  io.println(code)
  use s <- result.try(parser.parse(code, parser.expr()))
  // io.println(header.pretty_syntax(s))
  use #(t, ty) <- result.try(elab.infer(elab.empty_ctx, s))
  // io.println(header.pretty_term(t))
  let t2 = elab.eval(t, [])
  io.println(header.pretty_virtual(t2) <> " : " <> header.pretty_virtual(ty))
  Ok(Nil)
}

pub fn main() -> Nil {
  case go() {
    Error(e) -> {
      io.println(e)
      Nil
    }
    Ok(Nil) -> Nil
  }
}
