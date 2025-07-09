import elab
import gleam/io
import gleam/result
import header
import parser

fn go() {
  let code =
    "
def nat{t: Type}: Type = t=>(t=>t)=>t in
let zero{t: Type}: nat<t> = z-> s-> z in
let succ{t: Type}: nat<t>=>nat<t> = n-> z-> s-> s(n(z)(s)) in
let add{t: Type}: nat<nat<t>>=>nat<t>=>nat<t> = a-> b-> a(b)(succ{t}) in
let two{t: Type}: nat<t> = succ{t}(succ{t}(zero{t})) in
let four{t: Type}: nat<t> = add{t}(two{nat<t>})(two{t}) in
let vec<t: Type><n: nat<t>>: Type = t=>(Nat=>t=>t)=>t in
let nil{t: Type}: vec<t><zero{t}> = n-> c-> n in
let cons{t: Type}{m: nat<t>}: Nat=>vec<t><m>=>vec<t><succ{t}(m)> 
  = a-> v-> n-> c-> c(a)(v(n)(c)) in
let one_two{t: Type}: vec<t><two{t}> 
  = cons{t}{succ{t}(zero{t})}(1)(cons{t}{zero{t}}(2)(nil{t})) in
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
