import gleam/result
import header.{
  type BinderMode, type Index, type Level, type Neutral, type Pos, type Syntax,
  type Term, type Value, App, AppSyntax, Binder, Ctor0, Ctor1, Ctor2, Ctor3,
  DefSyntax, Eq, EqSyntax, Ident, IdentSyntax, Index, J, JSyntax, KindSort,
  Lambda, LambdaSyntax, Let, LetSyntax, Level, ManyMode, Nat, NatSyntax, NatT,
  NatTypeSyntax, Pi, PiSyntax, Refl, ReflSyntax, Sort, SortSyntax, TypeMode,
  TypeSort, VApp, VEq, VIdent, VJ, VLambda, VNat, VNatType, VNeutral, VPi, VRefl,
  VSort, ZeroMode, inc, pretty_mode, pretty_pos, pretty_term, pretty_value,
}

fn erase(t: Value) -> Value {
  case t {
    VNeutral(n) -> VNeutral(erase_neutral(n))
    VLambda(_, ZeroMode, e, p) ->
      erase(e(VNeutral(VIdent("", ZeroMode, Level(0), p))))
    VLambda(x, mode, e, p) -> VLambda(x, mode, fn(arg) { erase(e(arg)) }, p)
    VPi(x, mode, a, b, p) ->
      VPi(x, mode, erase(a), fn(arg) { erase(b(arg)) }, p)
    VEq(a, b, t, p) -> VEq(erase(a), erase(b), erase(t), p)
    VRefl(_, p) -> VLambda("x", ManyMode, fn(x) {x}, p)
    VJ(e, _, _) -> erase(e)
    VNat(_, _) | VNatType(_) | VSort(_, _) -> t
  }
}

fn erase_neutral(n: Neutral) -> Neutral {
  case n {
    VIdent(_, _, _, _) -> n
    VApp(ZeroMode, a, _, _) -> erase_neutral(a)
    VApp(m, a, b, p) -> VApp(m, erase_neutral(a), erase(b), p)
  }
}

fn app(mode: BinderMode, foo: Value, bar: Value) -> Value {
  case foo {
    VNeutral(neutral) ->
      VNeutral(VApp(mode, neutral, bar, header.value_pos(bar)))
    VLambda(_, _, f, _) -> f(bar)
    _ -> panic as "impossible virtual application"
  }
}

fn lookup(l: List(a), i: Int) -> Result(a, Nil) {
  case l, i {
    [], _ -> Error(Nil)
    [x, ..], 0 -> Ok(x)
    [_, ..rest], i -> lookup(rest, i - 1)
  }
}

pub fn eval(t: Term, env: List(Value)) -> Value {
  case t {
    Ident(_mode, idx, _s, _pos) ->
      case lookup(env, idx.int) {
        Ok(v) -> v
        Error(_) -> panic as "out-of-scope var during eval"
      }
    Ctor0(Sort(TypeSort), pos) -> VSort(TypeSort, pos)
    Ctor0(Sort(KindSort), pos) -> VSort(KindSort, pos)
    Binder(Pi(mode, t), x, u, pos) ->
      VPi(x, mode, eval(t, env), fn(arg) { eval(u, [arg, ..env]) }, pos)
    Binder(Lambda(mode), x, e, pos) ->
      VLambda(x, mode, fn(arg) { eval(e, [arg, ..env]) }, pos)
    Ctor2(App(mode), foo, bar, _) -> app(mode, eval(foo, env), eval(bar, env))
    Binder(Let(_mode, v), _x, e, _) -> eval(e, [eval(v, env), ..env])
    Ctor0(Nat(n), pos) -> VNat(n, pos)
    Ctor0(NatT, pos) -> VNatType(pos)
    Ctor3(Eq, a, b, t, pos) ->
      VEq(eval(a, env), eval(b, env), eval(t, env), pos)
    Ctor1(Refl, a, pos) -> VRefl(eval(a, env), pos)
    Ctor2(J, e, p, pos) -> VJ(eval(e, env), eval(p, env), pos)
    _ -> todo
  }
}

pub type Context {
  Context(
    level: Level,
    types: List(Value),
    env: List(Value),
    scope: List(#(String, #(BinderMode, Value))),
  )
}

pub const empty_ctx = Context(Level(0), [], [], [])

fn eq(lvl: Level, a: Value, b: Value) -> Bool {
  eq_helper(lvl, erase(a), erase(b))
}

fn eq_helper(lvl: Level, a: Value, b: Value) -> Bool {
  let eqh = fn(a, b) { eq_helper(lvl, a, b) }
  case a, b {
    VSort(s1, _), VSort(s2, _) -> s1 == s2
    VPi(x, m1, t1, u1, pos), VPi(_, m2, t2, u2, _) -> {
      let dummy = VNeutral(VIdent(x, m1, lvl, pos))
      m1 == m2 && eqh(t1, t2) && eq_helper(inc(lvl), u1(dummy), u2(dummy))
    }
    VLambda(x, m, f, pos), b -> {
      let dummy = VNeutral(VIdent(x, m, lvl, pos))
      eq_helper(inc(lvl), f(dummy), app(m, b, dummy))
    }
    a, VLambda(x, m, f, pos) -> {
      let dummy = VNeutral(VIdent(x, m, lvl, pos))
      eq_helper(inc(lvl), app(m, a, dummy), f(dummy))
    }
    VNeutral(VIdent(_, _, i, _)), VNeutral(VIdent(_, _, j, _)) -> i == j
    VNeutral(VApp(m1, n1, arg1, _)), VNeutral(VApp(m2, n2, arg2, _)) ->
      m1 == m2 && eqh(VNeutral(n1), VNeutral(n2)) && eqh(arg1, arg2)
    VNat(n, _), VNat(m, _) -> n == m
    VNatType(_), VNatType(_) -> True
    VEq(a1, b1, t1, _), VEq(a2, b2, t2, _) ->
      eqh(a1, a2) && eqh(b1, b2) && eqh(t1, t2)
    VRefl(a1, _), VRefl(a2, _) -> eqh(a1, a2)
    VJ(e1, p1, _), VJ(e2, p2, _) -> eqh(e1, e2) && eqh(p1, p2)
    _, _ -> False
  }
}

fn inc_idx(i: Index) -> Index {
  Index(i.int + 1)
}

fn rel_occurs(t: Term, x: Index) -> Result(Pos, Nil) {
  case t {
    Ident(_, y, _, pos) if x == y -> Ok(pos)
    Ident(_, _, _, _) -> Error(Nil)
    Binder(Let(_, v), _, e, _) ->
      result.or(rel_occurs(v, x), rel_occurs(e, inc_idx(x)))
    Binder(_, _, e, _) -> rel_occurs(e, inc_idx(x))
    Ctor0(_, _) -> Error(Nil)
    Ctor1(_, a, _) -> rel_occurs(a, x)
    Ctor2(App(ZeroMode), a, _, _) -> rel_occurs(a, x)
    Ctor2(_, a, b, _) -> result.or(rel_occurs(a, x), rel_occurs(b, x))
    Ctor3(_, a, b, c, _) ->
      rel_occurs(a, x)
      |> result.or(rel_occurs(b, x))
      |> result.or(rel_occurs(c, x))
  }
}

pub fn check(ctx: Context, s: Syntax, ty: Value) -> Result(Term, String) {
  case s, ty {
    LambdaSyntax(mode1, x, Ok(xt), body, pos), VPi(_, mode2, a, b, _) -> {
      use _ <- result.try(case mode1 == mode2 {
        True -> Ok(Nil)
        False ->
          Error(
            "mode mismatch: "
            <> pretty_mode(mode1)
            <> " and "
            <> pretty_mode(mode2),
          )
      })
      use #(xt2, _xtt) <- result.try(infer(ctx, xt))
      let xt3 = eval(xt2, ctx.env)
      use _ <- result.try(case eq(ctx.level, xt3, a) {
        True -> Ok(Nil)
        False ->
          Error(
            "type mismatch: " <> pretty_term(xt2) <> " and " <> pretty_value(a),
          )
      })
      let v = VNeutral(VIdent(x, mode1, ctx.level, pos))
      let ctx2 =
        Context(
          level: inc(ctx.level),
          types: [a, ..ctx.types],
          env: [v, ..ctx.env],
          scope: [#(x, #(mode1, a)), ..ctx.scope],
        )
      use body2 <- result.try(check(ctx2, body, b(v)))
      use _ <- result.try(case mode1 {
        ZeroMode ->
          case rel_occurs(body2, Index(0)) {
            Ok(pos2) ->
              Error("relevant usage of erased variable at " <> pretty_pos(pos2))
            Error(Nil) -> Ok(Nil)
          }
        _ -> Ok(Nil)
      })
      Ok(Binder(Lambda(mode1), x, body2, pos))
    }
    LambdaSyntax(mode1, x, Error(Nil), body, pos), VPi(_, mode2, a, b, _) -> {
      use _ <- result.try(case mode1 == mode2 {
        True -> Ok(Nil)
        False ->
          Error(
            "mode mismatch: "
            <> pretty_mode(mode1)
            <> " and "
            <> pretty_mode(mode2),
          )
      })
      let dummy = VNeutral(VIdent(x, mode1, ctx.level, pos))
      let ctx2 =
        Context(
          level: inc(ctx.level),
          types: [a, ..ctx.types],
          env: [dummy, ..ctx.env],
          scope: [#(x, #(mode1, a)), ..ctx.scope],
        )
      use body2 <- result.try(check(ctx2, body, b(dummy)))
      Ok(Binder(Lambda(mode1), x, body2, pos))
    }
    LetSyntax(x, xt, v, e, pos), ty -> {
      use #(xt2, xtt) <- result.try(infer(ctx, xt))
      use _ <- result.try(case xtt {
        VSort(_, _) -> Ok(Nil)
        _ -> Error("type annotation must be a type")
      })
      let xt2v = eval(xt2, ctx.env)
      use v2 <- result.try(check(ctx, v, xt2v))
      let v3 = eval(v2, ctx.env)
      let ctx2 =
        Context(..ctx, env: [v3, ..ctx.env], scope: [
          #(x, #(ManyMode, xt2v)),
          ..ctx.scope
        ])
      use e2 <- result.try(check(ctx2, e, ty))
      Ok(Binder(Let(mode: ManyMode, val: v2), x, e2, pos))
    }
    ReflSyntax(x, pos), VEq(a, b, _t, _) -> {
      use #(x2, _xt) <- result.try(infer(ctx, x))
      let x3 = eval(x2, ctx.env)
      use _ <- result.try(case eq(ctx.level, x3, a) {
        True ->
          case eq(ctx.level, x3, b) {
            True -> Ok(Nil)
            False ->
              Error(
                "type mismatch between "
                <> pretty_value(x3)
                <> " and "
                <> pretty_value(b)
                <> " at "
                <> pretty_pos(pos),
              )
          }
        False ->
          Error(
            "type mismatch between "
            <> pretty_value(x3)
            <> " and "
            <> pretty_value(a)
            <> " at "
            <> pretty_pos(pos),
          )
      })
      Ok(Ctor1(Refl, x2, pos))
    }
    s, ty -> {
      use #(v, ty2) <- result.try(infer(ctx, s))
      case eq(ctx.level, ty, ty2) {
        True -> Ok(v)
        False -> {
          Error(
            "type mismatch between `"
            <> pretty_value(ty)
            <> "` and `"
            <> pretty_value(ty2)
            <> "` at "
            <> pretty_pos(header.get_pos(s)),
          )
        }
      }
    }
  }
}

fn scan(i: Int, l: List(#(k, v)), key: k) -> Result(#(v, Int), Nil) {
  case l {
    [] -> Error(Nil)
    [#(k, v), ..] if k == key -> Ok(#(v, i))
    [_, ..rest] -> scan(i + 1, rest, key)
  }
}

pub fn infer(ctx: Context, s: Syntax) -> Result(#(Term, Value), String) {
  case s {
    IdentSyntax(str, pos) -> {
      case scan(0, ctx.scope, str) {
        Ok(#(#(mode, ty), i)) -> Ok(#(Ident(mode, Index(i), str, pos), ty))
        Error(Nil) -> Error("undefined variable " <> str)
      }
    }
    SortSyntax(TypeSort, pos) ->
      Ok(#(Ctor0(Sort(TypeSort), pos), VSort(KindSort, pos)))
    SortSyntax(KindSort, _) -> panic as "parsed impossible kind literal"
    PiSyntax(mode, str, a, b, pos) -> {
      use #(a2, at) <- result.try(infer(ctx, a))
      case at {
        VSort(s1, _) -> {
          use _ <- result.try(case s1, mode {
            KindSort, ManyMode ->
              Error(
                "relevant lambdas can't bind types (" <> pretty_pos(pos) <> ")",
              )
            _, _ -> Ok(Nil)
          })
          let dummy = VNeutral(VIdent(str, mode, ctx.level, pos))
          let a3 = eval(a2, ctx.env)
          let ctx2 =
            Context(
              level: inc(ctx.level),
              types: [a3, ..ctx.types],
              env: [dummy, ..ctx.env],
              scope: [#(str, #(mode, a3)), ..ctx.scope],
            )
          use #(b2, bt) <- result.try(infer(ctx2, b))
          case bt, mode {
            VSort(KindSort, _) as s, TypeMode ->
              Ok(#(Binder(Pi(mode, a2), str, b2, pos), s))
            VSort(KindSort, _), ManyMode ->
              Error(
                "relevant functions can't return types ("
                <> pretty_pos(pos)
                <> ")",
              )
            VSort(KindSort, _), ZeroMode ->
              Error(
                "erased functions can't return types ("
                <> pretty_pos(pos)
                <> ")",
              )
            VSort(TypeSort, _), TypeMode ->
              Error(
                "type abstractions must return types ("
                <> pretty_pos(pos)
                <> ")",
              )
            VSort(TypeSort, _) as s, _ ->
              Ok(#(Binder(Pi(mode, a2), str, b2, pos), s))
            _, _ -> Error("pi right-side be a type (" <> pretty_pos(pos) <> ")")
          }
        }
        _ -> Error("pi left-side should be a type (" <> pretty_pos(pos) <> ")")
      }
    }
    LambdaSyntax(mode, str, Ok(xt), body, pos) -> {
      use #(xt2, xtt) <- result.try(infer(ctx, xt))
      use _ <- result.try(case mode, xtt {
        ManyMode, VSort(KindSort, _) ->
          Error("relevant lambda binding can't bind types")
        _, VSort(TypeSort, _) -> Ok(Nil)
        _, _ -> Error("type annotation in lambda must be a type")
      })
      let xt2v = eval(xt2, ctx.env)
      let v = VNeutral(VIdent(str, mode, ctx.level, pos))
      let ctx2 =
        Context(
          level: inc(ctx.level),
          types: [xt2v, ..ctx.types],
          env: [v, ..ctx.env],
          scope: [#(str, #(mode, xt2v)), ..ctx.scope],
        )
      use #(body2, _body2t) <- result.try(infer(ctx2, body))
      Ok(#(
        Binder(Lambda(mode), str, body2, pos),
        VPi(
          str,
          mode,
          xt2v,
          fn(x) {
            let ctx2 =
              Context(
                inc(ctx.level),
                types: [xt2v, ..ctx.env],
                env: [x, ..ctx.env],
                scope: [#(str, #(mode, xt2v)), ..ctx.scope],
              )
            let assert Ok(#(_, t)) = infer(ctx2, body)
            t
          },
          pos,
        ),
      ))
    }
    LambdaSyntax(_, _, Error(Nil), _, pos) ->
      Error("can't infer the type of the lambda at " <> pretty_pos(pos))
    AppSyntax(mode1, foo, bar, pos) -> {
      use #(foo2, foot) <- result.try(infer(ctx, foo))
      case foot {
        VPi(_, mode2, a, b, _) if mode1 == mode2 -> {
          use bar2 <- result.try(check(ctx, bar, a))
          let t = b(eval(bar2, ctx.env))
          Ok(#(Ctor2(App(mode1), foo2, bar2, pos), t))
        }
        VPi(_, mode2, _, _, _) ->
          Error(
            "mode-mismatch between "
            <> pretty_mode(mode1)
            <> " and "
            <> pretty_mode(mode2)
            <> " at "
            <> pretty_pos(pos),
          )
        _ ->
          Error(
            "application to non-function `"
            <> pretty_value(foot)
            <> "` at "
            <> pretty_pos(pos),
          )
      }
    }
    LetSyntax(x, xt, v, e, pos) -> {
      use #(xt2, xtt) <- result.try(infer(ctx, xt))
      use _ <- result.try(case xtt {
        VSort(_, _) -> Ok(Nil)
        _ -> Error("type annotation must be a type")
      })
      let xt2v = eval(xt2, ctx.env)
      use v2 <- result.try(check(ctx, v, xt2v))
      let v3 = eval(v2, ctx.env)
      let ctx2 =
        Context(..ctx, env: [v3, ..ctx.env], scope: [
          #(x, #(ManyMode, xt2v)),
          ..ctx.scope
        ])
      use #(e2, et) <- result.try(infer(ctx2, e))
      Ok(#(Binder(Let(mode: ManyMode, val: v2), x, e2, pos), et))
    }
    DefSyntax(x, xt, v, e, pos) -> {
      use #(xt2, xtt) <- result.try(infer(ctx, xt))
      use _ <- result.try(case xtt {
        VSort(_, _) -> Ok(Nil)
        _ -> Error("type annotation must be a type")
      })
      let xt2v = eval(xt2, ctx.env)
      use v2 <- result.try(check(ctx, v, xt2v))
      let v3 = eval(v2, ctx.env)
      let ctx2 =
        Context(..ctx, env: [v3, ..ctx.env], scope: [
          #(x, #(ZeroMode, xt2v)),
          ..ctx.scope
        ])
      use #(e2, et) <- result.try(infer(ctx2, e))
      Ok(#(Binder(Let(mode: ZeroMode, val: v2), x, e2, pos), et))
    }
    NatSyntax(n, pos) -> Ok(#(Ctor0(Nat(n), pos), VNatType(pos)))
    NatTypeSyntax(pos) -> Ok(#(Ctor0(NatT, pos), VSort(TypeSort, pos)))
    EqSyntax(a, b, pos) -> {
      use #(a2, t) <- result.try(infer(ctx, a))
      use b2 <- result.try(check(ctx, b, t))
      let t2 = header.quote(ctx.level, t)
      Ok(#(Ctor3(Eq, a2, b2, t2, pos), VSort(TypeSort, pos)))
    }
    JSyntax(e, p, pos) -> {
      use #(e2, _et) <- result.try(infer(ctx, e))
      case e2 {
        Ctor3(Eq, a, b, t, _) -> {
          let a2 = eval(a, ctx.env)
          let b2 = eval(b, ctx.env)
          let t2 = eval(t, ctx.env)
          use p2 <- result.try(check(
            ctx,
            p,
            VPi(
              "y",
              TypeMode,
              t2,
              fn(y) {
                VPi(
                  "p",
                  TypeMode,
                  VEq(a2, y, t2, pos),
                  fn(_) { VSort(TypeSort, pos) },
                  pos,
                )
              },
              pos,
            ),
          ))
          let p3 = eval(p2, ctx.env)
          let e3 = eval(e2, ctx.env)
          Ok(#(
            Ctor2(J, e2, p2, pos),
            VPi(
              "_",
              ManyMode,
              app(TypeMode, app(TypeMode, p3, a2), VRefl(a2, pos)),
              fn(_) { app(TypeMode, app(TypeMode, p3, b2), e3) },
              pos,
            ),
          ))
        }
        _ -> Error("J requires an equality type")
      }
    }
    _ -> todo as { header.pretty_syntax(s) }
  }
}
