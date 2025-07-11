import gleam/result
import header.{
  type BinderMode, type Level, type Sort, type Syntax, type Term, type Virtual,
  App, AppSyntax, Binder, Ctor0, Ctor2, DefSyntax, Ident, IdentSyntax, Index,
  KindSort, Lambda, LambdaSyntax, Let, LetSyntax, Level, ManyMode, Nat,
  NatSyntax, NatT, NatTypeSyntax, Pi, PiSyntax, Sort, SortSyntax, TypeMode,
  TypeSort, VApp, VIdent, VLambda, VNat, VNatType, VNeutral, VPi, VSort,
  ZeroMode, inc, pretty_term, pretty_virtual,
}

fn app(foo: Virtual, bar: Virtual) -> Virtual {
  case foo {
    VNeutral(neutral) -> VNeutral(VApp(neutral, bar))
    VLambda(_, _, f) -> f(bar)
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

pub fn eval(t: Term, env: List(Virtual)) -> Virtual {
  case t {
    Ident(_mode, idx, _s, _pos) ->
      case lookup(env, idx.int) {
        Ok(v) -> v
        Error(_) -> panic as "out-of-scope var during eval"
      }
    Ctor0(Sort(TypeSort), _) -> VSort(TypeSort)
    Ctor0(Sort(KindSort), _) -> VSort(KindSort)
    Binder(Pi(mode, t), x, u, _) ->
      VPi(x, mode, eval(t, env), fn(arg) { eval(u, [arg, ..env]) })
    Binder(Lambda(mode), x, e, _) ->
      VLambda(x, mode, fn(arg) { eval(e, [arg, ..env]) })
    Ctor2(App(_mode), foo, bar, _) -> app(eval(foo, env), eval(bar, env))
    Binder(Let(_mode, v), _x, e, _) -> eval(e, [eval(v, env), ..env])
    Ctor0(Nat(n), _) -> VNat(n)
    Ctor0(NatT, _) -> VNatType
    _ -> todo
  }
}

pub type Context {
  Context(
    level: Level,
    types: List(Virtual),
    env: List(Virtual),
    scope: List(#(String, #(BinderMode, Virtual))),
  )
}

pub const empty_ctx = Context(Level(0), [], [], [])

pub fn eq(lvl: Level, a: Virtual, b: Virtual) -> Bool {
  case a, b {
    VSort(s1), VSort(s2) -> s1 == s2
    VPi(x, m1, t1, u1), VPi(_, m2, t2, u2) -> {
      let dummy = VNeutral(VIdent(x, m1, lvl))
      m1 == m2 && eq(lvl, t1, t2) && eq(inc(lvl), u1(dummy), u2(dummy))
    }
    VLambda(x, m, f), b -> {
      let dummy = VNeutral(VIdent(x, m, lvl))
      eq(inc(lvl), f(dummy), app(b, dummy))
    }
    a, VLambda(x, m, f) -> {
      let dummy = VNeutral(VIdent(x, m, lvl))
      eq(inc(lvl), app(a, dummy), f(dummy))
    }
    VNeutral(VIdent(_, _, i)), VNeutral(VIdent(_, _, j)) -> i == j
    VNeutral(VApp(n1, arg1)), VNeutral(VApp(n2, arg2)) ->
      eq(lvl, VNeutral(n1), VNeutral(n2)) && eq(lvl, arg1, arg2)
    VNat(n), VNat(m) -> n == m
    VNatType, VNatType -> True
    _, _ -> False
  }
}

pub fn check(ctx: Context, s: Syntax, ty: Virtual) -> Result(Term, String) {
  case s, ty {
    LambdaSyntax(mode1, x, Ok(xt), body, pos), VPi(_, mode2, a, b) -> {
      use _ <- result.try(case mode1 == mode2 {
        True -> Ok(Nil)
        False ->
          Error(
            "mode mismatch: "
            <> header.pretty_mode(mode1)
            <> " and "
            <> header.pretty_mode(mode2),
          )
      })
      use #(xt2, _xtt) <- result.try(infer(ctx, xt))
      let xt3 = eval(xt2, ctx.env)
      use _ <- result.try(case eq(ctx.level, xt3, a) {
        True -> Ok(Nil)
        False ->
          Error(
            "type mismatch: "
            <> pretty_term(xt2)
            <> " and "
            <> pretty_virtual(a),
          )
      })
      let v = VNeutral(VIdent(x, mode1, ctx.level))
      let ctx2 =
        Context(
          level: inc(ctx.level),
          types: [a, ..ctx.types],
          env: [v, ..ctx.env],
          scope: [#(x, #(mode1, a)), ..ctx.scope],
        )
      use body2 <- result.try(check(ctx2, body, b(v)))
      Ok(Binder(Lambda(mode1), x, body2, pos))
    }
    LambdaSyntax(mode1, x, Error(Nil), body, pos), VPi(_, mode2, a, b) -> {
      use _ <- result.try(case mode1 == mode2 {
        True -> Ok(Nil)
        False ->
          Error(
            "mode mismatch: "
            <> header.pretty_mode(mode1)
            <> " and "
            <> header.pretty_mode(mode2),
          )
      })
      let dummy = VNeutral(VIdent(x, mode1, ctx.level))
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
        VSort(_) -> Ok(Nil)
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
    s, ty -> {
      use #(v, ty2) <- result.try(infer(ctx, s))
      case eq(ctx.level, ty, ty2) {
        True -> Ok(v)
        False -> {
          Error(
            "type mismatch between `"
            <> pretty_virtual(ty)
            <> "` and `"
            <> pretty_virtual(ty2)
            <> "` at "
            <> header.pretty_pos(header.get_pos(s)),
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

pub fn infer(ctx: Context, s: Syntax) -> Result(#(Term, Virtual), String) {
  case s {
    IdentSyntax(str, pos) -> {
      case scan(0, ctx.scope, str) {
        Ok(#(#(mode, ty), i)) -> Ok(#(Ident(mode, Index(i), str, pos), ty))
        Error(Nil) -> Error("undefined variable " <> str)
      }
    }
    SortSyntax(TypeSort, pos) ->
      Ok(#(Ctor0(Sort(TypeSort), pos), VSort(KindSort)))
    SortSyntax(KindSort, _) -> panic as "parsed impossible kind literal"
    PiSyntax(mode, str, a, b, pos) -> {
      use #(a2, at) <- result.try(infer(ctx, a))
      case at {
        VSort(s1) -> {
          use _ <- result.try(case s1, mode {
            KindSort, ManyMode ->
              Error(
                "relevant lambdas can't bind types ("
                <> header.pretty_pos(pos)
                <> ")",
              )
            _, _ -> Ok(Nil)
          })
          let dummy = VNeutral(VIdent(str, mode, ctx.level))
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
            VSort(KindSort), TypeMode ->
              Ok(#(Binder(Pi(mode, a2), str, b2, pos), VSort(KindSort)))
            VSort(KindSort), ManyMode ->
              Error(
                "relevant functions can't return types ("
                <> header.pretty_pos(pos)
                <> ")",
              )
            VSort(KindSort), ZeroMode ->
              Error(
                "erased functions can't return types ("
                <> header.pretty_pos(pos)
                <> ")",
              )
            VSort(TypeSort), TypeMode ->
              Error(
                "type abstractions must return types ("
                <> header.pretty_pos(pos)
                <> ")",
              )
            VSort(TypeSort), _ ->
              Ok(#(Binder(Pi(mode, a2), str, b2, pos), VSort(TypeSort)))
            _, _ ->
              Error(
                "pi right-side be a type (" <> header.pretty_pos(pos) <> ")",
              )
          }
        }
        _ ->
          Error(
            "pi left-side should be a type (" <> header.pretty_pos(pos) <> ")",
          )
      }
    }
    LambdaSyntax(mode, str, Ok(xt), body, pos) -> {
      use #(xt2, xtt) <- result.try(infer(ctx, xt))
      use _ <- result.try(case mode, xtt {
        ManyMode, VSort(KindSort) ->
          Error("relevant lambda binding can't bind types")
        _, VSort(TypeSort) -> Ok(Nil)
        _, _ -> Error("type annotation in lambda must be a type")
      })
      let xt2v = eval(xt2, ctx.env)
      let v = VNeutral(VIdent(str, mode, ctx.level))
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
        VPi(str, mode, xt2v, fn(x) {
          let ctx2 =
            Context(
              inc(ctx.level),
              types: [xt2v, ..ctx.env],
              env: [x, ..ctx.env],
              scope: [#(str, #(mode, xt2v)), ..ctx.scope],
            )
          let assert Ok(#(_, t)) = infer(ctx2, body)
          t
        }),
      ))
    }
    LambdaSyntax(_, _, Error(Nil), _, pos) ->
      Error("can't infer the type of the lambda at " <> header.pretty_pos(pos))
    AppSyntax(mode1, foo, bar, pos) -> {
      use #(foo2, foot) <- result.try(infer(ctx, foo))
      case foot {
        VPi(_, mode2, a, b) if mode1 == mode2 -> {
          use bar2 <- result.try(check(ctx, bar, a))
          let t = b(eval(bar2, ctx.env))
          Ok(#(Ctor2(App(mode1), foo2, bar2, pos), t))
        }
        VPi(_, mode2, _, _) ->
          Error(
            "mode-mismatch between "
            <> header.pretty_mode(mode1)
            <> " and "
            <> header.pretty_mode(mode2)
            <> " at "
            <> header.pretty_pos(pos),
          )
        _ ->
          Error(
            "application to non-function `"
            <> pretty_virtual(foot)
            <> "` at "
            <> header.pretty_pos(pos),
          )
      }
    }
    LetSyntax(x, xt, v, e, pos) -> {
      use #(xt2, xtt) <- result.try(infer(ctx, xt))
      use _ <- result.try(case xtt {
        VSort(_) -> Ok(Nil)
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
        VSort(_) -> Ok(Nil)
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
    NatSyntax(n, pos) -> Ok(#(Ctor0(Nat(n), pos), VNatType))
    NatTypeSyntax(pos) -> Ok(#(Ctor0(NatT, pos), VSort(TypeSort)))
    _ -> todo as { header.pretty_syntax(s) }
  }
}
