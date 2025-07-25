import gleam/dict
import gleam/int
import gleam/list
import gleam/result
import header.{
  type BinderMode, type ContextMask, type Index, type Level, type Meta,
  type Neutral, type Pos, type Ref, type Syntax, type Term, type Value, App,
  AppSyntax, Binder, Cast, CastSyntax, ContextMask, Ctor0, Ctor1, Ctor2, Ctor3,
  DefSyntax, Eq, EqSyntax, ExFalso, ExFalsoSyntax, Fst, FstSyntax, HoleSyntax,
  Ident, IdentSyntax, Index, InsertedMeta, Inter, InterT, IntersectionSyntax,
  IntersectionTypeSyntax, KindSort, Lambda, LambdaSyntax, Let, LetSyntax, Level,
  ManyMode, Meta, Nat, NatSyntax, NatT, NatTypeSyntax, Pi, PiSyntax, Psi,
  PsiSyntax, Refl, ReflSyntax, SetSort, Snd, SndSyntax, Solved, Sort, SortSyntax,
  TypeMode, Unsolved, VApp, VCast, VEq, VExFalso, VFst, VIdent, VInter, VInterT,
  VLambda, VMeta, VNat, VNatType, VNeutral, VPi, VPsi, VRefl, VSnd, VSort,
  ZeroMode, force, get, inc, lvl_to_idx, new, next_id, pretty_mode, pretty_pos,
  pretty_term, pretty_value, set,
}

fn erase(t: Value) -> Value {
  case force(t) {
    VNeutral(n) -> VNeutral(erase_neutral(n))
    VLambda(_, ZeroMode, e, p) ->
      erase(e(VNeutral(VIdent("", ZeroMode, Level(0), p))))
    VLambda(x, mode, e, p) -> VLambda(x, mode, fn(arg) { erase(e(arg)) }, p)
    VPi(x, mode, a, b, p) ->
      VPi(x, mode, erase(a), fn(arg) { erase(b(arg)) }, p)
    VEq(a, b, t, p) -> VEq(erase(a), erase(b), erase(t), p)
    VRefl(_, p) -> VLambda("x", ManyMode, fn(x) { x }, p)
    VInter(a, _, _) -> erase(a)
    VInterT(x, a, b, p) -> VInterT(x, erase(a), fn(arg) { erase(b(arg)) }, p)
    VCast(a, _, _, _) -> erase(a)
    VExFalso(a, _) -> erase(a)
    VNat(_, _) | VNatType(_) | VSort(_, _) -> t
  }
}

fn erase_neutral(n: Neutral) -> Neutral {
  case n {
    VIdent(_, _, _, _) -> n
    VMeta(_, _) -> n
    VApp(ZeroMode, a, _, _) -> erase_neutral(a)
    VApp(m, a, b, p) -> VApp(m, erase_neutral(a), erase(b), p)
    VPsi(e, _, _) -> erase_neutral(e)
    VFst(a, _) -> erase_neutral(a)
    VSnd(a, _) -> erase_neutral(a)
  }
}

pub fn pretty_erasure(v: Value) -> String {
  case force(v) {
    VNeutral(VIdent(x, _, _, _)) -> x
    VNeutral(VMeta(_, _)) -> "_"
    VNeutral(VApp(_, a, b, _)) ->
      "(" <> pretty_erasure(VNeutral(a)) <> ")(" <> pretty_erasure(b) <> ")"
    VNeutral(VPsi(_, _, _)) -> panic
    VNeutral(VFst(_, _)) -> panic
    VNeutral(VSnd(_, _)) -> panic
    VLambda(x, _, body, pos) ->
      x
      <> "-> "
      <> pretty_erasure(body(VNeutral(VIdent(x, ManyMode, Level(0), pos))))
    VPi(_, _, _, _, _) -> panic
    VEq(_, _, _, _) -> panic
    VRefl(_, _) -> panic
    VInter(_, _, _) -> panic
    VInterT(_, _, _, _) -> panic
    VCast(_, _, _, _) -> panic
    VExFalso(_, _) -> panic
    VNat(n, _) -> int.to_string(n)
    VNatType(_) -> panic
    VSort(_, _) -> panic
  }
}

fn app(mode: BinderMode, foo: Value, bar: Value) -> Value {
  case force(foo) {
    VNeutral(neutral) ->
      VNeutral(VApp(mode, neutral, bar, header.value_pos(bar)))
    VLambda(_, _, f, _) -> f(bar)
    _ -> panic as "impossible value application"
  }
}

fn apps(foo: Value, env: List(Value), mask: List(ContextMask)) -> Value {
  echo #(list.length(env), list.length(mask))
  case env, mask {
    [], [] -> foo
    [_, ..env2], [ContextMask(has_def: True, mode: _), ..mask2] ->
      apps(foo, env2, mask2)
    [v, ..env2], [ContextMask(has_def: False, mode:), ..mask2] ->
      app(mode, apps(foo, env2, mask2), v)
    _, _ -> panic
  }
}

fn psi(pos: Pos, eq: Value, pred: Value) -> Value {
  case force(eq) {
    VNeutral(neutral) -> VNeutral(VPsi(neutral, pred, pos))
    VRefl(_, _) -> VLambda("x", ManyMode, fn(x) { x }, pos)
    _ -> panic as { "impossible equality elimination " <> pretty_value(eq) }
  }
}

fn fst(pos: Pos, inter: Value) -> Value {
  case force(inter) {
    VNeutral(neutral) -> VNeutral(VFst(neutral, pos))
    VInter(a, _, _) -> a
    VCast(a, _, _, _) -> {
      // slightly creative but seems right
      a
    }
    _ -> panic as { "impossible value projection " <> pretty_value(inter) }
  }
}

fn snd(pos: Pos, inter: Value) -> Value {
  case force(inter) {
    VNeutral(neutral) -> VNeutral(VSnd(neutral, pos))
    VInter(_, b, _) -> b
    VCast(a, _, _, _) -> {
      // slightly creative but seems right
      a
    }
    _ -> panic as "impossible value projection"
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
    Ctor0(Meta(ref), pos) -> VNeutral(VMeta(ref, pos))
    Ctor0(InsertedMeta(ref, mask), pos) ->
      apps(VNeutral(VMeta(ref, pos)), env, mask)
    Ctor0(Sort(SetSort), pos) -> VSort(SetSort, pos)
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
    Ctor2(Psi, e, p, pos) -> psi(pos, eval(e, env), eval(p, env))
    Ctor2(Inter, a, b, pos) -> VInter(eval(a, env), eval(b, env), pos)
    Binder(InterT(a), x, b, pos) ->
      VInterT(x, eval(a, env), fn(arg) { eval(b, [arg, ..env]) }, pos)
    Ctor1(Fst, a, pos) -> fst(pos, eval(a, env))
    Ctor1(Snd, a, pos) -> snd(pos, eval(a, env))
    Ctor3(Cast, a, inter, eq, pos) ->
      VCast(eval(a, env), eval(inter, env), eval(eq, env), pos)
    Ctor1(ExFalso, a, pos) -> VExFalso(eval(a, env), pos)
  }
}

pub type Context {
  Context(
    level: Level,
    types: List(Value),
    env: List(Value),
    scope: List(#(String, #(BinderMode, Value))),
    mask: List(ContextMask),
  )
}

pub const empty_ctx = Context(Level(0), [], [], [], [])

fn fresh_meta(ctx: Context, pos: Pos) -> Term {
  let ref = new(Unsolved(next_id()))
  Ctor0(InsertedMeta(ref, ctx.mask), pos)
}

type PartialRenaming {
  PartialRenaming(
    domain_size: Level,
    codomain_size: Level,
    renaming: dict.Dict(Level, Level),
  )
}

fn lift(pr: PartialRenaming) -> PartialRenaming {
  PartialRenaming(
    domain_size: inc(pr.domain_size),
    codomain_size: inc(pr.codomain_size),
    renaming: dict.insert(pr.renaming, pr.codomain_size, pr.domain_size),
  )
}

fn invert(
  gamma codomain_size: Level,
  spine n: Neutral,
) -> Result(PartialRenaming, String) {
  use #(domain_size, renaming) <- result.try(invert_helper(n))
  Ok(PartialRenaming(domain_size:, codomain_size:, renaming:))
}

fn invert_helper(
  n: Neutral,
) -> Result(#(Level, dict.Dict(Level, Level)), String) {
  case n {
    VMeta(_, _) -> Ok(#(Level(0), dict.new()))
    VApp(_mode, foo, bar, pos) -> {
      use #(domain, renaming) <- result.try(invert_helper(foo))
      case force(bar) {
        VNeutral(VIdent(_, _, lvl, _)) ->
          case dict.get(renaming, lvl) {
            Ok(_) -> Error("unify error " <> pretty_pos(pos))
            Error(Nil) -> Ok(#(inc(domain), dict.insert(renaming, lvl, domain)))
          }
        _ -> panic
      }
    }
    _ -> panic
  }
}

fn rename(
  meta: Ref(Meta),
  pr: PartialRenaming,
  v: Value,
) -> Result(Term, String) {
  case force(v) {
    VNeutral(VMeta(ref, pos)) ->
      case get(ref), get(meta) {
        Unsolved(i), Unsolved(j) if i == j ->
          Error("unify error: occurs check failure at " <> pretty_pos(pos))
        Unsolved(_), Unsolved(_) -> Ok(Ctor0(Meta(ref), pos))
        _, _ -> panic
      }
    VNeutral(VIdent(x, mode, lvl, pos)) ->
      case dict.get(pr.renaming, lvl) {
        Ok(lvl2) -> Ok(Ident(mode, lvl_to_idx(pr.domain_size, lvl2), x, pos))
        Error(Nil) ->
          Error("unify error: variable escaping scope at " <> pretty_pos(pos))
      }
    VNeutral(VApp(mode, n, a, pos)) -> {
      use n2 <- result.try(rename(meta, pr, VNeutral(n)))
      use a2 <- result.try(rename(meta, pr, a))
      Ok(Ctor2(App(mode), n2, a2, pos))
    }
    VNeutral(VPsi(a, b, pos)) -> {
      use a2 <- result.try(rename(meta, pr, VNeutral(a)))
      use b2 <- result.try(rename(meta, pr, b))
      Ok(Ctor2(Psi, a2, b2, pos))
    }
    VNeutral(VFst(a, pos)) -> {
      use a2 <- result.try(rename(meta, pr, VNeutral(a)))
      Ok(Ctor1(Fst, a2, pos))
    }
    VNeutral(VSnd(a, pos)) -> {
      use a2 <- result.try(rename(meta, pr, VNeutral(a)))
      Ok(Ctor1(Snd, a2, pos))
    }
    VSort(s, pos) -> Ok(Ctor0(Sort(s), pos))
    VNat(n, pos) -> Ok(Ctor0(Nat(n), pos))
    VNatType(pos) -> Ok(Ctor0(NatT, pos))
    VPi(x, mode, a, b, pos) -> {
      use a2 <- result.try(rename(meta, pr, a))
      use b2 <- result.try(rename(
        meta,
        lift(pr),
        b(VNeutral(VIdent(x, mode, pr.codomain_size, pos))),
      ))
      Ok(Binder(Pi(mode, a2), x, b2, pos))
    }
    VLambda(x, mode, e, pos) -> {
      use e2 <- result.try(rename(
        meta,
        lift(pr),
        e(VNeutral(VIdent(x, mode, pr.codomain_size, pos))),
      ))
      Ok(Binder(Lambda(mode), x, e2, pos))
    }
    VEq(a, b, t, pos) -> {
      use a2 <- result.try(rename(meta, pr, a))
      use b2 <- result.try(rename(meta, pr, b))
      use t2 <- result.try(rename(meta, pr, t))
      Ok(Ctor3(Eq, a2, b2, t2, pos))
    }
    VRefl(a, pos) -> {
      use a2 <- result.try(rename(meta, pr, a))
      Ok(Ctor1(Refl, a2, pos))
    }
    VInter(a, b, pos) -> {
      use a2 <- result.try(rename(meta, pr, a))
      use b2 <- result.try(rename(meta, pr, b))
      Ok(Ctor2(Inter, a2, b2, pos))
    }
    VInterT(x, a, b, pos) -> {
      use a2 <- result.try(rename(meta, pr, a))
      use b2 <- result.try(rename(
        meta,
        lift(pr),
        b(VNeutral(VIdent(x, TypeMode, pr.codomain_size, pos))),
      ))
      Ok(Binder(InterT(a2), x, b2, pos))
    }
    VCast(a, b, c, pos) -> {
      use a2 <- result.try(rename(meta, pr, a))
      use b2 <- result.try(rename(meta, pr, b))
      use c2 <- result.try(rename(meta, pr, c))
      Ok(Ctor3(Cast, a2, b2, c2, pos))
    }
    VExFalso(a, pos) -> {
      use a2 <- result.try(rename(meta, pr, a))
      Ok(Ctor1(ExFalso, a2, pos))
    }
  }
}

fn lambdas(lvl: Level, body: Term) -> Term {
  lambdas_helper(lvl, body, Level(0))
}

fn lambdas_helper(lvl: Level, body: Term, x: Level) -> Term {
  case x == lvl {
    True -> body
    False ->
      Binder(
        Lambda(ManyMode),
        "x" <> int.to_string(x.int + 1),
        lambdas_helper(lvl, body, inc(x)),
        header.term_pos(body),
      )
  }
}

fn solve(
  gamma: Level,
  ref: Ref(Meta),
  lhs: Neutral,
  rhs: Value,
) -> Result(Bool, String) {
  use pr <- result.try(invert(gamma, lhs))
  use rhs2 <- result.try(rename(ref, pr, rhs))
  let solution = eval(lambdas(pr.domain_size, rhs2), [])
  set(ref, Solved(solution))
  Ok(True)
}

fn unify(lvl: Level, a: Value, b: Value) -> Result(Bool, String) {
  unify_helper(lvl, erase(a), erase(b))
}

fn and(a: Result(Bool, String), b: Result(Bool, String)) -> Result(Bool, String) {
  case a, b {
    Error(err), _ | _, Error(err) -> Error(err)
    Ok(False), _ | _, Ok(False) -> Ok(False)
    Ok(True), Ok(True) -> Ok(True)
  }
}

fn unify_helper(lvl: Level, a: Value, b: Value) -> Result(Bool, String) {
  let uh = fn(a, b) { unify_helper(lvl, a, b) }
  case force(a), force(b) {
    VNeutral(VMeta(m1, _) as meta1), VNeutral(VMeta(m2, _)) as meta2 ->
      case get(m1), get(m2) {
        Unsolved(i), Unsolved(j) if i == j -> Ok(True)
        Unsolved(_), Unsolved(_) -> solve(lvl, m1, meta1, meta2)
        _, _ -> panic
      }
    VNeutral(VMeta(m, _) as n), t | t, VNeutral(VMeta(m, _) as n) ->
      solve(lvl, m, n, t)
    VSort(s1, _), VSort(s2, _) -> Ok(s1 == s2)
    VPi(x, m1, t1, u1, pos), VPi(_, m2, t2, u2, _) -> {
      let dummy = VNeutral(VIdent(x, m1, lvl, pos))
      Ok(m1 == m2)
      |> and(uh(t1, t2))
      |> and(unify_helper(inc(lvl), u1(dummy), u2(dummy)))
    }
    VLambda(x, m, f, pos), b -> {
      let dummy = VNeutral(VIdent(x, m, lvl, pos))
      unify_helper(inc(lvl), f(dummy), app(m, b, dummy))
    }
    a, VLambda(x, m, f, pos) -> {
      let dummy = VNeutral(VIdent(x, m, lvl, pos))
      unify_helper(inc(lvl), app(m, a, dummy), f(dummy))
    }
    VNeutral(VIdent(_, _, i, _)), VNeutral(VIdent(_, _, j, _)) -> Ok(i == j)
    VNeutral(VApp(m1, n1, arg1, _)), VNeutral(VApp(m2, n2, arg2, _)) ->
      Ok(m1 == m2) |> and(uh(VNeutral(n1), VNeutral(n2))) |> and(uh(arg1, arg2))
    VNat(n, _), VNat(m, _) -> Ok(n == m)
    VNatType(_), VNatType(_) -> Ok(True)
    VEq(a1, b1, t1, _), VEq(a2, b2, t2, _) ->
      uh(a1, a2) |> and(uh(b1, b2)) |> and(uh(t1, t2))
    VRefl(a1, _), VRefl(a2, _) -> uh(a1, a2)
    VNeutral(VPsi(e1, p1, _)), VNeutral(VPsi(e2, p2, _)) ->
      uh(VNeutral(e1), VNeutral(e2)) |> and(uh(p1, p2))
    VInter(a1, b1, _), VInter(a2, b2, _) -> uh(a1, a2) |> and(uh(b1, b2))
    VInterT(x, a1, b1, pos), VInterT(_, a2, b2, _) -> {
      let dummy = VNeutral(VIdent(x, TypeMode, lvl, pos))
      uh(a1, a2) |> and(unify_helper(inc(lvl), b1(dummy), b2(dummy)))
    }
    VNeutral(VFst(a1, _)), VNeutral(VFst(a2, _)) ->
      uh(VNeutral(a1), VNeutral(a2))
    VNeutral(VSnd(a1, _)), VNeutral(VSnd(a2, _)) ->
      uh(VNeutral(a1), VNeutral(a2))
    VCast(a1, inter1, eq1, _), VCast(a2, inter2, eq2, _) ->
      uh(a1, a2) |> and(uh(inter1, inter2)) |> and(uh(eq1, eq2))
    VExFalso(a1, _), VExFalso(a2, _) -> uh(a1, a2)
    _, _ -> Ok(False)
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
    Ctor1(Refl, _, _) -> Error(Nil)
    Ctor1(_, a, _) -> rel_occurs(a, x)
    Ctor2(App(ZeroMode), a, _, _) -> rel_occurs(a, x)
    Ctor2(Psi, a, _, _) -> rel_occurs(a, x)
    Ctor2(_, a, b, _) -> result.or(rel_occurs(a, x), rel_occurs(b, x))
    Ctor3(Cast, a, _, _, _) -> rel_occurs(a, x)
    Ctor3(_, a, b, c, _) ->
      rel_occurs(a, x)
      |> result.or(rel_occurs(b, x))
      |> result.or(rel_occurs(c, x))
  }
}

fn check(ctx: Context, s: Syntax, ty: Value) -> Result(Term, String) {
  case s, force(ty) {
    LambdaSyntax(mode1, x, Ok(xt), body, pos), VPi(_, mode2, a, b, _) -> {
      use mode <- result.try(case mode1, mode2 {
        m1, m2 if m1 == m2 -> Ok(m1)
        ManyMode, TypeMode -> Ok(TypeMode)
        _, _ ->
          Error(
            "mode mismatch: "
            <> pretty_mode(mode1)
            <> " and "
            <> pretty_mode(mode2)
            <> " at "
            <> pretty_pos(pos),
          )
      })
      use #(xt2, _xtt) <- result.try(infer(ctx, xt))
      let xt3 = eval(xt2, ctx.env)
      use _ <- result.try(case unify(ctx.level, xt3, a) {
        Ok(True) -> Ok(Nil)
        Ok(False) ->
          Error(
            "type mismatch: " <> pretty_term(xt2) <> " and " <> pretty_value(a),
          )
        Error(err) -> Error(err)
      })
      let v = VNeutral(VIdent(x, mode, ctx.level, pos))
      let ctx2 =
        Context(
          level: inc(ctx.level),
          types: [a, ..ctx.types],
          env: [v, ..ctx.env],
          scope: [#(x, #(mode, a)), ..ctx.scope],
          mask: [ContextMask(has_def: False, mode:), ..ctx.mask],
        )
      use body2 <- result.try(check(ctx2, body, b(v)))
      use _ <- result.try(case mode {
        ZeroMode ->
          case rel_occurs(body2, Index(0)) {
            Ok(pos2) ->
              Error("relevant usage of erased variable at " <> pretty_pos(pos2))
            Error(Nil) -> Ok(Nil)
          }
        _ -> Ok(Nil)
      })
      Ok(Binder(Lambda(mode), x, body2, pos))
    }
    LambdaSyntax(mode1, x, Error(Nil), body, pos), VPi(_, mode2, a, b, _) -> {
      use mode <- result.try(case mode1, mode2 {
        m1, m2 if m1 == m2 -> Ok(m1)
        ManyMode, TypeMode -> Ok(TypeMode)
        _, _ ->
          Error(
            "mode mismatch: "
            <> pretty_mode(mode1)
            <> " and "
            <> pretty_mode(mode2)
            <> " at "
            <> pretty_pos(pos),
          )
      })
      let dummy = VNeutral(VIdent(x, mode, ctx.level, pos))
      let ctx2 =
        Context(
          level: inc(ctx.level),
          types: [a, ..ctx.types],
          env: [dummy, ..ctx.env],
          scope: [#(x, #(mode, a)), ..ctx.scope],
          mask: [ContextMask(has_def: False, mode:), ..ctx.mask],
        )
      use body2 <- result.try(check(ctx2, body, b(dummy)))
      Ok(Binder(Lambda(mode), x, body2, pos))
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
        Context(
          level: inc(ctx.level),
          types: [xt2v, ..ctx.types],
          env: [v3, ..ctx.env],
          scope: [#(x, #(ManyMode, xt2v)), ..ctx.scope],
          mask: [ContextMask(has_def: True, mode: ManyMode), ..ctx.mask],
        )
      use e2 <- result.try(check(ctx2, e, ty))
      Ok(Binder(Let(mode: ManyMode, val: v2), x, e2, pos))
    }
    DefSyntax(x, xt, v, e, pos), ty -> {
      use #(xt2, xtt) <- result.try(infer(ctx, xt))
      use _ <- result.try(case xtt {
        VSort(_, _) -> Ok(Nil)
        _ -> Error("type annotation must be a type")
      })
      let xt2v = eval(xt2, ctx.env)
      use v2 <- result.try(check(ctx, v, xt2v))
      let v3 = eval(v2, ctx.env)
      let ctx2 =
        Context(
          level: inc(ctx.level),
          types: [xt2v, ..ctx.types],
          env: [v3, ..ctx.env],
          scope: [#(x, #(ZeroMode, xt2v)), ..ctx.scope],
          mask: [ContextMask(has_def: True, mode: ZeroMode), ..ctx.mask],
        )
      use e2 <- result.try(check(ctx2, e, ty))
      Ok(Binder(Let(mode: ZeroMode, val: v2), x, e2, pos))
    }
    ReflSyntax(x, pos), VEq(a, b, _t, _) -> {
      use #(x2, _xt) <- result.try(infer(ctx, x))
      let x3 = eval(x2, ctx.env)
      use _ <- result.try(case unify(ctx.level, x3, a) {
        Ok(True) ->
          case unify(ctx.level, x3, b) {
            Ok(True) -> Ok(Nil)
            Ok(False) ->
              Error(
                "type mismatch between "
                <> pretty_value(x3)
                <> " and "
                <> pretty_value(b)
                <> " at "
                <> pretty_pos(pos),
              )
            Error(err) -> Error(err)
          }
        Ok(False) ->
          Error(
            "type mismatch between "
            <> pretty_value(x3)
            <> " and "
            <> pretty_value(a)
            <> " at "
            <> pretty_pos(pos),
          )
        Error(err) -> Error(err)
      })
      Ok(Ctor1(Refl, x2, pos))
    }
    IntersectionSyntax(a, b, pos), VInterT(_, at, bt, _) -> {
      use a2 <- result.try(check(ctx, a, at))
      let a3 = eval(a2, ctx.env)
      use b2 <- result.try(check(ctx, b, bt(a3)))
      let b3 = eval(b2, ctx.env)
      use _ <- result.try(case unify(ctx.level, a3, b3) {
        Ok(True) -> Ok(Nil)
        Ok(False) ->
          Error(
            "intersection components must be equal (" <> pretty_pos(pos) <> ")",
          )
        Error(err) -> Error(err)
      })
      Ok(Ctor2(Inter, a2, b2, pos))
    }
    CastSyntax(a, inter, eq, pos), VInterT(_, at, _, _) as intert -> {
      use a2 <- result.try(check(ctx, a, at))
      let a3 = eval(a2, ctx.env)
      use inter2 <- result.try(check(ctx, inter, intert))
      let inter3 = eval(inter2, ctx.env)
      use eq2 <- result.try(check(ctx, eq, VEq(a3, fst(pos, inter3), at, pos)))
      Ok(Ctor3(Cast, a2, inter2, eq2, pos))
    }
    s, ty -> {
      use #(v, ty2) <- result.try(infer(ctx, s))
      case unify(ctx.level, ty, ty2) {
        Ok(True) -> Ok(v)
        Ok(False) -> {
          Error(
            "type mismatch between `"
            <> pretty_value(ty)
            <> "` and `"
            <> pretty_value(ty2)
            <> "` at "
            <> pretty_pos(header.get_pos(s)),
          )
        }
        Error(err) -> Error(err)
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
    SortSyntax(SetSort, pos) ->
      Ok(#(Ctor0(Sort(SetSort), pos), VSort(KindSort, pos)))
    SortSyntax(KindSort, _) -> panic as "parsed impossible kind literal"
    PiSyntax(mode, str, a, b, pos) -> {
      use #(a2, at) <- result.try(infer(ctx, a))
      case at {
        VSort(s1, _) -> {
          let mode = case s1, mode {
            KindSort, ManyMode -> TypeMode
            _, _ -> mode
          }
          let dummy = VNeutral(VIdent(str, mode, ctx.level, pos))
          let a3 = eval(a2, ctx.env)
          let ctx2 =
            Context(
              level: inc(ctx.level),
              types: [a3, ..ctx.types],
              env: [dummy, ..ctx.env],
              scope: [#(str, #(mode, a3)), ..ctx.scope],
              mask: [ContextMask(has_def: False, mode:), ..ctx.mask],
            )
          use #(b2, bt) <- result.try(infer(ctx2, b))
          case bt, mode {
            VSort(KindSort, _) as s, TypeMode ->
              Ok(#(Binder(Pi(mode, a2), str, b2, pos), s))
            VSort(KindSort, _) as s, ManyMode ->
              Ok(#(Binder(Pi(TypeMode, a2), str, b2, pos), s))
            VSort(KindSort, _), ZeroMode ->
              Error(
                "erased functions can't return types ("
                <> pretty_pos(pos)
                <> ")",
              )
            VSort(SetSort, _), TypeMode ->
              Error(
                "type abstractions must return types ("
                <> pretty_pos(pos)
                <> ")",
              )
            VSort(SetSort, _) as s, _ ->
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
        _, VSort(SetSort, _) -> Ok(Nil)
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
          mask: [ContextMask(has_def: False, mode:), ..ctx.mask],
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
                mask: [ContextMask(has_def: False, mode:), ..ctx.mask],
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
        VPi(_, TypeMode, a, b, _) if mode1 == ManyMode -> {
          use bar2 <- result.try(check(ctx, bar, a))
          let t = b(eval(bar2, ctx.env))
          Ok(#(Ctor2(App(TypeMode), foo2, bar2, pos), t))
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
      // echo x <> " = " <> pretty_erasure(erase(eval(v2, ctx.env)))
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
    NatTypeSyntax(pos) -> Ok(#(Ctor0(NatT, pos), VSort(SetSort, pos)))
    EqSyntax(a, b, pos) -> {
      use #(a2, t) <- result.try(infer(ctx, a))
      use b2 <- result.try(check(ctx, b, t))
      let t2 = header.quote(ctx.level, t)
      Ok(#(Ctor3(Eq, a2, b2, t2, pos), VSort(SetSort, pos)))
    }
    ReflSyntax(a, pos) -> {
      use #(a2, t) <- result.try(infer(ctx, a))
      let a3 = eval(a2, ctx.env)
      Ok(#(Ctor1(Refl, a2, pos), VEq(a3, a3, t, pos)))
    }
    PsiSyntax(e, p, pos) -> {
      use #(e2, et) <- result.try(infer(ctx, e))
      case et {
        VEq(a, b, t, _) -> {
          use p2 <- result.try(check(
            ctx,
            p,
            VPi(
              "y",
              TypeMode,
              t,
              fn(y) {
                VPi(
                  "p",
                  TypeMode,
                  VEq(a, y, t, pos),
                  fn(_) { VSort(SetSort, pos) },
                  pos,
                )
              },
              pos,
            ),
          ))
          let p3 = eval(p2, ctx.env)
          let e3 = eval(e2, ctx.env)
          Ok(#(
            Ctor2(Psi, e2, p2, pos),
            VPi(
              "_",
              ManyMode,
              app(TypeMode, app(TypeMode, p3, a), VRefl(a, pos)),
              fn(_) { app(TypeMode, app(TypeMode, p3, b), e3) },
              pos,
            ),
          ))
        }
        _ ->
          Error(
            "Psi requires an equality type, but received "
            <> pretty_term(e2)
            <> " ("
            <> pretty_pos(pos)
            <> ")",
          )
      }
    }
    IntersectionTypeSyntax(x, a, b, pos) -> {
      use a2 <- result.try(check(ctx, a, VSort(SetSort, pos)))
      let dummy = VNeutral(VIdent(x, TypeMode, ctx.level, pos))
      let a3 = eval(a2, ctx.env)
      let ctx2 =
        Context(
          level: inc(ctx.level),
          types: [a3, ..ctx.types],
          env: [dummy, ..ctx.env],
          scope: [#(x, #(TypeMode, a3)), ..ctx.scope],
          mask: [ContextMask(has_def: False, mode: TypeMode), ..ctx.mask],
        )
      use b2 <- result.try(check(ctx2, b, VSort(SetSort, pos)))
      Ok(#(Binder(InterT(a2), x, b2, pos), VSort(SetSort, pos)))
    }
    IntersectionSyntax(a, b, pos) -> {
      use #(a2, at) <- result.try(infer(ctx, a))
      let a3 = eval(a2, ctx.env)
      use #(b2, bt) <- result.try(infer(ctx, b))
      let b3 = eval(b2, ctx.env)
      case unify(ctx.level, a3, b3) {
        Ok(True) ->
          Ok(#(Ctor2(Inter, a2, b2, pos), VInterT("_", at, fn(_) { bt }, pos)))
        Ok(False) ->
          Error(
            "Intersection components must be equal (" <> pretty_pos(pos) <> ")",
          )
        Error(err) -> Error(err)
      }
    }
    FstSyntax(a, pos) -> {
      use #(a2, at) <- result.try(infer(ctx, a))
      case at {
        VInterT(_, a, _, _) -> Ok(#(Ctor1(Fst, a2, pos), a))
        _ ->
          Error("Projection requires intersection (" <> pretty_pos(pos) <> ")")
      }
    }
    SndSyntax(a, pos) -> {
      use #(a2, at) <- result.try(infer(ctx, a))
      let a3 = eval(a2, ctx.env)
      case at {
        VInterT(_, _, b, _) -> Ok(#(Ctor1(Snd, a2, pos), b(fst(pos, a3))))
        _ ->
          Error("Projection requires intersection (" <> pretty_pos(pos) <> ")")
      }
    }
    CastSyntax(a, inter, eq, pos) -> {
      use #(inter2, intert) <- result.try(infer(ctx, inter))
      case intert {
        VInterT(_, at, _, _) -> {
          let inter3 = eval(inter2, ctx.env)
          use a2 <- result.try(check(ctx, a, at))
          let a3 = eval(a2, ctx.env)
          use eq2 <- result.try(check(
            ctx,
            eq,
            VEq(a3, fst(pos, inter3), at, pos),
          ))
          Ok(#(Ctor3(Cast, a2, inter2, eq2, pos), intert))
        }
        _ ->
          Error(
            "cast requires an intersection in the second argument ("
            <> pretty_pos(pos)
            <> ")",
          )
      }
    }
    ExFalsoSyntax(a, pos) -> {
      use a2 <- result.try(check(
        ctx,
        a,
        VEq(ctrue(pos), cfalse(pos), cbool(pos), pos),
      ))
      Ok(#(
        Ctor1(ExFalso, a2, pos),
        VPi("t", ZeroMode, VSort(SetSort, pos), fn(t) { t }, pos),
      ))
    }
    HoleSyntax(pos) -> {
      let x = fresh_meta(ctx, pos)
      let xt = eval(fresh_meta(ctx, pos), ctx.env)
      Ok(#(x, xt))
    }
  }
}

fn cbool(pos: Pos) -> Value {
  VPi(
    "t",
    ZeroMode,
    VSort(SetSort, pos),
    fn(t) {
      VPi(
        "x",
        ManyMode,
        t,
        fn(_x) { VPi("y", ManyMode, t, fn(_y) { t }, pos) },
        pos,
      )
    },
    pos,
  )
}

fn ctrue(pos: Pos) -> Value {
  VLambda(
    "t",
    ZeroMode,
    fn(_t) {
      VLambda(
        "x",
        ManyMode,
        fn(x) { VLambda("y", ManyMode, fn(_y) { x }, pos) },
        pos,
      )
    },
    pos,
  )
}

fn cfalse(pos: Pos) -> Value {
  VLambda(
    "t",
    ZeroMode,
    fn(_t) {
      VLambda(
        "x",
        ManyMode,
        fn(_x) { VLambda("y", ManyMode, fn(y) { y }, pos) },
        pos,
      )
    },
    pos,
  )
}
