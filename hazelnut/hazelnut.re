open Sexplib.Std;
open Monad_lib.Monad; // Uncomment this line to use the maybe monad

let compare_string = String.compare;
let compare_int = Int.compare;

module Htyp = {
  [@deriving (sexp, compare)]
  type t =
    | Arrow(t, t)
    | Num
    | Hole;
};

module Hexp = {
  [@deriving (sexp, compare)]
  type t =
    | Var(string)
    | Lam(string, t)
    | Ap(t, t)
    | Lit(int)
    | Plus(t, t)
    | Asc(t, Htyp.t)
    | EHole
    | NEHole(t);
};

module Ztyp = {
  [@deriving (sexp, compare)]
  type t =
    | Cursor(Htyp.t)
    | LArrow(t, Htyp.t)
    | RArrow(Htyp.t, t);
};

module Zexp = {
  [@deriving (sexp, compare)]
  type t =
    | Cursor(Hexp.t)
    | Lam(string, t)
    | LAp(t, Hexp.t)
    | RAp(Hexp.t, t)
    | LPlus(t, Hexp.t)
    | RPlus(Hexp.t, t)
    | LAsc(t, Htyp.t)
    | RAsc(Hexp.t, Ztyp.t)
    | NEHole(t);
};

module Child = {
  [@deriving (sexp, compare)]
  type t =
    | One
    | Two;
};

module Dir = {
  [@deriving (sexp, compare)]
  type t =
    | Child(Child.t)
    | Parent;
};

module Shape = {
  [@deriving (sexp, compare)]
  type t =
    | Arrow
    | Num
    | Asc
    | Var(string)
    | Lam(string)
    | Ap
    | Lit(int)
    | Plus
    | NEHole;
};

module Action = {
  [@deriving (sexp, compare)]
  type t =
    | Move(Dir.t)
    | Construct(Shape.t)
    | Del
    | Finish;
};

module TypCtx = Map.Make(String);
type typctx = TypCtx.t(Htyp.t);

exception Unimplemented;

let rec erase_typ = (ty: Ztyp.t): Htyp.t => {
  switch (ty) {
  | Cursor(under_curs_typ) => under_curs_typ
  | LArrow(t_in, t_out) => Arrow(erase_typ(t_in), t_out)
  | RArrow(t_in, t_out) => Arrow(t_in, erase_typ(t_out))
  }
};

let rec erase_exp = (e: Zexp.t): Hexp.t => {
  switch (e) {
  | Cursor(under_curs_exp) => under_curs_exp
  | Lam(var, body_exp) => Lam(var, erase_exp(body_exp))
  | LAp(func, arg) => Ap(erase_exp(func), arg)
  | RAp(func, arg) => Ap(func, erase_exp(arg))
  | LPlus(lhs, rhs) => Plus(erase_exp(lhs), rhs)
  | RPlus(lhs, rhs) => Plus(lhs, erase_exp(rhs))
  | LAsc(typed_exp, typ) => Asc(erase_exp(typed_exp), typ)
  | RAsc(typed_exp, typ) => Asc(typed_exp, erase_typ(typ))
  | NEHole(subexp) => NEHole(erase_exp(subexp))
  }
};

let extract_arrow = (tau: Htyp.t): option((Htyp.t, Htyp.t)) => {
  switch (tau) {
  | Hole => Some((Hole, Hole)) // DOUBLE CHECK
  | Arrow(t_in, t_out) => Some((t_in, t_out))
  | _ => None
  };
};

let rec consistent = (a: Htyp.t, b: Htyp.t): bool => {
  (a == Hole || b == Hole)
  || a == b
  || Option.value(
       {
         let* (a_in, a_out) = extract_arrow(a);
         let* (b_in, b_out) = extract_arrow(b);
         Some(consistent(a_in, b_in) && consistent(a_out, b_out));
       },
       ~default=false,
     );
};

let rec syn = (ctx: typctx, e: Hexp.t): option(Htyp.t) => {
  switch (e) {
  | Var(name) => TypCtx.find_opt(name, ctx) // 1a
  | Ap(a, b) =>
    // 1b
    let* ap_type = syn(ctx, a);
    let* (in_ty, out_ty) = extract_arrow(ap_type);
    ana(ctx, b, in_ty) ? Some(out_ty) : None;
  | Lit(_) => Some(Num) // 1c
  | Plus(a, b) =>
    ana(ctx, a, Num) && ana(ctx, b, Num)
      // 1d
      ? Some(Num) : None
  | Asc(exp, typ) =>
    ana(ctx, exp, typ)
      // 1e
      ? Some(typ) : None
  | EHole => Some(Hole) // 1f
  | NEHole(_) => Some(Hole) // 1g
  | _ => None
  };
}

and ana = (ctx: typctx, e: Hexp.t, t: Htyp.t): bool => {
  switch (e) {
  // Double check: can Lam take the other branch?
  | Lam(var, body_e) =>
    switch (t) {
    | Hole => ana(TypCtx.add(var, Htyp.Hole, ctx), body_e, Htyp.Hole) // 2a
    | Arrow(t_1, t_2) => ana(TypCtx.add(var, t_1, ctx), body_e, t_2) // 2a
    | _ =>
      // 2b as backup
      switch (syn(ctx, e)) {
      | Some(syn_ty) => consistent(t, syn_ty)
      | None => false
      }
    }

  | _ =>
    // 2b
    switch (syn(ctx, e)) {
    | Some(syn_ty) => consistent(t, syn_ty)
    | None => false
    }
  };
};

let syn_action =
    (ctx: typctx, (e: Zexp.t, t: Htyp.t), a: Action.t)
    : option((Zexp.t, Htyp.t)) => {
  // Used to suppress unused variable warnings
  // Okay to remove
  let _ = ctx;
  let _ = e;
  let _ = t;
  let _ = a;

  raise(Unimplemented);
}

and ana_action =
    (ctx: typctx, e: Zexp.t, a: Action.t, t: Htyp.t): option(Zexp.t) => {
  // Used to suppress unused variable warnings
  // Okay to remove
  let _ = ctx;
  let _ = e;
  let _ = a;
  let _ = t;

  raise(Unimplemented);
};
