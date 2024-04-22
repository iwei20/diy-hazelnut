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

let erase_exp = (e: Zexp.t): Hexp.t => {
  // Used to suppress unused variable warnings
  // Okay to remove
  let _ = e;

  raise(Unimplemented);
};

let rec consistent = (a: Htyp.t, b: Htyp.t): bool => {
  (a == Hole || b == Hole)
  || a == b
  || {
    switch (
      {
        let* (a_in, a_out) =
          switch (a) {
          | Arrow(t_in, t_out) => Some((t_in, t_out))
          | _ => None
          };
        let* (b_in, b_out) =
          switch (b) {
          | Arrow(t_in, t_out) => Some((t_in, t_out))
          | _ => None
          };
        Some(consistent(a_in, b_in) && consistent(a_out, b_out));
      }
    ) {
    | Some(bool) => bool
    | None => false
    };
  };
};

let rec syn = (ctx: typctx, e: Hexp.t): option(Htyp.t) => {
  switch (e) {
  | Var(name) => TypCtx.find_opt(name, ctx) // 1a
  | Ap(a, b) =>
    // 1b
    let* ap_type = syn(ctx, a);
    let* (in_ty, out_ty) =
      switch (ap_type) {
      | Hole => Some((Htyp.Hole, Htyp.Hole))
      | Arrow(t_1, t_2) => Some((t_1, t_2))
      | _ => None
      };
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
    | Arrow(t_1, t_2) => ana(TypCtx.add(var, t_1, ctx), body_e, t_2)  // 2a
    | _ => // 2b as backup
      switch (syn(ctx, e)) {
      | Some(syn_ty) => consistent(t, syn_ty)
      | None => false
      }
    }

  | _ => // 2b
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
