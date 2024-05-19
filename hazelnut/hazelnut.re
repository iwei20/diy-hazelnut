open Sexplib.Std;
open Monad_lib.Monad;

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

/**
 * For top-level cursor Z-expressions, returns the contents inside the cursor.
 * For other Z-expressions, returns nothing.
 */
let shallow_erase_exp = (e: Zexp.t): option(Hexp.t) => {
  switch (e) {
  | Cursor(under_curs_exp) => Some(under_curs_exp)
  | _ => None
  };
};

/**
 * For top-level cursor Z-types, returns the contents inside the cursor.
 * For other Z-types, returns nothing.
 */
let shallow_erase_typ = (t: Ztyp.t): option(Htyp.t) => {
  switch (t) {
  | Cursor(under_curs_typ) => Some(under_curs_typ)
  | _ => None
  };
};

/**
 * Performs cursor-erasure on a Z-expression, as described
 * in the Hazelnut paper.
 */
let rec deep_erase_exp = (e: Zexp.t): Hexp.t => {
  switch (e) {
  | Cursor(under_curs_exp) => under_curs_exp
  | Lam(var, body) => Lam(var, deep_erase_exp(body))
  | LAp(applier, input) => Ap(deep_erase_exp(applier), input)
  | RAp(applier, input) => Ap(applier, deep_erase_exp(input))
  | LPlus(lhs, rhs) => Plus(deep_erase_exp(lhs), rhs)
  | RPlus(lhs, rhs) => Plus(lhs, deep_erase_exp(rhs))
  | LAsc(ann_exp, asc_typ) => Asc(deep_erase_exp(ann_exp), asc_typ)
  | RAsc(ann_exp, asc_typ) => Asc(ann_exp, deep_erase_typ(asc_typ))
  | NEHole(hole_exp) => NEHole(deep_erase_exp(hole_exp))
  };
}

/**
 * Performs cursor-erasure on a Z-type, as described
 * in the Hazelnut paper.
 */
and deep_erase_typ = (t: Ztyp.t): Htyp.t => {
  switch (t) {
  | Cursor(under_curs_typ) => under_curs_typ
  | LArrow(t_in, t_out) => Arrow(deep_erase_typ(t_in), t_out)
  | RArrow(t_in, t_out) => Arrow(t_in, deep_erase_typ(t_out))
  };
};

/**
 * Attempts to match the given type as the LHS of
 * judgement 4a or 4b, and returns the output of that judgement
 * if a match is found. Otherwise, returns None.
 *
 * Note that 4a and 4b are mutually exclusive judgements.
 */
let extract_arrow = (t: Htyp.t): option((Htyp.t, Htyp.t)) => {
  switch (t) {
  | Hole => Some((Hole, Hole))
  | Arrow(t_in, t_out) => Some((t_in, t_out))
  | _ => None
  };
};

/**
 * Returns if a is consistent to b via a match with
 * judgements 3a-d.
 */
let rec consistent = (a: Htyp.t, b: Htyp.t): bool => {
  (a == Hole || b == Hole)
  || a == b
  || Option.value(
       {
         let* (a_in, a_out) = extract_arrow(a);
         let+ (b_in, b_out) = extract_arrow(b);
         consistent(a_in, b_in) && consistent(a_out, b_out);
       },
       ~default=false,
     );
};

let rec syn = (ctx: typctx, e: Hexp.t): option(Htyp.t) => {
  switch (e) {
  | Var(name) => TypCtx.find_opt(name, ctx) // 1a
  | Lam(_, _) => None
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
  };
}

and subsumption = (ctx: typctx, e: Hexp.t, t: Htyp.t): bool => {
  switch (syn(ctx, e)) {
  | Some(syn_ty) => consistent(t, syn_ty)
  | None => false
  };
}

and ana = (ctx: typctx, e: Hexp.t, t: Htyp.t): bool => {
  switch (e) {
  | Lam(var, body) =>
    switch (t) {
    | Hole =>
      // 2a
      let extend_ctx = TypCtx.add(var, Htyp.Hole, ctx);
      ana(extend_ctx, body, Htyp.Hole);
    | Arrow(t_in, t_out) =>
      // 2a
      let extend_ctx = TypCtx.add(var, t_in, ctx);
      ana(extend_ctx, body, t_out);
    | _ => subsumption(ctx, e, t)
    }
  | _ => subsumption(ctx, e, t)
  };
};

/* MOVE */
let do_move_typ = (t: Ztyp.t, d: Dir.t): option(Ztyp.t) => {
  switch (d) {
  | Child(which) =>
    // Must be under cursor
    let* ct = shallow_erase_typ(t);
    switch (ct) {
    // Only arrows have child-movement rules
    | Arrow(ty_in, ty_out) =>
      switch (which) {
      // 6a
      | One => Some(Ztyp.LArrow(Ztyp.Cursor(ty_in), ty_out))
      // 6b
      | Two => Some(Ztyp.RArrow(ty_in, Ztyp.Cursor(ty_out)))
      }
    | _ => None
    };
  | Parent =>
    switch (t) {
    | Cursor(_) => None
    | LArrow(ty_in, ty_out) =>
      // 6c
      let+ cty_in = shallow_erase_typ(ty_in);
      Ztyp.Cursor(Htyp.Arrow(cty_in, ty_out));
    | RArrow(ty_in, ty_out) =>
      // 6d
      let+ cty_out = shallow_erase_typ(ty_out);
      Ztyp.Cursor(Htyp.Arrow(ty_in, cty_out));
    }
  };
};

let move_child_1 = (under_curs_exp: Hexp.t): option(Zexp.t) => {
  switch (under_curs_exp) {
  | Var(_) => None
  | Lam(var, body) => Some(Lam(var, Cursor(body))) // 8e
  | Ap(applier, input) => Some(LAp(Cursor(applier), input)) // 8g
  | Lit(_) => None
  | Plus(a, b) => Some(LPlus(Cursor(a), b)) // 8k
  | Asc(typed_exp, typ) => Some(LAsc(Cursor(typed_exp), typ)) // 8a
  | EHole => None
  | NEHole(hole_contents) => Some(Cursor(hole_contents)) // 8o
  };
};

let move_child_2 = (under_curs_exp: Hexp.t): option(Zexp.t) => {
  switch (under_curs_exp) {
  | Var(_) => None
  | Lam(_, _) => None
  | Ap(applier, input) => Some(RAp(applier, Cursor(input))) // 8h
  | Lit(_) => None
  | Plus(a, b) => Some(RPlus(a, Cursor(b))) // 8l
  | Asc(typed_exp, typ) => Some(RAsc(typed_exp, Cursor(typ))) // 8b
  | EHole => None
  | NEHole(_) => None
  };
};

let do_move_exp = (e: Zexp.t, dir: Dir.t): option(Zexp.t) => {
  switch (dir) {
  | Child(child_dir) =>
    switch (e) {
    | Cursor(under_curs_exp) =>
      switch (child_dir) {
      | One => move_child_1(under_curs_exp) // 8aegko
      | Two => move_child_2(under_curs_exp) // 8bhl
      }
    | _ => None
    }
  | Parent =>
    switch (e) {
    | Cursor(_) => None
    | Lam(var, body) =>
      // 8f
      let+ extract_result = shallow_erase_exp(body);
      Zexp.Cursor(Lam(var, extract_result));
    | LAp(applier, input) =>
      // 8i
      let+ extract_result = shallow_erase_exp(applier);
      Zexp.Cursor(Ap(extract_result, input));
    | RAp(applier, input) =>
      // 8j
      let+ extract_result = shallow_erase_exp(input);
      Zexp.Cursor(Ap(applier, extract_result));
    | LPlus(a, b) =>
      // 8m
      let+ extract_result = shallow_erase_exp(a);
      Zexp.Cursor(Plus(extract_result, b));
    | RPlus(a, b) =>
      // 8n
      let+ extract_result = shallow_erase_exp(b);
      Zexp.Cursor(Plus(a, extract_result));
    | LAsc(typed_exp, typ) =>
      // 8c
      let+ extract_result = shallow_erase_exp(typed_exp);
      Zexp.Cursor(Asc(extract_result, typ));
    | RAsc(typed_exp, typ) =>
      // 8d
      let+ extract_result = shallow_erase_typ(typ);
      Zexp.Cursor(Asc(typed_exp, extract_result));
    | NEHole(hole_contents) =>
      // 8p
      let+ extract_result = shallow_erase_exp(hole_contents);
      Zexp.Cursor(NEHole(extract_result));
    }
  };
};

/* CONSTRUCT */
let construct_typ = (t: Ztyp.t, cnstr_shape: Shape.t): option(Ztyp.t) => {
  switch (cnstr_shape) {
  // 12a
  | Arrow =>
    // Must be under cursor
    let+ ct = shallow_erase_typ(t);
    Ztyp.RArrow(ct, Ztyp.Cursor(Htyp.Hole));
  // 12b
  | Num =>
    // Must be under cursor
    let* ct = shallow_erase_typ(t);
    // Must be a hole
    switch (ct) {
    | Hole => Some(Ztyp.Cursor(Htyp.Num))
    | _ => None
    };
  | _ => None // These shapes are for expressions
  };
};

let syn_construct_exp =
    (ctx: typctx, (e: Zexp.t, t: Htyp.t), cnstr_shape: Shape.t)
    : option((Zexp.t, Htyp.t)) => {
  switch (cnstr_shape) {
  | Arrow => None // 12a These are shapes for types
  | Num => None // 12b These are shapes for types
  | Asc =>
    // 13a
    let+ ce = shallow_erase_exp(e);
    // Cursor moves to annotation
    (Zexp.RAsc(ce, Ztyp.Cursor(t)), t);
  | Var(varname) =>
    // 13c
    // Must be an empty hole synthesizing EHole
    let* ce = shallow_erase_exp(e);
    switch (ce) {
    | EHole =>
      switch (t) {
      | Hole =>
        let+ type_from_ctx = TypCtx.find_opt(varname, ctx);
        (Zexp.Cursor(Hexp.Var(varname)), type_from_ctx);
      | _ => None
      }
    | _ => None
    };
  | Lam(var) =>
    // 13e
    // Must be an empty hole synthesizing EHole
    let* ce = shallow_erase_exp(e);
    switch (ce) {
    | EHole =>
      switch (t) {
      | Hole =>
        Some((
          Zexp.RAsc(
            Hexp.Lam(var, Hexp.EHole),
            Ztyp.LArrow(Ztyp.Cursor(Htyp.Hole), Htyp.Hole),
          ),
          Htyp.Arrow(Htyp.Hole, Htyp.Hole),
        ))
      | _ => None
      }
    | _ => None
    };
  | Ap =>
    let+ ce = shallow_erase_exp(e);
    switch (extract_arrow(t)) {
    // 13h
    | Some((_, out_ty)) => (Zexp.RAp(ce, Zexp.Cursor(Hexp.EHole)), out_ty)
    // 13i
    | None => (
        Zexp.RAp(Hexp.NEHole(ce), Zexp.Cursor(Hexp.EHole)),
        Htyp.Hole,
      )
    };

  | Lit(n) =>
    // 13j
    // Must be an empty hole synthesizing EHole
    let* ce = shallow_erase_exp(e);
    switch (ce) {
    | EHole =>
      switch (t) {
      | Hole => Some((Zexp.Cursor(Hexp.Lit(n)), Htyp.Num))
      | _ => None
      }
    | _ => None
    };
  | Plus =>
    let+ ce = shallow_erase_exp(e);
    if (consistent(t, Htyp.Num)) {
      (
        Zexp.RPlus(ce, Zexp.Cursor(Hexp.EHole)),
        Htyp.Num // 13l
      );
    } else {
      (
        Zexp.RPlus(Hexp.NEHole(ce), Zexp.Cursor(Hexp.EHole)),
        Htyp.Hole // 13m
      );
    };
  | NEHole =>
    let+ _ = shallow_erase_exp(e); // Verify it has a cursor
    (Zexp.NEHole(e), Htyp.Hole);
  };
};

let ana_construct_exp =
    (ctx: typctx, e: Zexp.t, cnstr_shape: Shape.t, t: Htyp.t): option(Zexp.t) => {
  switch (cnstr_shape) {
  | Arrow => None
  | Num => None
  | Asc =>
    // 13b
    let+ ce = shallow_erase_exp(e);
    // Cursor moves to annotation
    Zexp.RAsc(ce, Ztyp.Cursor(t));
  | Var(varname) =>
    // 13d
    let* ce = shallow_erase_exp(e);
    switch (ce) {
    // require empty hole
    | EHole =>
      let* vartyp_from_ctx = TypCtx.find_opt(varname, ctx);
      // not consistent ? 13d : subsumption
      !consistent(vartyp_from_ctx, t)
        ? Some(Zexp.NEHole(Zexp.Cursor(Hexp.Var(varname)))) : None;
    | _ => None
    };
  | Lam(var) =>
    let* ce = shallow_erase_exp(e);
    switch (ce) {
    // require empty hole
    | EHole =>
      switch (extract_arrow(t)) {
      // 13f
      | Some((_, _)) => Some(Zexp.Lam(var, Zexp.Cursor(Hexp.EHole)))
      // 13g
      | None =>
        Some(
          Zexp.NEHole(
            Zexp.RAsc(
              Hexp.Lam(var, Hexp.EHole),
              Ztyp.LArrow(Ztyp.Cursor(Htyp.Hole), Htyp.Hole),
            ),
          ),
        )
      }
    | _ => None
    };
  | Ap => None // subsumption
  | Lit(n) =>
    let* ce = shallow_erase_exp(e);
    switch (ce) {
    // require empty hole
    | EHole =>
      if (!consistent(t, Htyp.Num)) {
        // 13k
        Some(Zexp.NEHole(Zexp.Cursor(Hexp.Lit(n))));
      } else {
        None;
      }
    | _ => None
    };
  | Plus => None // subsumption
  | NEHole => None // subsumption
  };
};

/* DELETION */

// 14
let delete_typ = (t: Ztyp.t): option(Ztyp.t) => {
  let+ _ = shallow_erase_typ(t);
  Ztyp.Cursor(Htyp.Hole);
};

let do_delete_exp = (e: Zexp.t): option(Zexp.t) => {
  // Must be expression under cursor
  let+ _ = shallow_erase_exp(e);
  Zexp.Cursor(Hexp.EHole);
};

/* FINISH */
let syn_finish =
    (ctx: typctx, (e: Zexp.t, t: Htyp.t)): option((Zexp.t, Htyp.t)) => {
  // 16a
  // Must be expression under cursor
  let* ce = shallow_erase_exp(e);
  // Check LHS t is hole or fail early
  let* _ =
    switch (t) {
    | Hole => Some()
    | _ => None
    };
  switch (ce) {
  | NEHole(nee) =>
    let+ syn_ty = syn(ctx, nee);
    (Zexp.Cursor(nee), syn_ty);
  | _ => None
  };
};

let ana_finish = (ctx: typctx, e: Zexp.t, t: Htyp.t): option(Zexp.t) => {
  // 16b
  // Must be expression under cursor
  let* ce = shallow_erase_exp(e);
  switch (ce) {
  | NEHole(nee) =>
    if (ana(ctx, nee, t)) {
      Some(Zexp.Cursor(nee));
    } else {
      None;
    }
  | _ => None
  };
};

// WONTFIX: 9b 10ab 11ab are actionlist
let rec action_typ = (t: Ztyp.t, a: Action.t): option(Ztyp.t) => {
  // Base case
  let result =
    switch (a) {
    | Move(dir) => do_move_typ(t, dir)
    | Construct(shape) => construct_typ(t, shape)
    | Del => delete_typ(t)
    | Finish => None
    };
  switch (result) {
  | Some(result) => Some(result)
  | None =>
    // Zipper cases
    switch (t) {
    | LArrow(in_ty, out_ty) =>
      // 17a
      switch (action_typ(in_ty, a)) {
      | Some(in_ty_modified) => Some(Ztyp.LArrow(in_ty_modified, out_ty))
      | None => None
      }
    | RArrow(in_ty, out_ty) =>
      // 17b
      switch (action_typ(out_ty, a)) {
      | Some(out_ty_modified) => Some(Ztyp.RArrow(in_ty, out_ty_modified))
      | None => None
      }
    | _ => None
    }
  };
};

let rec syn_action =
        (ctx: typctx, (e: Zexp.t, t: Htyp.t), a: Action.t)
        : option((Zexp.t, Htyp.t)) => {
  // Base case
  let result =
    switch (a) {
    | Move(dir) =>
      // Moves are type independent (7a), so if the move is valid, second return is always t
      let+ move_result = do_move_exp(e, dir);
      (move_result, t);
    | Construct(shape) => syn_construct_exp(ctx, (e, t), shape)
    | Del =>
      // 15a
      let+ del_result = do_delete_exp(e);
      (del_result, Htyp.Hole);
    | Finish => syn_finish(ctx, (e, t))
    };
  switch (result) {
  | Some(result) => Some(result)
  | None =>
    // Zipper cases
    switch (e) {
    | Cursor(_) => None
    | Lam(_, _) => None
    | LAp(applier, input) =>
      // 18b
      let applier_erased = deep_erase_exp(applier);
      let* applier_syn_ty = syn(ctx, applier_erased);
      let* (applier_acted, applier_acted_syn_ty) =
        syn_action(ctx, (applier, applier_syn_ty), a);
      let* (ty_in, ty_out) = extract_arrow(applier_acted_syn_ty);
      if (ana(ctx, input, ty_in)) {
        Some((Zexp.LAp(applier_acted, input), ty_out));
      } else {
        None;
      };
    | RAp(applier, input) =>
      // 18c
      let* applier_syn_ty = syn(ctx, applier);
      let* (ty_in, ty_out) = extract_arrow(applier_syn_ty);
      let+ input_acted = ana_action(ctx, input, a, ty_in);
      (Zexp.RAp(applier, input_acted), ty_out);
    | LPlus(lhs, rhs) =>
      // 18d
      // check t is Num
      let* _ =
        switch (t) {
        | Num => Some()
        | _ => None
        };
      let+ lhs_acted = ana_action(ctx, lhs, a, Htyp.Num);
      (Zexp.LPlus(lhs_acted, rhs), Htyp.Num);
    | RPlus(lhs, rhs) =>
      // 18e
      // check t is Num
      let* _ =
        switch (t) {
        | Num => Some()
        | _ => None
        };
      let+ rhs_acted = ana_action(ctx, rhs, a, Htyp.Num);
      (Zexp.RPlus(lhs, rhs_acted), Htyp.Num);
    | LAsc(ann_exp, asc_typ) =>
      // 18f
      if (t == asc_typ) {
        let+ ann_exp_acted = ana_action(ctx, ann_exp, a, t);
        (Zexp.LAsc(ann_exp_acted, t), t);
      } else {
        None;
      }
    | RAsc(ann_exp, asc_typ) =>
      // 18g
      if (t == deep_erase_typ(asc_typ)) {
        let* asc_typ_acted = action_typ(asc_typ, a);
        if (ana(ctx, ann_exp, deep_erase_typ(asc_typ_acted))) {
          Some((
            Zexp.RAsc(ann_exp, asc_typ_acted),
            deep_erase_typ(asc_typ_acted),
          ));
        } else {
          None;
        };
      } else {
        None;
      }
    | NEHole(in_hole) =>
      // 18h
      switch (t) {
      | Hole =>
        let in_hole_erased = deep_erase_exp(in_hole);
        let* in_hole_syn_ty = syn(ctx, in_hole_erased);
        let+ (e_acted, _) = syn_action(ctx, (in_hole, in_hole_syn_ty), a);
        (Zexp.NEHole(e_acted), Htyp.Hole);
      | _ => None
      }
    }
  };
}

and subsumption_action =
    (ctx: typctx, e: Zexp.t, a: Action.t, t: Htyp.t): option(Zexp.t) => {
  // Subsumption 5
  let e_erased = deep_erase_exp(e); // ehat-erased
  let* e_erased_syn_ty = syn(ctx, e_erased); // ehat-erased => tau'
  let* (e_acted, t_syn_act) = syn_action(ctx, (e, e_erased_syn_ty), a); // ehat => tau' a-> ehat' => tau''
  consistent(t, t_syn_act) ? Some(e_acted) : None; // tau \sim tau''
}

and ana_action =
    (ctx: typctx, e: Zexp.t, a: Action.t, t: Htyp.t): option(Zexp.t) => {
  // Base case
  let result =
    switch (a) {
    | Move(dir) => do_move_exp(e, dir) // 7b analytic move judgement independent of type
    | Construct(shape) => ana_construct_exp(ctx, e, shape, t)
    // 15b
    | Del => do_delete_exp(e)
    | Finish => ana_finish(ctx, e, t)
    };
  // Zipper case
  let result =
    switch (result) {
    | Some(_) => result
    | None =>
      switch (e) {
      | Lam(var, body) =>
        // 18a
        let* (ty_in, ty_out) = extract_arrow(t);
        let+ body_acted =
          ana_action(TypCtx.add(var, ty_in, ctx), body, a, ty_out);
        Zexp.Lam(var, body_acted);
      | _ => None
      }
    };
  // Algorithmically, subsumption should be the rule of last resort (see Sec. 3.4 for further discussion.)
  switch (result) {
  | Some(_) => result
  | None => subsumption_action(ctx, e, a, t)
  };
};
