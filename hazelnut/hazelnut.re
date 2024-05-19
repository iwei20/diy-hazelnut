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

// WONTFIX: 9b 10ab 11ab are actionlist

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
let rec erase_exp = (e: Zexp.t): Hexp.t => {
  switch (e) {
  | Cursor(under_curs_exp) => under_curs_exp
  | Lam(var, body) => Lam(var, erase_exp(body))
  | LAp(applier, input) => Ap(erase_exp(applier), input)
  | RAp(applier, input) => Ap(applier, erase_exp(input))
  | LPlus(lhs, rhs) => Plus(erase_exp(lhs), rhs)
  | RPlus(lhs, rhs) => Plus(lhs, erase_exp(rhs))
  | LAsc(ann_exp, asc_typ) => Asc(erase_exp(ann_exp), asc_typ)
  | RAsc(ann_exp, asc_typ) => Asc(ann_exp, deep_erase_typ(asc_typ))
  | NEHole(hole_exp) => NEHole(erase_exp(hole_exp))
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
    // 1d
    ana(ctx, a, Num) && ana(ctx, b, Num) ? Some(Num) : None

  | Asc(exp, typ) => ana(ctx, exp, typ) ? Some(typ) : None // 1e
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

/*** MOVE ***/

/**
 * Matches a Z-type and move direction against the base-case move judgements and
 * outputs the RHS of a matching judgement.
 *
 * Returns None with no match.
 */
let do_move_typ = (t: Ztyp.t, d: Dir.t): option(Ztyp.t) => {
  switch (d) {
  | Child(which) =>
    let* ct = shallow_erase_typ(t);
    switch (ct) {
    | Arrow(t_in, t_out) =>
      switch (which) {
      | One => Some(Ztyp.LArrow(Ztyp.Cursor(t_in), t_out)) // 6a
      | Two => Some(Ztyp.RArrow(t_in, Ztyp.Cursor(t_out))) // 6b
      }
    | _ => None
    };

  | Parent =>
    switch (t) {
    | Cursor(_) => None
    | LArrow(t_in, t_out) =>
      // 6c
      let+ ct_in = shallow_erase_typ(t_in);
      Ztyp.Cursor(Htyp.Arrow(ct_in, t_out));

    | RArrow(t_in, t_out) =>
      // 6d
      let+ ct_out = shallow_erase_typ(t_out);
      Ztyp.Cursor(Htyp.Arrow(t_in, ct_out));
    }
  };
};

/**
 * Matches a Z-expression and move child 1 against the base-case
 * move judgements and outputs the RHS of a matching judgement.
 * Returns None with no match.
 */
let move_child_1 = (under_curs_exp: Hexp.t): option(Zexp.t) => {
  switch (under_curs_exp) {
  | Var(_) => None
  | Lam(var, body) => Some(Lam(var, Cursor(body))) // 8e
  | Ap(applier, input) => Some(LAp(Cursor(applier), input)) // 8g
  | Lit(_) => None
  | Plus(lhs, rhs) => Some(LPlus(Cursor(lhs), rhs)) // 8k
  | Asc(ann_exp, asc_typ) => Some(LAsc(Cursor(ann_exp), asc_typ)) // 8a
  | EHole => None
  | NEHole(hole_exp) => Some(NEHole(Cursor(hole_exp))) // 8o
  };
};

/**
 * Matches a Z-expression and move child 1 against the base-case
 * move judgements and outputs the RHS of a matching judgement.
 * Returns None with no match.
 */
let move_child_2 = (under_curs_exp: Hexp.t): option(Zexp.t) => {
  switch (under_curs_exp) {
  | Var(_) => None
  | Lam(_, _) => None
  | Ap(applier, input) => Some(RAp(applier, Cursor(input))) // 8h
  | Lit(_) => None
  | Plus(lhs, rhs) => Some(RPlus(lhs, Cursor(rhs))) // 8l
  | Asc(ann_exp, asc_typ) => Some(RAsc(ann_exp, Cursor(asc_typ))) // 8b
  | EHole => None
  | NEHole(_) => None
  };
};

/**
 * Matches a Z-expression and move direction against the base-case
 * move judgements and outputs the RHS of a matching judgement.
 *
 * Returns None with no match.
 */
let do_move_exp = (e: Zexp.t, dir: Dir.t): option(Zexp.t) => {
  switch (dir) {
  | Child(child_dir) =>
    switch (e) {
    | Cursor(under_curs_exp) =>
      switch (child_dir) {
      | One => move_child_1(under_curs_exp)
      | Two => move_child_2(under_curs_exp)
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

/*** CONSTRUCT ***/

/**
 * Matches a Z-type and construction shape against the base-case
 * construct judgements and outputs the RHS of a matching judgement.
 *
 * Returns None with no match.
 */
let construct_typ = (t: Ztyp.t, cnstr_shape: Shape.t): option(Ztyp.t) => {
  switch (cnstr_shape) {
  | Arrow =>
    // 12a
    let+ ct = shallow_erase_typ(t);
    Ztyp.RArrow(ct, Ztyp.Cursor(Htyp.Hole));

  | Num =>
    // 12b
    let* ct = shallow_erase_typ(t);
    switch (ct) {
    | Hole => Some(Ztyp.Cursor(Htyp.Num))
    | _ => None
    };

  | _ => None
  };
};

/**
 * Matches a Z-expression, type, and construction shape against the base-case
 * synthetic construct judgements and outputs the RHS of a matching judgement.
 *
 * Returns None with no match.
 */
let syn_construct_exp =
    (ctx: typctx, (e: Zexp.t, t: Htyp.t), cnstr_shape: Shape.t)
    : option((Zexp.t, Htyp.t)) => {
  switch (cnstr_shape) {
  | Arrow => None
  | Num => None
  | Asc =>
    // 13a
    let+ ce = shallow_erase_exp(e);
    (Zexp.RAsc(ce, Ztyp.Cursor(t)), t);

  | Var(name) =>
    // 13c
    let* ce = shallow_erase_exp(e);
    let* _t_hole_check =
      switch (t) {
      | Hole => Some()
      | _ => None
      };
    let* _e_hole_check =
      switch (ce) {
      | EHole => Some()
      | _ => None
      };
    let+ t_from_ctx = TypCtx.find_opt(name, ctx);
    (Zexp.Cursor(Hexp.Var(name)), t_from_ctx);

  | Lam(var) =>
    // 13e
    let* ce = shallow_erase_exp(e);
    let* _t_hole_check =
      switch (t) {
      | Hole => Some()
      | _ => None
      };
    let+ _e_hole_check =
      switch (ce) {
      | EHole => Some()
      | _ => None
      };
    (
      Zexp.RAsc(
        Hexp.Lam(var, Hexp.EHole),
        Ztyp.LArrow(Ztyp.Cursor(Htyp.Hole), Htyp.Hole),
      ),
      Htyp.Arrow(Htyp.Hole, Htyp.Hole),
    );

  | Ap =>
    let+ ce = shallow_erase_exp(e);
    switch (extract_arrow(t)) {
    // 13h
    | Some((_, t_out)) => (Zexp.RAp(ce, Zexp.Cursor(Hexp.EHole)), t_out)
    // 13i
    | None => (
        Zexp.RAp(Hexp.NEHole(ce), Zexp.Cursor(Hexp.EHole)),
        Htyp.Hole,
      )
    };

  | Lit(n) =>
    // 13j
    let* ce = shallow_erase_exp(e);
    let* _t_hole_check =
      switch (t) {
      | Hole => Some()
      | _ => None
      };
    let+ _e_hole_check =
      switch (ce) {
      | EHole => Some()
      | _ => None
      };
    (Zexp.Cursor(Hexp.Lit(n)), Htyp.Num);

  | Plus =>
    let+ ce = shallow_erase_exp(e);
    if (consistent(t, Htyp.Num)) {
      (
        // 13l
        Zexp.RPlus(ce, Zexp.Cursor(Hexp.EHole)),
        Htyp.Num,
      );
    } else {
      (
        // 13m
        Zexp.RPlus(Hexp.NEHole(ce), Zexp.Cursor(Hexp.EHole)),
        Htyp.Hole,
      );
    };

  | NEHole =>
    let+ _cursor_inside_check = shallow_erase_exp(e);
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
    Zexp.RAsc(ce, Ztyp.Cursor(t));

  | Var(varname) =>
    // 13d
    let* ce = shallow_erase_exp(e);
    let* _e_hole_check =
      switch (ce) {
      | EHole => Some()
      | _ => None
      };
    let* vartyp_from_ctx = TypCtx.find_opt(varname, ctx);
    // Not consistent ? 13d : subsumption
    !consistent(vartyp_from_ctx, t)
      ? Some(Zexp.NEHole(Zexp.Cursor(Hexp.Var(varname)))) : None;

  | Lam(var) =>
    let* ce = shallow_erase_exp(e);
    let* _e_hole_check =
      switch (ce) {
      | EHole => Some()
      | _ => None
      };
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
    };

  | Ap => None
  | Lit(n) =>
    let* ce = shallow_erase_exp(e);
    let* _e_hole_check =
      switch (ce) {
      | EHole => Some()
      | _ => None
      };
    // !consistent ? 13k : subsumption
    !consistent(t, Htyp.Num)
      ? Some(Zexp.NEHole(Zexp.Cursor(Hexp.Lit(n)))) : None;

  | Plus => None
  | NEHole => None
  };
};

/*** DELETION ***/

// 14
let delete_typ = (t: Ztyp.t): option(Ztyp.t) => {
  let+ _t_cursor_check = shallow_erase_typ(t);
  Ztyp.Cursor(Htyp.Hole);
};

let do_delete_exp = (e: Zexp.t): option(Zexp.t) => {
  let+ _e_cursor_check = shallow_erase_exp(e);
  Zexp.Cursor(Hexp.EHole);
};

/*** FINISH ***/
let syn_finish =
    (ctx: typctx, (e: Zexp.t, t: Htyp.t)): option((Zexp.t, Htyp.t)) => {
  // 16a
  let* ce = shallow_erase_exp(e);
  let* _t_hole_check =
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
  let* ce = shallow_erase_exp(e);
  switch (ce) {
  | NEHole(nee) => ana(ctx, nee, t) ? Some(Zexp.Cursor(nee)) : None
  | _ => None
  };
};

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
  | Some(_) => result
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
      // 7a
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
  | Some(_) => result
  | None =>
    // Zipper cases
    switch (e) {
    | Cursor(_) => None
    | Lam(_, _) => None
    | LAp(applier, input) =>
      // 18b
      let applier_erased = erase_exp(applier);
      let* applier_syn_t = syn(ctx, applier_erased);
      let* (applier_acted, applier_acted_syn_t) =
        syn_action(ctx, (applier, applier_syn_t), a);
      let* (t_in, t_out) = extract_arrow(applier_acted_syn_t);
      if (ana(ctx, input, t_in)) {
        Some((Zexp.LAp(applier_acted, input), t_out));
      } else {
        None;
      };

    | RAp(applier, input) =>
      // 18c
      let* applier_syn_t = syn(ctx, applier);
      let* (t_in, t_out) = extract_arrow(applier_syn_t);
      let+ input_acted = ana_action(ctx, input, a, t_in);
      (Zexp.RAp(applier, input_acted), t_out);

    | LPlus(lhs, rhs) =>
      // 18d
      let* _t_num_check =
        switch (t) {
        | Num => Some()
        | _ => None
        };
      let+ lhs_acted = ana_action(ctx, lhs, a, Htyp.Num);
      (Zexp.LPlus(lhs_acted, rhs), Htyp.Num);

    | RPlus(lhs, rhs) =>
      // 18e
      let* _t_num_check =
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
      let* asc_typ_acted = action_typ(asc_typ, a);
      if (t == deep_erase_typ(asc_typ)
          && ana(ctx, ann_exp, deep_erase_typ(asc_typ_acted))) {
        Some((
          Zexp.RAsc(ann_exp, asc_typ_acted),
          deep_erase_typ(asc_typ_acted),
        ));
      } else {
        None;
      };

    | NEHole(hole_exp) =>
      // 18h
      switch (t) {
      | Hole =>
        let hole_exp_erased = erase_exp(hole_exp);
        let* hole_exp_syn_t = syn(ctx, hole_exp_erased);
        let+ (hole_exp_acted, _) =
          syn_action(ctx, (hole_exp, hole_exp_syn_t), a);
        (Zexp.NEHole(hole_exp_acted), Htyp.Hole);

      | _ => None
      }
    }
  };
}

and subsumption_action =
    (ctx: typctx, e: Zexp.t, a: Action.t, t: Htyp.t): option(Zexp.t) => {
  // 5
  let e_erased = erase_exp(e);
  let* e_erased_syn_ty = syn(ctx, e_erased);
  let* (e_acted, t_syn_act) = syn_action(ctx, (e, e_erased_syn_ty), a);
  consistent(t, t_syn_act) ? Some(e_acted) : None;
}

and ana_action =
    (ctx: typctx, e: Zexp.t, a: Action.t, t: Htyp.t): option(Zexp.t) => {
  // Base case
  let result =
    switch (a) {
    | Move(dir) => do_move_exp(e, dir) // 7b
    | Construct(shape) => ana_construct_exp(ctx, e, shape, t)
    | Del => do_delete_exp(e) // 15b
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
