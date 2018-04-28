module S = Syntax

(* |- Γ *)
module rec Context : sig
  val check : S.Context.t -> unit
end = struct
  module C = S.Context
  open C.Item

  let check = function
  (* ctx_empty *)
  | [] -> ()

  (* ctx_type *)
  | Type ((typevar, stamp), (_as, kind)) :: gamma ->
    begin
      assert (not (C.contains_stamp stamp gamma));
      Kind.check (C.cons_type_params gamma _as) kind
    end

  (* ctx_value *)
  | Val ((termvar, stamp), typ) :: gamma ->
    begin
      assert (not (C.contains_stamp stamp gamma));
      Type.check gamma (typ, S.Kind.Other)
    end

  (* ctx_modtype *)
  | ModType ((modtypevar, stamp), modkind) :: gamma ->
    begin
      assert (not (C.contains_stamp stamp gamma));
      ModuleKind.check gamma modkind
    end

  (* ctx_module *)
  | Mod ((modvar, stamp), (modtype, modkind)) :: gamma ->
    begin
      assert (not (C.contains_stamp stamp gamma));
      ModuleType.check gamma (modtype, modkind)
    end
end

(* Γ |- k *)
and Kind : sig
  val check : S.Context.t -> S.Kind.t -> unit
end = struct
  open S.Kind

  let check gamma = function
  (* knd_other *)
  | Other -> Context.check gamma

  (* knd_singleton_kind *)
  | Singleton (t, k) -> Type.check gamma (t, k)
end

(* Γ |- K *)
and ModuleKind : sig
  val check : S.Context.t -> S.ModuleKind.t -> unit
end = struct
  open S.ModuleKind

  let check gamma = function
  (* mknd_level *)
  | Level l -> Context.check gamma

  (* mknd_singleton_kind *)
  | Singleton (t, k) -> ModuleType.check gamma (t, k)
end

(* Γ |- t : k *)
and Type : sig
  val check : S.Context.t -> S.Type.t * S.Kind.t -> unit
end = struct
  module T = S.Type
  module K = S.Kind
  module MT = S.ModuleType
  module SI = S.SignatureItem
  module SIG = S.Signature

  let check gamma = function
  (* typ_var *)
  | (T.Var (ts, ai), k) ->
    begin
      match S.Context.find_type ai gamma with
      | Some (S.Context.Item.Type (_, (_as, _))) ->
        TypeArgs.check gamma (ts, _as)
      | _ -> failwith "type error"
    end

  (* typ_proj *)
  | (T.Proj (ts, ev, a), k) ->
    begin
      (* todo: not sure that this is a correct way to get "as" *)
      match S.Context.find_type' a gamma with
      | Some (S.Context.Item.Type (ai, (_as, k'))) when k = k' ->
        begin
          ModuleExpressionValue.check gamma (ev, MT.Sig (SIG.Cons (SI.Type (ai, (_as, k')), SIG.End)));
          TypeArgs.check gamma (ts, _as)
        end
      | _ -> failwith "type error"
    end

  (* typ_other *)
  | (T.Other, K.Other) -> Context.check gamma

  (* typ_singleton *)
  | (t, K.Singleton (t', k)) when t = t' -> Type.check gamma (t, k)

  (* typ_subsumption *)
  | (t, k2) ->
    begin
      (* infer kind of t *)
      match t with
      | T.Other -> SubKind.check gamma (K.Other, k2)
      | _ -> failwith "not implemented"
    end
end

(* Γ |- ts : as *)
and TypeArgs : sig
  val check : S.Context.t -> S.TypeArgs.t * S.TypeParams.t -> unit
end = struct
  module A = S.TypeArgs
  module P = S.TypeParams

  let check gamma = function
  (* typs_nil *)
  | (A.Epsilon, P.Epsilon) -> Context.check gamma

  (* typs_cons *)
  | (A.Cons (t, ts), P.Cons ((_, k), _as)) ->
    begin
      Type.check gamma (t, k);
      TypeArgs.check gamma (ts, _as)
    end

  | _ -> failwith "type error"
end

(* Γ |- SI : l *)
and SignatureItem : sig
  val check : S.Context.t -> S.SignatureItem.t * S.Level.t -> unit
end = struct
  module C = S.Context
  module MK = S.ModuleKind
  open S.SignatureItem
  open S.Level

  let check gamma = function
  (* sitem_type *)
  | (Type (_, (_as, k)), Zero) -> Kind.check (C.cons_type_params gamma _as) k

  (* sitem_value *)
  | (Val (_, t), Zero) -> Type.check gamma (t, S.Kind.Other)

  (* sitem_modtype *)
  | (ModuleType (_, k), l) ->
    begin
      ModuleKind.check gamma k;
      SubModuleKind.check gamma (k, MK.Level l)
    end

  (* sitem_module *)
  | (Module (_, (t, k)), l) ->
    begin
      ModuleType.check gamma (t, k);
      SubModuleKind.check gamma (k, MK.Level l)
    end

  | _ -> failwith "type error"
end

(* Γ |- S : l *)
and Signature : sig
  val check : S.Context.t -> S.Signature.t * S.Level.t -> unit
end = struct
  module L =  S.Level
  module C = S.Context
  module S = S.Signature

  let check gamma = function
  (* sig_empty *)
  | (S.End, L.Zero) -> Context.check gamma

  (* sig_cons *)
  | (S.Cons (si, s), L.Max (l, l')) ->
    begin
      assert (not (S.contains_signature_item si s));
      SignatureItem.check gamma (si, l);
      Signature.check (C.cons_signature_item gamma si) (s, l');
    end

  | _ -> failwith "type error"
end

(* Γ |- T : K *)
and ModuleType : sig
  val check : S.Context.t -> S.ModuleType.t * S.ModuleKind.t -> unit
end = struct
  module T = S.ModuleType
  module K = S.ModuleKind
  module L = S.Level
  module C = S.Context
  module SI = S.SignatureItem
  module S = S.Signature

  let check gamma = function
  (* mtyp_signature *)
  | (T.Sig s, K.Level l) -> Signature.check gamma (s, l)

  (* mtyp_functor *)
  | (T.Functor (m, (xi, t), t'), K.Level L.Max (l, l')) when t = t' ->
    begin
      ModuleType.check gamma (t, K.Level l);
      ModuleType.check (C.Item.Mod (xi, (t, K.Level l)) :: gamma) (t, K.Level l')
    end

  (* mtyp_var *)
  | (T.Var (a, i), k) -> assert (C.contains (C.Item.ModType ((a, i), k)) gamma)

  (* mtyp_proj *)
  | (T.Proj (ev, a), k) ->
    (* how to get i? *)
    (* let s = (S.Cons ((SI.ModuleType ((a, i), k)), S.End)) in *)
    (* ModuleExpressionValue.check gamma (e, T.Sig s) *)
    failwith "not implemented"

  (* mtyp_singleton_type *)
  | (T.Singleton (ev, t), k) ->
    begin
      ModuleExpressionValue.check gamma (ev, t);
      ModuleType.check gamma (t, k)
    end

  (* mtyp_singleton *)
  | (t, K.Singleton (t', k)) when t = t' -> ModuleType.check gamma (t, k)

  (* mtyp_subsumption *)
  | (t, k2) ->
    begin
      (* how to get k1? *)
      (* ModuleType.check gamma (t, k1); *)
    end
end

(* Γ |- e : t *)
and Expression : sig
  val check : S.Context.t -> S.Expression.t * S.Type.t -> unit
end = struct
  module C = S.Context
  module E = S.Expression
  module T = S.Type
  module MT = S.ModuleType
  module SI = S.SignatureItem
  module S = S.Signature

  let check gamma = function
  (* expr_var *)
  | (E.Var (x, i), t) -> assert (C.contains (C.Item.Val ((x, i), t)) gamma)

  (* expr_proj *)
  | (E.Proj (ev, x), t) ->
    (* how to get i? *)
    (* let s = S.Cons ((SI.Val ((x, i), t)), S.End) in
    ModuleExpressionValue.check gamma (ev, MT.Sig s) *)
    failwith "not implemented"

  (* expr_other *)
  | (E.Other, T.Other) -> Context.check gamma

  | _ -> failwith "type error"
end

(* Γ |- DI : SI *)
and DefinitionItem : sig
  val check : S.Context.t -> S.DefinitionItem.t * S.SignatureItem.t -> unit
end = struct
  module DI = S.DefinitionItem
  module SI = S.SignatureItem
  module C = S.Context

  let check gamma = function
  (* ditem_type *)
  | (DI.Type (ai, (_as, k)), SI.Type (ai', (_as', k')))
    when ai = ai' && _as = _as' && k = k' ->
      Kind.check (C.cons_type_params gamma _as) k

  (* ditem_value *)
  | (DI.Val (xi, e), SI.Val (xi', t)) when xi = xi' ->
    Expression.check gamma (e, t)

  (* ditem_modtype *)
  | (DI.ModuleType (ai, k), SI.ModuleType (ai', k'))
    when ai = ai' && k = k' -> ModuleKind.check gamma k

  (* ditem_module *)
  | (DI.Module (xi, e), SI.Module (xi', (t, k))) when xi = xi' ->
    ModuleExpression.check gamma (e, t)

  | _ -> failwith "type error"
end

(* Γ |- D : S *)
and Definition : sig
  val check : S.Context.t -> S.Definition.t * S.Signature.t -> unit
end = struct
  module D = S.Definition
  module C = S.Context
  module S = S.Signature

  let check gamma = function
  (* def_empty *)
  | (D.End, S.End) -> Context.check gamma

  (* def_cons *)
  | (D.Cons (di, d), S.Cons (si, s)) ->
    begin
      DefinitionItem.check gamma (di, si);
      Definition.check (C.cons_signature_item gamma si) (d, s)
    end

  | _ -> failwith "type error"
end

(* Γ |- DIv : SIv *)
(* todo: ^ is not described in pdf *)
and DefinitionValueItem : sig
  val check : S.Context.t -> S.DefinitionValueItem.t * S.SignatureValueItem.t -> unit
end = struct
  module C = S.Context
  module DVI = S.DefinitionValueItem
  module SVI = S.SignatureValueItem

  let check gamma = function
  (* dvitem_type *)
  | (DVI.Type (ai, (_as, k)), SVI.Type (ai', (_as', k')))
    when ai = ai' && _as = _as' && k = k' ->
      Kind.check (C.cons_type_params gamma _as) k

  (* dvitem_modtype *)
  | (DVI.ModuleType (ai, k), SVI.ModuleType (ai', k'))
    when ai = ai' && k = k' -> ModuleKind.check gamma k

  (* dvitem_module *)
  | (DVI.Module (xi, e), SVI.Module (xi', (t, k))) when xi = xi' ->
    ModuleExpressionValue.check gamma (e, t)

  | _ -> failwith "type error"
end

(* Γ |- Dv : Sv *)
(* todo: ^ is not described in pdf *)
and DefinitionValue : sig
  val check : S.Context.t -> S.DefinitionValue.t * S.SignatureValue.t -> unit
end = struct
  module C = S.Context
  module DV = S.DefinitionValue
  module SV = S.SignatureValue

  let check gamma = function
  (* defv_empty *)
  | (DV.End, SV.End) -> Context.check gamma

  (* defv_cons *)
  | (DV.Cons (dvi, dv), SV.Cons (svi, sv)) ->
    begin
      DefinitionValueItem.check gamma (dvi, svi);
      DefinitionValue.check (C.cons_signature_value_item gamma svi) (dv, sv)
    end

  | _ -> failwith "type error"
end

(* Γ |- E : T *)
and ModuleExpression : sig
  val check : S.Context.t -> S.ModuleExpression.t * S.ModuleType.t -> unit
end = struct
  module M = S.ModuleExpression
  module T = S.ModuleType
  module C = S.Context
  module SI = S.SignatureItem
  module S = S.Signature

  let check gamma = function
  (* mexpr_var *)
  | (M.Var (x, i), t) -> assert (C.contains_modvar_modtype ((x, i), t) gamma)

  (* mexpr_proj *)
  | (M.Proj (ev, x), t) ->
    begin
      (* todo: how to get 'i'? *)
      (* ModuleExpressionValue.check gamma (S.Cons (SI.Module (xi, t)) S.End) *)
      failwith "not implemented"
    end

  (* mexpr_structure *)
  | (M.Struct d, T.Sig s) -> Definition.check gamma (d, s)

  (* mexpr_functor *)
  | (M.Functor (m, (xi, t1), e), T.Functor (m', (xi', t1'), t2))
    when m = m' && xi = xi' && t1 = t1' ->
      begin
        (* todo: how to get 'l'? *)
        (* ModuleType.check gamma (t2, l) *)
        (* todo: t1 = t2 ? *)
        (* ModuleExpression.check (C.Item.Mod (xi, t1, l) :: gamma) (e, t2); *)
        failwith "not implemented"
      end

  (* mexpr_apply *)
  | (M.App (e, m, ev), t) -> failwith "not implemented"

  (* mexpr_ascripe *)
  | (M.Ascription (e, t), t') when t = t' ->
    ModuleExpression.check gamma (e, t)

  (* mexpr_singleton *)
  | (ev, T.Singleton (ev', t)) ->
    (* how to check if ev = ev'? *)
    ModuleExpressionValue.check gamma (ev', t)

  (* mexpr_subsumption *)
  | (e, t2) -> failwith "not implemented"
end

(* Γ |- k ≤ k' *)
and SubKind : sig
  val check : S.Context.t -> S.Kind.t * S.Kind.t -> unit
end = struct
  module K = S.Kind

  let check gamma = function
  (* sub_knd_singleton *)
  | (K.Singleton (t, k), K.Singleton (t', k')) ->
    begin
      TypeEquality.check gamma (t, t', k);
      SubKind.check gamma (k, k')
    end

  (* sub_knd_sub_singleton *)
  | (K.Singleton (t, k), k') when k = k' ->
    begin
      Kind.check gamma (K.Singleton (t, k))
    end

  (* sub_knd_refl *)
  | (k, k') when k = k' -> Kind.check gamma k

  (* sub_knd_trans *)
  | (k1, k3) ->
    begin
      (* how to get k2? *)
      failwith "not implemented"
    end
end

(* Γ |- K ≤ K' *)
and SubModuleKind : sig
  val check : S.Context.t -> S.ModuleKind.t * S.ModuleKind.t -> unit
end = struct
  module MK = S.ModuleKind
  module L = S.Level

  let check gamma = function
  (* sub_mknd_successor *)
  | (MK.Level l, MK.Level (L.Succ l')) when l = l' ->
    ModuleKind.check gamma (MK.Level l)

  (* sub_mknd_singleton *)
  | (MK.Singleton (t, k), MK.Singleton (t', k')) ->
    begin
      ModuleTypeEquality.check gamma (t, t', k);
      SubModuleKind.check gamma (k, k')
    end

  (* sub_mknd_sub_singleton *)
  | (MK.Singleton (t, k), k') when k = k' ->
    ModuleKind.check gamma (MK.Singleton (t, k))

  (* sub_mknd_refl *)
  | (k, k') when k = k' ->
    ModuleKind.check gamma k

  (* sub_mknd_trans *)
  | (k, k') ->
    failwith "not implemented"
end

(* Γ |- Ev : T *)
and ModuleExpressionValue : sig
  val check : S.Context.t -> S.ModuleExpressionValue.t * S.ModuleType.t -> unit
end = struct
  let check gamma = function
  | _ -> failwith "not implemented"
end

(* Γ |- k = k' *)
and KindEquality : sig
  val check : S.Context.t -> S.Kind.t * S.Kind.t -> unit
end = struct
  module K = S.Kind

  let check gamma = function
  (* eql_knd_refl *)
  | (k, k') when k = k' -> Kind.check gamma k

  (* eql_knd_singleton *)
  | (K.Singleton (t, k), K.Singleton (t', k')) ->
    begin
      TypeEquality.check gamma (t, t', k);
      KindEquality.check gamma (k, k')
    end

  (* eql_knd_trans *)
  | _ -> failwith "not implemented"
end

(* Γ |- t = t' : k *)
and TypeEquality : sig
  val check : S.Context.t -> S.Type.t * S.Type.t * S.Kind.t -> unit
end = struct
  module T = S.Type
  module MT = S.ModuleType
  module SIG = S.Signature
  module SI = S.SignatureItem
  module K = S.Kind

  let check gamma = function
  (* eql_typ_proj *)
  | (T.Proj (ts, ev, a), T.Proj (ts', ev', a'), k) when a = a' ->
    begin
      (* todo: not sure that this is a correct way to get "as" *)
      match S.Context.find_type' a gamma with
      | Some (S.Context.Item.Type (ai, (_as, k'))) when k = k' ->
        begin
          ModuleExpressionValueEquality.check gamma (ev, ev', MT.Sig (SIG.Cons (SI.Type (ai, (_as, k')), SIG.End)));
          TypeArgs.check gamma (ts, _as)
        end
      | _ -> failwith "type error"
    end

  (* eql_typ_singleton *)
  | (t, t', k) -> Type.check gamma (t, K.Singleton (t', k))

  (* eql_typ_trans *)
  | _ -> failwith "not implemented"
end

(* Γ |- K = K' *)
and ModuleKindEquality : sig
  val check : S.Context.t -> S.ModuleKind.t * S.ModuleKind.t -> unit
end = struct
  module MK = S.ModuleKind

  let check gamma = function
  (* eql_mknd_refl *)
  | (k, k') when k = k' -> ModuleKind.check gamma k

  (* eql_mknd_singleton *)
  | (MK.Singleton (t, k), MK.Singleton (t', k')) ->
    begin
      ModuleTypeEquality.check gamma (t, t', k);
      ModuleKindEquality.check gamma (k, k')
    end

  (* eql_mknd_trans *)
  | _ -> failwith "not implemented"
end

(* Γ |- SI = SI' : l *)
and SignatureItemEquality : sig
  val check : S.Context.t -> S.SignatureItem.t * S.SignatureItem.t * S.Level.t -> unit
end = struct
  module L = S.Level
  module C = S.Context
  module K = S.Kind
  module MK = S.ModuleKind
  module SI = S.SignatureItem

  let check gamma = function
  (* eql_sitem_type *)
  | (SI.Type (ai1, (as_, k1)), SI.Type (ai2, (as_', k2)), L.Zero)
    when as_ = as_' ->
      KindEquality.check (C.cons_type_params gamma as_) (k1, k2)

  (* eql_sitem_value *)
  | (SI.Val (xi, t), SI.Val (xi', t'), L.Zero) ->
    TypeEquality.check gamma (t, t', K.Other)

  (* eql_sitem_modtype *)
  | (SI.ModuleType (ai, k), SI.ModuleType (ai', k'), l) ->
    begin
      ModuleKindEquality.check gamma (k, k');
      SubModuleKind.check gamma (k, MK.Level l)
    end

  (* eql_sitem_module *)
  | (SI.Module (xi, (t, k)), SI.Module (xi', (t', k')), l)
    when k = k' ->
    (* ^ todo: should we check if k = k'? *)
      begin
        ModuleTypeEquality.check gamma (t, t', k);
        SubModuleKind.check gamma (k, MK.Level l)
      end

  | _ -> failwith "type error"
end

(* Γ |- S = S' : l *)
and SignatureEquality : sig
  val check : S.Context.t -> S.Signature.t * S.Signature.t * S.Level.t -> unit
end = struct
  module L = S.Level
  module C = S.Context
  module S = S.Signature

  let check gamma = function
  (* eql_sig_refl *)
  | (s, s', l) when s = s' -> Signature.check gamma (s, l)

  (* eql_sig_cons *)
  | (S.Cons (si, s), S.Cons (si', s'), L.Max (l, l')) ->
    begin
      assert (not (S.contains_signature_item si s));
      SignatureItemEquality.check gamma (si, si', l);
      SignatureEquality.check (C.cons_signature_item gamma si) (s, s', l')
    end

  (* eql_sig_trans *)
  | _ -> failwith "not implemented"
end

(* Γ |- T = T' : K *)
and ModuleTypeEquality : sig
  val check : S.Context.t -> S.ModuleType.t * S.ModuleType.t * S.ModuleKind.t -> unit
end = struct
  module L = S.Level
  module MT = S.ModuleType
  module MK = S.ModuleKind
  module C = S.Context

  let check gamma = function
  (* eql_mtyp_signature *)
  | (MT.Sig s, MT.Sig s', MK.Level (L.Succ l)) ->
    SignatureEquality.check gamma (s, s', l)

  (* eql_mtyp_functor *)
  | (MT.Functor(m, (x1i, t1), t1'), MT.Functor(m', (x2i, t2), t2'), MK.Level L.Max(l, l'))
    when m = m' ->
      begin
        ModuleTypeEquality.check gamma (t1, t2, MK.Level l);
        (* todo: infer k *)
        (* ModuleTypeEquality.check (C.cons_module_type gamma x2i (t2, k) (t1', t2', MK.Level l'); *)
      end

  (* eql_mtyp_singleton *)
  | (t1, t2, k) -> ModuleType.check gamma (t1, MK.Singleton (t2, k))

  (* eql_mtyp_trans *)
  | _ -> failwith "not implemented"
end

(* Γ |- DIv = DIv' : SIv *)
(* todo: i guess this ^ is a typo in the paper (SI, not SIv) *)
and DefinitionValueItemEquality : sig
  val check : S.Context.t -> S.DefinitionValueItem.t * S.DefinitionValueItem.t * S.SignatureValueItem.t -> unit
end = struct
  module DVI = S.DefinitionValueItem
  module SVI = S.SignatureValueItem
  module C = S.Context

  let check gamma = function
  (* eql_ditem_type *)
  | (DVI.Type (ai, (as_, kv)), DVI.Type (ai', (as_', kv')), SVI.Type (ai'', (as_'', kv'')))
    when ai = ai' && ai' = ai'' && as_ = as_' && as_' = as_'' && kv = kv'' ->
      KindEquality.check (C.cons_type_params gamma as_) (kv, kv')

  (* eql_ditem_modtype *)
  | (DVI.ModuleType (ai, kv), DVI.ModuleType (ai', kv'), SVI.ModuleType (ai'', kv''))
    when ai = ai' && ai' = ai'' && kv = kv'' ->
      ModuleKindEquality.check gamma (kv, kv')

  (* eql_ditem_module *)
  | (DVI.Module (xi, ev), DVI.Module (xi', ev'), SVI.Module (xi'', (t, k)))
    when xi = xi' && xi' = xi'' ->
      ModuleExpressionValueEquality.check gamma (ev, ev', t)

  | _ -> failwith "type error"
end


(* Γ |- Dv = Dv' : Sv *)
and DefinitionValueEquality : sig
  val check : S.Context.t -> S.DefinitionValue.t * S.DefinitionValue.t * S.SignatureValue.t -> unit
end = struct
  module DV = S.DefinitionValue
  module DVI = S.DefinitionValueItem
  module SV = S.SignatureValue
  module C = S.Context

  let check gamma = function
  (* eql_def_refl *)
  | (dv, dv', sv) when dv = dv' -> DefinitionValue.check gamma (dv, sv)

  (* eql_def_cons *)
  | (DV.Cons(dvi1, dv1), DV.Cons(dvi2, dv2), SV.Cons(svi, sv)) ->
    begin
      DefinitionValueItemEquality.check gamma (dvi1, dvi2, svi);
      DefinitionValueEquality.check (C.cons_signature_value_item gamma svi) (dv1, dv2, sv)
    end

  (* eql_def_trans *)
  | _ -> failwith "not implemented"
end

(* Γ |- Dv projects X at Ev : T *)
and Projection : sig
  val check : S.Context.t -> S.DefinitionValue.t * S.modvar * S.ModuleExpressionValue.t * S.ModuleType.t -> unit
end = struct
  module DV = S.DefinitionValue
  module DVI = S.DefinitionValueItem

  let check gamma = function
  (* proj_mod_match_module *)
  | (DV.Cons(DVI.Module((x, i), mev), dv), x', mev', mt)
    when x = x' && mev = mev' ->
      begin
        (* infer sv *)
        (* DefinitionValue.check gamma (dv, sv) *)
        failwith "not implemented"
      end
  | _ -> failwith "not implemented"
end

(* Γ |- Ev = Ev' : T *)
and ModuleExpressionValueEquality : sig
  val check : S.Context.t -> S.ModuleExpressionValue.t * S.ModuleExpressionValue.t * S.ModuleType.t -> unit
end = struct
  let check gamma = function
  | _ -> failwith "not implemented"
end