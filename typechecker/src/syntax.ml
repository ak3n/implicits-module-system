type termvar = string
type typevar = string
type modvar = string
type modtypevar = string
type stamp = int

module Level = struct
  type t =
  | Zero
  | Succ of t
  | Max of t * t
end

module ParameterMode = struct
  type t =
  | Ord
  | Impl
  | Inf
end

module rec Kind : sig
  type t =
  | Singleton of Type.t * t
  | Other
end = struct
  type t =
  | Singleton of Type.t * t
  | Other
end

and TypeParams : sig
  type t =
  | Epsilon
  | Cons of ((typevar * stamp) * Kind.t) * t
end = struct
  type t =
  | Epsilon
  | Cons of ((typevar * stamp) * Kind.t) * t
end

and ModuleType : sig
  type t =
  | Var of modtypevar * stamp
  | Proj of ModuleExpressionValue.t * modtypevar
  | Sig of Signature.t
  | Functor of ParameterMode.t * ((modvar * stamp) * t) * t
  | Singleton of ModuleExpressionValue.t * t
end = struct
  type t =
  | Var of modtypevar * stamp
  | Proj of ModuleExpressionValue.t * modtypevar
  | Sig of Signature.t
  | Functor of ParameterMode.t * ((modvar * stamp) * t) * t
  | Singleton of ModuleExpressionValue.t * t
end

and ModuleExpressionValue : sig
  type t =
  | Var of modvar * stamp
  | Proj of t * modvar
  | Struct of Definition.t
  | Functor of ParameterMode.t * ((modvar * stamp) * ModuleType.t) * t
  | Apply of t * t
end = struct
  type t =
  | Var of modvar * stamp
  | Proj of t * modvar
  | Struct of Definition.t
  | Functor of ParameterMode.t * ((modvar * stamp) * ModuleType.t) * t
  | Apply of t * t
end

and ModuleKind : sig
  type t =
  | Level of Level.t
  | Singleton of ModuleType.t * t
end = struct
  type t =
  | Level of Level.t
  | Singleton of ModuleType.t * t
end

and Expression : sig
  type t =
  | Var of termvar * stamp
  | Proj of ModuleExpressionValue.t * termvar
  | Other
end = struct
  type t =
  | Var of termvar * stamp
  | Proj of ModuleExpressionValue.t * termvar
  | Other
end

and ModuleExpression : sig
  type t =
  | Var of modvar * stamp
  | Proj of ModuleExpressionValue.t * modvar
  | Struct of Definition.t
  | Functor of ParameterMode.t * ((modvar * stamp) * ModuleType.t) * t
  | App of t * ParameterMode.t * ModuleExpressionValue.t
  | Ascription of t * ModuleType.t
end = struct
  type t =
  | Var of modvar * stamp
  | Proj of ModuleExpressionValue.t * modvar
  | Struct of Definition.t
  | Functor of ParameterMode.t * ((modvar * stamp) * ModuleType.t) * t
  | App of t * ParameterMode.t * ModuleExpressionValue.t
  | Ascription of t * ModuleType.t
end

and DefinitionItem : sig
  type t =
  | Type of (typevar * stamp) * (TypeParams.t * Kind.t)
  | Val of (termvar * stamp) * Expression.t
  | ModuleType of (modtypevar * stamp) * ModuleKind.t
  | Module of (modvar * stamp) * ModuleExpression.t
end = struct
  type t =
  | Type of (typevar * stamp) * (TypeParams.t * Kind.t)
  | Val of (termvar * stamp) * Expression.t
  | ModuleType of (modtypevar * stamp) * ModuleKind.t
  | Module of (modvar * stamp) * ModuleExpression.t
end

and Definition : sig
  type t =
  | Cons of DefinitionItem.t * t
  | End
end = struct
  type t =
  | Cons of DefinitionItem.t * t
  | End
end

and SignatureItem : sig
  type t =
  | Type of (typevar * stamp) * (TypeParams.t * Kind.t)
  | Val of (termvar * stamp) * Type.t
  | ModuleType of (modtypevar * stamp) * ModuleKind.t
  | Module of (modvar * stamp) * (ModuleType.t * ModuleKind.t)
end = struct
  type t =
  | Type of (typevar * stamp) * (TypeParams.t * Kind.t)
  | Val of (termvar * stamp) * Type.t
  | ModuleType of (modtypevar * stamp) * ModuleKind.t
  | Module of (modvar * stamp) * (ModuleType.t * ModuleKind.t)
  (* an extra module kind (not mentioned in pdf) ^ *)
end

and Signature : sig
  type t =
  | Cons of SignatureItem.t * t
  | End

  val contains_signature_item : SignatureItem.t -> Signature.t -> bool
end = struct
  type t =
  | Cons of SignatureItem.t * t
  | End

  let rec contains_signature_item s_item = function
  | Cons (s_item', s) -> s_item = s_item' || contains_signature_item s_item' s
  | End -> false
end

and Type : sig
  type t =
  | Var of TypeArgs.t * (typevar * stamp)
  | Proj of TypeArgs.t * ModuleExpressionValue.t * typevar
  | Other
end = struct
  type t =
  | Var of TypeArgs.t * (typevar * stamp)
  | Proj of TypeArgs.t * ModuleExpressionValue.t * typevar
  | Other
end

and TypeArgs : sig
  type t =
  | Epsilon
  | Cons of Type.t * t
end = struct
  type t =
  | Epsilon
  | Cons of Type.t * t
end

module SignatureValueItem = struct
  type t =
  | Type of (typevar * stamp) * (TypeParams.t * Kind.t)
  | ModuleType of (modtypevar * stamp) * ModuleKind.t
  | Module of (modvar * stamp) * (ModuleType.t * ModuleKind.t)
  (* an extra module kind (not mentioned in pdf) ^ *)
end

module SignatureValue = struct
  type t =
  | Cons of SignatureValueItem.t * t
  | End
end

module DefinitionValueItem = struct
  type t =
  | Type of (typevar * stamp) * (TypeParams.t * Kind.t)
  | ModuleType of (modtypevar * stamp) * ModuleKind.t
  | Module of (modvar * stamp) * ModuleExpressionValue.t
end

module DefinitionValue = struct
  type t =
  | Cons of DefinitionValueItem.t * t
  | End
end

module ModuleKindValue = struct
  type t = Singleton of ModuleType.t * ModuleKind.t
end

module KindValue = struct
  type t = Singleton of Type.t * Kind.t
end

module Substitution = struct
  type t =
  | Type of (typevar * stamp) * TypeParams.t * Kind.t
  | ModType of (modtypevar * stamp) * ModuleType.t
  | Module of (modvar * stamp) * ModuleExpressionValue.t
end

module Context = struct
  module Item = struct
    type t =
    | Type of (typevar * stamp) * (TypeParams.t * Kind.t)
    | Val of (termvar * stamp) * Type.t
    | ModType of (modtypevar * stamp) * ModuleKind.t
    | Mod of (modvar * stamp) * (ModuleType.t * ModuleKind.t)
    (* an extra module kind (not mentioned in pdf) ^ *)
  end

  type t = Item.t list

  let contains item gamma = List.mem item gamma
  let rec contains_stamp stamp = function
  | [] -> false
  | x :: g ->
    begin
      let check = function
      | Item.Type ((_, i), _) -> stamp = i
      | Item.Val ((_, i), _) -> stamp = i
      | Item.ModType ((_, i), _) -> stamp = i
      | Item.Mod ((_, i), _) -> stamp = i
      in
      check x || contains_stamp stamp g
    end

  let find_type (typevar, stamp) gamma =
    let pred = function
      | Item.Type ((x, i), _) -> typevar = x && stamp = i
      | _ -> false
    in
    List.find_opt pred gamma

  let find_type' typevar gamma =
    let pred = function
      | Item.Type ((x, _), _) -> typevar = x
      | _ -> false
    in
    List.find_opt pred gamma

  (* Xi : T \in Γ *)
  let rec contains_modvar_modtype ((modvar, stamp), modtype) = function
  | [] -> false
  | x :: g ->
    begin
      let check = function
      | Item.Mod ((x', i'), (t', _)) -> modvar = x' && stamp = i' && t' = modtype
      | _ -> false
      in
      check x || contains_modvar_modtype ((modvar, stamp), modtype) g
    end

  let cons_module_type gamma xi (t, k) = Item.Mod (xi, (t, k)) :: gamma

  let rec cons_type_params gamma = function
  | TypeParams.Epsilon -> gamma
  | TypeParams.Cons (((a, i), k), params) ->
    (Item.Type ((a, i), (TypeParams.Epsilon, k))) :: cons_type_params gamma params

  let cons_signature_item gamma = function
  | SignatureItem.Type (ai, (as_, k)) -> Item.Type (ai, (as_, k)) :: gamma
  | SignatureItem.Val (xi, t) -> Item.Val (xi, t) :: gamma
  | SignatureItem.ModuleType (ai, k) -> Item.ModType (ai, k) :: gamma
  | SignatureItem.Module (xi, (t, k)) -> Item.Mod (xi, (t, k)) :: gamma

  let cons_signature_value_item gamma = function
  | SignatureValueItem.Type (ai, (as_, k)) -> Item.Type (ai, (as_, k)) :: gamma
  | SignatureValueItem.ModuleType (ai, k) -> Item.ModType (ai, k) :: gamma
  | SignatureValueItem.Module (xi, (t, k)) -> Item.Mod (xi, (t, k)) :: gamma
end