(* PA5c *)
open Printf
open Str

type cool_program = cool_class list
and loc = string
and id = loc*string
and cool_type = id
and cool_class = id * cool_type option * cool_feature list
and cool_feature = 
  (* option to have none for the attribute exp *)
  | Attribute of id * cool_type * (exp option)
  | Method of id * cool_formal list * cool_type * exp
and cool_formal = id * cool_type
and exp = loc * ekind 

and ekind = 
    | New of string (* new point*)
    | Dispatch of exp option  * string option * string * (exp list) (* self.foo(a1, a2, ... an) *)
    | String of string (* "hello" *)
    | Variable of string (* x *)
    | Integer of Int32.t (* 1 *)
    | Plus of exp * exp (* e1 + e2 *)
    | Minus of exp * exp (* e1 - e2 *)
    | Times of exp * exp (* e1 * e2 *)
    | Divide of exp * exp (* e1 / e2 *)
    | LessThan of exp * exp (* e1 < e2 *)
    | LessThanEq of exp * exp (* e1 <= e2 *)
    | Equal of exp * exp (* e1 = e2 *)
    | Not of exp (* not e *)
    | Negate of exp (* -e *)
    | IsVoid of exp (* isvoid e *)
    | If of exp * exp * exp (* if e1 then e2 else e3 *)
    | While of exp * exp (* while e1 loop e2 pool *)
    | Block of exp list (* {e1; e2; ... en} *)
    | Let of (let_binding list * exp)(* let x : T <- e1 in e2 *)
    | Case of exp * ((string * string * exp) list) (* case e of x1 : T1 => e1; x2 : T2 => e2; ...; xn : Tn => en esac *)
    | Assign of string * exp (* x <- e *)
    | Internal of string (* empty exp for the method body of internal methods*)
    | TrueConst of bool (* true *)
    | FalseConst of bool (* false *)

and let_binding = 
  | LetBindingInit of (id * id * exp)
  | LetBindingNoInit of (id * id)

type cool_address = int

type cool_value = 
  | Cool_Int of Int32.t
  | Cool_Bool of bool
  | Cool_String of string
  | Cool_Object of string * ((string * cool_address) list) (*X(a1=L1)*)
  | Address of cool_address
  | Void
(* Enviroment: Maps variable Names -> Cool Addresses *)
type enviroment = (string * cool_address) list
(* Store: Maps Cool  Addresses  -> Cool values  *)
type store = (cool_address * cool_value) list
(* Class Map  *)
(* Maps class names to a list of attributes and their types *)
type class_map = (string * (string * (exp option)) list) list
(* Implementation Map 
  Maps ("Class Name", "Method name") to 
  the method formal parameter names to the method body *)
type impl_map = (string * (string * (string list * exp)) list ) list
(* Parent Map Maps class names to their parent class names *)
type parent_map = (string * string) list
(* Global Variables *)
let class_map = ref ([]: class_map)
let impl_map = ref ([] : impl_map)
let parent_map = ref ([] : parent_map)

(* Evaluation *)
let replace_all str pattern replacement =
  let rec replace_rec str =
    try
      let index = String.index str pattern.[0] in
      if String.sub str index (String.length pattern) = pattern then
        let prefix = String.sub str 0 index in
        let suffix = String.sub str (index + (String.length pattern)) (String.length str - index - (String.length pattern)) in
        prefix ^ replacement ^ (replace_rec suffix)
      else
        str
    with Not_found -> str
  in
  replace_rec str

let exit_error eloc str = 
  if eloc <> "" then
    printf "ERROR: %s: Exception: " eloc;
  printf "%s\n" str;
  exit 1

let rec find_first_non_digit input len index =
  if index < len then
    match input.[index] with
    | '0' .. '9' -> find_first_non_digit input len (index + 1)
    | _ -> index
  else
    index

let rec exp_to_str (_,e) = 
  match e with
  | New(x) -> sprintf "New(%s)" x
  | Dispatch(Some(e0), Some(t), fname, args) -> sprintf "Dispatch(%s, %s, %s, [%s])" (exp_to_str e0) t fname (String.concat "; " (List.map exp_to_str args))
  | Dispatch(Some(e0), None, fname, args) -> sprintf "Dispatch(%s, %s, [%s])" (exp_to_str e0) fname (String.concat "; " (List.map exp_to_str args))
  | Dispatch(None, None, fname, args) -> sprintf "Dispatch(NONE, %s, [%s])" fname (String.concat "; " (List.map exp_to_str args))
  | Variable(x) -> sprintf "Var(%s) \n" x
  | Integer(i) -> Int32.to_string i
  | Plus(e1, e2) -> sprintf "%s + %s" (exp_to_str e1) (exp_to_str e2)
  | Minus(e1, e2) -> sprintf "%s - %s" (exp_to_str e1) (exp_to_str e2)
  | Times(e1, e2) -> sprintf "%s * %s" (exp_to_str e1) (exp_to_str e2)
  | Divide(e1, e2) -> sprintf "%s / %s" (exp_to_str e1) (exp_to_str e2)
  | LessThan(e1, e2) -> sprintf "%s < %s" (exp_to_str e1) (exp_to_str e2)
  | LessThanEq(e1, e2) -> sprintf "%s <= %s" (exp_to_str e1) (exp_to_str e2)
  | Equal(e1, e2) -> sprintf "%s = %s" (exp_to_str e1) (exp_to_str e2)
  | Not(e) -> sprintf "not %s" (exp_to_str e)
  | Negate(e) -> sprintf "-%s" (exp_to_str e)
  | IsVoid(e) -> sprintf "isvoid %s" (exp_to_str e)
  | If(e1, e2, e3) -> sprintf "if %s then %s else %s" (exp_to_str e1) (exp_to_str e2) (exp_to_str e3)
  | While(e1, e2) -> sprintf "while %s loop %s pool" (exp_to_str e1) (exp_to_str e2)
  | Block(el) -> sprintf "Block{%s}" (String.concat "; " (List.map exp_to_str el))
  | Let(bindings, e1) -> sprintf "let bindings: [%s] , Exp %s" (String.concat "; " (List.map let_binding_to_str bindings)) (exp_to_str e1)
  | Case(exp, cl) -> sprintf "case %s of %s esac" (exp_to_str exp) (String.concat "; " (List.map (fun (x, t, e) -> sprintf "%s : %s => %s" x t (exp_to_str e)) cl))
  | Assign(x, e) -> sprintf "Assign(%s <- %s)" x (exp_to_str e)
  | Internal(extra_info) -> sprintf "Internal(%s)" extra_info
  | String(s) -> sprintf "String(%s)" s
  | TrueConst(b) -> sprintf "TrueConst(%b)" b
  | FalseConst(b) -> sprintf "FalseConst(%b)" b
  | _ -> failwith "Not implemented"

and let_binding_to_str (b) =
  match b with
  | LetBindingInit((x, t, e)) -> sprintf "LetBindingInit(%s : %s <- %s)" (snd x) (snd t) (exp_to_str e)
  | LetBindingNoInit((x, t)) -> sprintf "LetBindingNoInit(%s : %s)" (snd x) (snd t)

let value_to_str v = 
  match v with
  | Cool_Int(i) -> sprintf "%ld" i
  | Cool_Bool(b) -> sprintf "%b" b
  | Cool_String(str) -> 
    sprintf "replace all %s\n" str;
    sprintf "%s" (replace_all str "\\n" "\n")
  | Cool_Object(cname, attrs) -> 
      let attr_str = List.fold_left (fun acc (aname, aaddr) -> 
        sprintf "%s, %s=%d, " acc aname aaddr) "" attrs in 
        sprintf "%s(%s)" cname attr_str
  | Void -> sprintf "Void" 
  | _ -> failwith "Not implemented"

let enviroment_to_str env = ""
  (* let binding_str = List.fold_left (fun acc (aname, addr) -> 
    sprintf "%s, %s=%d" acc aname addr) "" (List.sort compare env) in
    sprintf "[%s]" binding_str *)

let store_to_str store = 
  let binding_str = List.fold_left (fun acc (addr, value) -> 
    sprintf "%s, %d -> %s" acc addr (value_to_str value)) "" store in
    sprintf "[%s]" binding_str
    (* Debugging and Tracing*)
let do_debug = false 

let debug fmt = 
  let handle result_string = 
    (* fix this line *)
    if do_debug then printf "%s" result_string
  in 
  ksprintf handle fmt

let indent_count = ref 0
let debug_indent() = 
  debug "%s" (String.make (!indent_count) ' ')

let depth_count = ref 0

let inc_depth() = 
  depth_count := !depth_count + 1

let dec_depth() =
  depth_count := !depth_count - 1

let new_location_counter = ref 1000
let new_loc() = 
  (* debug "new_loc\n"; *)
  incr new_location_counter;
  !new_location_counter

  (* Evaluation *)
let is_subtype c t =
  let rec is_subtype_helper c t = 
    (* debug "is_subtype_helper: %s %s\n" c t; *)
    if c = t then true 
    else
      if c = "Object" then false
      else 
        match List.assoc c !parent_map with
        | p -> is_subtype_helper p t
        | _ -> false
  in
  is_subtype_helper c t

let compare_subtype t1 t2 =
  if is_subtype t1 t2 then -1
  else if is_subtype t2 t1 then 1
  else 0

let rec eval (so : cool_value )
       (s : store)
       (env : enviroment)
       (exp : exp) 
       : 
       (cool_value * 
       store) =
  indent_count := !indent_count + 2;
  (* debug_indent(); debug "eval: %s\n" (exp_to_str exp);
  debug_indent(); debug "self: %s\n" (value_to_str so);
  debug_indent(); debug "stor: %s\n" (store_to_str s);
  debug_indent(); debug "env: %s\n\n" (enviroment_to_str env); *)
  let eloc, exp = exp in
  let (new_value, new_store) = match exp with
  (* need to add self type *)
  | New(class_name) -> 
    inc_depth();
    if !depth_count > 1000 then
      exit_error eloc "stack overflow";

    debug_indent(); debug "New: %s\n" class_name;
    let class_name  = if class_name = "SELF_TYPE" then
      match so with 
      | Cool_Object(cname, _) -> cname
      | Cool_Int(_) -> "Int"
      | Cool_Bool(_) -> "Bool"
      | Cool_String(_) -> "String"
      | Void -> exit_error eloc "new on void"
      | _ -> failwith "Type error"
    else 
      class_name
    in 
    begin match class_name with
    | "Int" -> Cool_Int(0l), s
    | "Bool" -> Cool_Bool(false), s
    | "String" -> Cool_String(""), s
    | _ -> 
        let attrs_and_inits = List.assoc class_name !class_map in
        let new_attr_loc = List.map (fun (aname, ainit) -> 
          new_loc()
        ) attrs_and_inits in
        let attr_names = List.map (fun (aname, ainit) -> aname) attrs_and_inits in
        let attrs_and_locs = List.combine attr_names new_attr_loc in
        let v1 = Cool_Object(class_name, attrs_and_locs) in
        let final_store = List.fold_left (fun acc_store (aname, ainit) -> 
            let loc = List.assoc aname attrs_and_locs in
            let acc_store = (loc, Void) :: acc_store in
            match ainit with
            | None -> 
              acc_store
            | Some(ainit) -> 
                let _, acc_store = eval v1 acc_store attrs_and_locs (eloc, Assign(aname, ainit)) in
                acc_store
        ) s attrs_and_inits in
        dec_depth();
        v1, final_store
    end
  | Variable(vname) ->
    (match vname with 
    | "self" -> so, s
    | _ ->
      (* debug_indent(); debug "Variable: %s\n" vname; *)
      (* check if the location is known from env  *)
        let location = 
          if List.mem_assoc vname env then
            List.assoc vname env
          else
            (* List.assoc vname (begin match so with
            | Cool_Object(_, attrs) -> attrs
            | _ -> failwith "Type error" *)
            failwith "Variable not found in enviroment"
            (* end) *)
          in 
        (* debug_indent(); debug "Location: %d\n" location; *)
        let final_value = List.assoc location s in
        (* debug_indent(); debug "Final Value: %s\n" (value_to_str final_value); *)
        final_value, s
    )
  | Integer(i) -> Cool_Int(i), s
  | Plus(e1, e2) -> 
    let (v1, s1) = eval so s env e1 in 
    let (v2, s2) = eval so s1 env e2 in 
    (match (v1, v2) with 
    | (Cool_Int(i1), Cool_Int(i2)) -> (Cool_Int(Int32.add i1 i2), s2)
    | _ -> failwith "add Type error")
  | Minus(e1, e2) ->
    let (v1, s1) = eval so s env e1 in
    let (v2, s2) = eval so s1 env e2 in
    (match (v1, v2) with
      | (Cool_Int(i1), Cool_Int(i2)) -> (Cool_Int(Int32.sub i1 i2), s2)
      | _ -> failwith "Minus Type error")
  | Times(e1, e2) ->
    let (v1, s1) = eval so s env e1 in
    let (v2, s2) = eval so s1 env e2 in
    (match (v1, v2) with
    | (Cool_Int(i1), Cool_Int(i2)) -> (Cool_Int(Int32.mul i1 i2), s2)
    | _ -> failwith "Times Type error")
  | Divide(e1, e2) ->
    let (v1, s1) = eval so s env e1 in
    let (v2, s2) = eval so s1 env e2 in
    (match (v1, v2) with
    | (Cool_Int(i1), Cool_Int(0l)) -> exit_error eloc "division by zero";
    | (Cool_Int(i1), Cool_Int(i2)) -> (Cool_Int(Int32.div i1 i2), s2)
    | _ -> failwith "DIVIDE Type error")
  | LessThan(e1, e2) ->
    let (v1, s1) = eval so s env e1 in
    let (v2, s2) = eval so s1 env e2 in
    (match (v1, v2) with
    | (Cool_Int(i1), Cool_Int(i2)) -> (Cool_Bool(i1 < i2), s2)
    | (Cool_Bool(b1), Cool_Bool(b2)) -> (Cool_Bool(b1 < b2), s2)
    | (Cool_String(str1), Cool_String(str2)) -> (Cool_Bool(str1 < str2), s2)
    | (Cool_Object(cname1, _), Cool_Object(cname2, _)) -> (Cool_Bool(cname1 < cname2), s2)
    | (Void, Void) -> (Cool_Bool(false), s2)
    | _ -> failwith "LT Type error")
  | LessThanEq(e1, e2) ->
    let (v1, s1) = eval so s env e1 in
    let (v2, s2) = eval so s1 env e2 in
    (match (v1, v2) with
    | (Cool_Int(i1), Cool_Int(i2)) -> (Cool_Bool(i1 <= i2), s2)
    | (Cool_Bool(b1), Cool_Bool(b2)) -> (Cool_Bool(b1 <= b2), s2)
    | (Cool_String(str1), Cool_String(str2)) -> (Cool_Bool(str1 <= str2), s2)
    | (Cool_Object(cname1, _), Cool_Object(cname2, _)) -> (Cool_Bool(cname1 <= cname2), s2)
    | (Void, Void) -> (Cool_Bool(true), s2)
    | _ -> failwith "LT EQ Type error")
  | Equal(e1, e2) ->
    let (v1, s1) = eval so s env e1 in
    let (v2, s2) = eval so s1 env e2 in
    (match (v1, v2) with
    | (Cool_Int(i1), Cool_Int(i2)) -> (Cool_Bool(i1 = i2), s2)
    | (Cool_Bool(b1), Cool_Bool(b2)) -> (Cool_Bool(b1 = b2), s2)
    | (Cool_String(str1), Cool_String(str2)) -> (Cool_Bool(str1 = str2), s2)
    | (Void, Void) -> (Cool_Bool(true), s2)
    | (Cool_Object(_, _), Cool_Object(_, _)) -> (Cool_Bool(v1 == v2), s2)
    | _ -> (Cool_Bool(false), s2))
  | Not(e) ->
    let (v, s1) = eval so s env e in 
    (match v with 
    | Cool_Bool(b) -> (Cool_Bool(not b), s1)
    | Cool_Object(_, _) -> (Cool_Bool(false), s1)
    | Void -> (Cool_Bool(true), s1)
    | _ -> failwith "NOT Type error")
  | Negate(e) ->
    let (v, s1) = eval so s env e in 
    (match v with 
    | Cool_Int(i) -> Cool_Int(Int32.neg i), s1
    | _ -> failwith "NEGATE Type error")
  | TrueConst(b) -> Cool_Bool(true), s
  | FalseConst(b) -> Cool_Bool(false), s
  | IsVoid(e) -> 
    let (v, s1) = eval so s env e in 
    (match v with 
    | Cool_Bool(b) -> (Cool_Bool(false), s1)
    | Cool_Object(_, _) -> (Cool_Bool(false), s1)
    | Void -> (Cool_Bool(true), s1)
    | _ -> failwith "Is Void Type error")
  | If(e1, e2, e3) ->
    let (v1, s1) = eval so s env e1 in 
    (match v1 with 
      | Cool_Bool(true) -> eval so s1 env e2
      | Cool_Bool(false) -> eval so s1 env e3
      | _ -> failwith "IF Type error")
  | While(e1, e2) ->
    let (v1, s1) = eval so s env e1 in 
    (match v1 with 
      | Cool_Bool(true) -> 
        (* debug_indent(); debug "WHILE TRUE: %s\n" (exp_to_str e1); *)
        let (v2, s2) = eval so s1 env e2 in 
        eval so s2 env (eloc, While(e1, e2))
      | Cool_Bool(false) -> (Void, s1)
      | _ -> failwith "WHILE Type error")
  | Block(el) ->
    let v = so in
    let (v, s) = List.fold_left (fun (acc_val, acc_store) e -> 
      eval v acc_store env e) (v, s) el in 
    (v, s)
  | Let(bindings, e1) ->
      let new_store = s in
      let new_env, new_store = List.fold_left (fun (acc_env, acc_store) b -> 
        match b with 
        | LetBindingInit((x, t, e)) -> 
          let (v, s1) = eval so acc_store acc_env e in 
          let new_loc = new_loc() in 
          let new_env = (snd x, new_loc) :: acc_env in 
          let new_store = (new_loc, v) :: s1 in 
          new_env, new_store
        | LetBindingNoInit((x, t)) -> 
          let new_loc = new_loc() in
          let new_env = (snd x, new_loc) :: acc_env in 
          let v = 
            begin match snd t with
            | "Int" -> Cool_Int(0l)
            | "Bool" -> Cool_Bool(false)
            | "String" -> Cool_String("")
            | "Object" -> Cool_Object(snd t, [])
            | _ -> Void;
            end in
          let new_store = (new_loc, v) :: new_store in 
          new_env, new_store
      ) (env, new_store) bindings in
      eval so new_store new_env e1 
  | Case(e1, branches) ->
    let v, s1 = eval so s env e1 in
    let c = begin match v with 
      | Cool_Object(cname, _) -> cname
      | Cool_String(_) -> "String"
      | Cool_Int(_) -> "Int"
      | Cool_Bool(_) -> "Bool"
      | Void -> exit_error eloc "case on void"
      | _ -> failwith "Type error"
    end in
    (* filter out branhces that c is not a subtype of *)
    let filtered_branches = List.filter (fun (_, t, _) -> is_subtype c t) branches in
    let sorted_branches = List.sort (fun (_, t1, _) (_, t2, _) ->
      let cmp = compare_subtype t1 t2 in
      if cmp = 0 then exit_error eloc "duplicate branches in case"
      else cmp
    ) filtered_branches in 
    debug_indent(); debug "sorted_branches: %s\n" (String.concat "; " (List.map (fun (x, t, e) -> sprintf "%s : %s => %s" x t (exp_to_str e)) sorted_branches));
    let rec evaluate_branches = function
      | [] -> exit_error eloc "case without matching branch:"
      | (x, t, e) :: rest ->
          if is_subtype c t then
            let new_loc = new_loc() in
            let new_env = (x, new_loc) :: env in
            let new_store = (new_loc, v) :: s1 in
            let result_v, result_s = eval so new_store new_env e in
            result_v, result_s
          else
            evaluate_branches rest
    in
    evaluate_branches sorted_branches
  | Assign(vname, rhs) ->
      let v1, s1 = eval so s env rhs in 
      let l1 = List.assoc vname env in
      let s2 = List.map (fun (loc, value) ->
        if loc = l1 then (l1, v1)  (* Update the value at location l1 *)
        else (loc, value)           (* Leave other locations unchanged *)
      ) s1 in
      v1, s2
  | Dispatch(_,_, fname, args) ->
      inc_depth();
      if !depth_count > 1000 then
        exit_error eloc "stack overflow";
      let arg_vals, s_n = List.fold_left (fun (acc_vals, acc_state) arg ->
        let val_i, new_state = eval so acc_state env arg in
        (val_i :: acc_vals, new_state)  (* Accumulate results and update state *)
      ) ([], s) args in  (* Start with empty accumulator for values and initial state s0 *) 
      let arg_vals = List.rev arg_vals in
      let v0, s_n1,cname = begin match exp with
      | Dispatch(Some(e0),None, _, _) -> let v2, s2 = eval so s_n env e0 in
        if v2 <> Void then 
          v2,s2, ""
        else 
          exit_error eloc "dispatch on void"; 
      | Dispatch(Some(e0), Some(t), _, _) -> 
      let v2, s2 = eval so s_n env e0 in
        if v2 <> Void then 
          v2,s2,t
        else 
          exit_error eloc "dispatch on void"; 
      | _ -> so, s_n, ""
        end
      in
      if v0 <> Void then 
        let class_name = 
          if String.length cname > 0 then 
            cname
          else 
            begin match v0 with
            | Cool_Object(c_name, _) -> c_name
            | Cool_String(_) -> "String"
            | Cool_Int(_) -> "Int"
            | Cool_Bool(_) -> "Bool"
            | Void -> exit_error eloc "dispatch on void"
            | _ -> failwith "Type error in dispatch"
            end
          in
        let attrs = match v0 with
          | Cool_Object(_, attrs) ->  attrs
          | _ -> []
        in
        let class_methods = List.assoc class_name !impl_map in
        let formals, body = List.assoc fname class_methods in    
        let new_arg_locs = List.map (fun _ -> new_loc ()) args in 
        let new_env = List.combine formals new_arg_locs @ attrs in
        let store_updates = List.fold_left2 (fun acc_store loc vn -> (loc, vn) :: acc_store) [] new_arg_locs arg_vals in
        let s_n2 = store_updates @ s_n1 in
        let v1, s_n3 = eval v0 s_n2 new_env body in
        dec_depth(); 
        v1, s_n3
      else 
        exit_error eloc "dispatch on void"
  | String(str) -> Cool_String(str), s
  | Internal(fname) -> 
    begin match fname with 
    | "Object.abort" -> exit_error "" "abort"
    | "Object.type_name" -> 
      let v = begin match so with 
      | Cool_Object(cname, _) -> Cool_String(cname)
      | Cool_String(_) -> Cool_String("String")
      | Cool_Int(_) -> Cool_String("Int")
      | Cool_Bool(_) -> Cool_String("Bool")
      | Void -> Cool_String("Void")
      | _ -> failwith "Type error"
      end in
      v, s
    | "Object.copy" ->
      let v, s = begin match so with 
      | Cool_Object(cname, attrs) -> 
        let new_attrs = List.map (fun (aname, aaddr) -> 
          let new_loc = new_loc() in
          (aname, new_loc)
        ) attrs in
        let store_updates = List.map (fun (aname, aaddr) -> 
          let v = List.assoc aaddr s in
          (aaddr, v)
        ) new_attrs in
        let s2 = store_updates @ s in
        Cool_Object(cname, new_attrs), s2
      | Cool_String(str) -> Cool_String(str), s
      | Cool_Int(i) -> Cool_Int(i), s
      | Cool_Bool(b) -> Cool_Bool(b), s
      | Void -> Void, s
      | _ -> failwith "Type error"
        end in 
      v, s
    | "IO.out_string" ->
      (* get the x from enviroment *)
      let x = List.assoc "x" env in
      let v = List.assoc x s in
      begin match v with
      | Cool_String(str) -> 
        let out_string = replace_all str "\\n" "\n" in
        let out_string = replace_all out_string "\t" "\\t" in
        output_string stdout out_string; so, s
      | _ -> failwith "Type error"
      end
    | "IO.in_string" -> 
      let str = read_line() in
      Cool_String(str), s
    | "IO.out_int" ->
      let x = List.assoc "x" env in 
      let v = List.assoc x s in
      begin match v with
      | Cool_Int(i) -> output_string stdout (Int32.to_string i); so, s
      | _ -> failwith "Type error"
      end
    | "IO.in_int" ->
      let input = read_line () in
      (* remove whitespace *)
      let input = String.trim input in
      let len = String.length input in
      let first_non_digit_index = find_first_non_digit input len 0 in
      begin try
        let number_part = String.sub input 0 first_non_digit_index in
        let number = int_of_string number_part in
        let i_32 = Int32.of_int number in
        (Cool_Int(i_32), s)
      with
      | Failure _ -> Cool_Int(0l), s
    end 
    | "String.length" ->
      begin match so with
      | Cool_String(str) -> Cool_Int(Int32.of_int (String.length str)), s
      | _ -> failwith "Type error"
      end
    | "String.concat" ->
      let str = List.assoc "s" env in
      let v2 = List.assoc str s in
      let v1 = so in 
      begin match (v1, v2) with
      | (Cool_String(str1), Cool_String(str2)) -> Cool_String(str1 ^ str2), s
      | _ -> failwith "Type error"
      end
    | "String.substr" ->
      let i = List.assoc "i" env in
      let l = List.assoc "l" env in
      let Cool_Int(i) = List.assoc i s in
      let Cool_Int(l) = List.assoc l s in
      let Cool_String(str) = so in
      if i < 0l || l < 0l || Int32.add i l > Int32.of_int (String.length str) then
        exit_error "0" "String.substr out of range"
      else 
        Cool_String(String.sub str (Int32.to_int i) (Int32.to_int l)), s 
    | _ -> failwith "Internal method not implemented"
    end 
  | _ -> failwith "Not implemented in eval"
  in
  indent_count := !indent_count - 2;
  new_value, new_store

let main() = begin
  let fname = Sys.argv.(1) in
  let ic = open_in fname in
  
  let read() =
    (* increment i *)
    let line = input_line ic in 
    line 
  in
  let rec range k =
    if k <= 0 then []
    else k :: range (k-1)
  in 
  let read_list worker = 
    let str = read() in
    let n = int_of_string str in
    let lst = range n in
    List.map (fun _ -> worker()) lst
  in

  (* write a method to read the classmap in the cool-type file *)
  let rec read_cool_program () =
    let my_class_map = read_class_map() in
    let my_impl_map = read_impl_map() in
    let my_parent_map = read_parent_map() in
    let my_program = read_annotated_ast() in
    (my_class_map, my_impl_map, my_parent_map, my_program)
  and read_class_map() : class_map = 
    let start_map = read() in
    let str = read() in
    let n = int_of_string str in
    let lst = range n in
    List.map (fun _ -> 
      let cname = read() in
      let str = read() in
      let n = int_of_string str in
      let lst = range n in
      let attrs = List.map (fun _ -> 
        let ainit = read() in
        let aname = read() in
        (* (do I need to add these to enviroment ? /  ) *)
        let atype = read() in
       (* if ainit == no initializer  *) 
        let exp = if ainit = "no_initializer" then None else Some(read_exp()) in
        (aname, exp)
      ) lst in
      (cname, attrs)
    ) lst
  and read_impl_map () =
    let start_map = read() in
    let str = read() in
    let n = int_of_string str in
    let lst = range n in
    List.map (fun _ -> 
      let cname = read() in
      let methods = read() in
      let num_methods = int_of_string methods in
      let m_lst = range num_methods in
      let methods_list = List.map (fun _ -> 
        let mname = read() in
        let formals = read_list (fun () -> 
          let fname = read() in
          fname
        ) in 
        let inherits = read() in
        let body = read_exp() in
        (mname, (formals, body))
      ) m_lst in
      (cname, methods_list)
    ) lst
  and read_parent_map() = 
    let parent_map = read() in
    let str = read() in
    let n = int_of_string str in
    let lst = range n in
    List.map (fun _ -> 
      let cname = read() in
      let pname = read() in
      (cname, pname)
    ) lst
  and read_annotated_ast () = 
    read_list read_cool_class
  and read_id() = 
    let loc = read() in
    let name = read() in
    (loc, name)
  and read_cool_class() =
    let cname =  read_id() in 
    match read() with
    | "inherits" -> 
      let pname = read_id() in 
      let features = read_list read_cool_feature in
      (cname, Some(pname), features)
    | "no_inherits" -> 
      let features = read_list read_cool_feature in
      (cname, None, features)
  and read_cool_feature() =
    match read() with
    | "attribute_init" -> 
      let aname = read_id() in
      let atype = read_id() in
      let ainit = read_exp() in
      Attribute(aname, atype, Some(ainit))
    | "attribute_no_init" -> 
      let aname = read_id() in
      let atype = read_id() in
      Attribute(aname, atype, None)
    | "method" -> 
      let mname = read_id() in
      let formals = read_list read_cool_formal in
      let mtype = read_id() in
      let body = read_exp() in
      Method(mname, formals, mtype, body)
    | _ -> failwith "cannot happen"
  and read_cool_formal() =
    let fname = read_id() in
    let ftype = read_id() in
    (fname, ftype)
  and read_exp() : exp =
      let eloc = read() in
      let etype = read() in
      let ename = read() in
      let ekind = match ename with
      | "internal" -> 
        let extra_info = read() in
        Internal(extra_info)
      | "string" ->
        let s = read() in
        String(s)
      | "new" -> 
        let eloc2 = read() in
        let cname = read() in 
        New(cname)
      | "dynamic_dispatch" ->
        let e0 = read_exp() in
        let eloc2 = read() in
        let fname = read() in
        let args = read_list read_exp in
        Dispatch(Some(e0), None, fname, args)
      | "static_dispatch" ->
        let e0 = read_exp() in
        let eloc2 = read() in
        let cname = read() in
        let eloc3 = read() in
        let mname = read() in
        let args = read_list read_exp in
        Dispatch(Some(e0), Some(cname) ,mname, args)
      | "self_dispatch" ->
        let mloc = read() in
        let mname =read() in
        let args = read_list read_exp in
        Dispatch(None, None, mname, args)
      | "variable" ->
        let vname = read() in
        Variable(vname)
      | "integer" ->
        let i = Int32.of_string (read()) in
        Integer(i)
      | "plus" ->
        let e1 = read_exp() in
        let e2 = read_exp() in
        Plus(e1, e2)
      | "minus" ->
        let e1 = read_exp() in
        let e2 = read_exp() in
        Minus(e1, e2)
      | "times" ->
        let e1 = read_exp() in
        let e2 = read_exp() in
        Times(e1, e2)
      | "divide" ->
        let e1 = read_exp() in
        let e2 = read_exp() in
        Divide(e1, e2)
      | "lt" ->
        let e1 = read_exp() in
        let e2 = read_exp() in
        LessThan(e1, e2)
      | "le" ->
        let e1 = read_exp() in
        let e2 = read_exp() in
        LessThanEq(e1, e2)
      | "eq" ->
        let e1 = read_exp() in
        let e2 = read_exp() in
        Equal(e1, e2)
      | "not" ->
        let e = read_exp() in
        Not(e)
      | "negate" ->
        let e = read_exp() in
        Negate(e)
      | "isvoid" ->
        let e = read_exp() in
        IsVoid(e)
      | "if" ->
        let e1 = read_exp() in
        let e2 = read_exp() in
        let e3 = read_exp() in
        If(e1, e2, e3)
      | "while" ->
        let e1 = read_exp() in
        let e2 = read_exp() in
        While(e1, e2)
      | "block" ->
        let el = read_list read_exp in
        Block(el)
      | "let" ->
        let bindings = read_list read_let_binding in
        let e = read_exp() in
        Let(bindings, e)
      | "case" ->
        let e = read_exp() in
        let branches = read_list read_case_branch in
        Case(e, branches)
      | "assign" ->
        let eloc2 = read() in
        let vname = read() in
        let e = read_exp() in
        Assign(vname, e)
      | "identifier" -> 
        let eloc = read() in
        let vname = read() in
        Variable(vname)
      | "self" -> 
        let vname = read() in
        Variable(vname)
      | "true" -> 
        (* let vname = read() in *)
        TrueConst(true)
      | "false" ->
        FalseConst(false)
      | _ -> 
        sprintf "BAD ename: %s\n" ename;  
        failwith "cannot happen"
      in
     (eloc, ekind)
  and read_let_binding() =
    let binding_str = read() in
    if binding_str = "let_binding_no_init" then 
      begin 
        let var = read_id() in 
        let etype = read_id() in
        LetBindingNoInit(var, etype) 
      end 
    else 
      begin
        let var = read_id() in 
        let etype = read_id() in
        let exp = read_exp() in
        LetBindingInit(var, etype, exp) 
      end 
  
  and read_case_branch() =
      let x = read() in
      let var = read() in
      let eloc2 = read() in
      let case_type = read() in
      let e = read_exp() in
      (var, case_type, e)
  in
  let my_class_map, my_impl_map, my_parent_map, my_program = read_cool_program() in
  class_map := my_class_map;
  impl_map := my_impl_map;
  parent_map := my_parent_map;
  debug "finished reading\n";
  let main_class = List.find (fun ((_,cname), _, _) -> cname = "Main") my_program in
  let main_id, main_parent, main_features = main_class in
  (* Find the main method *)
  let main_method = List.find ( fun feature ->
    match feature with 
    |Method((_,"main"), _, _, _) -> true
    |_ -> false
    ) main_features in
  let main_body = match main_method with
  | Method(_, _, _, body) -> body
  | _ -> failwith "cannot happen"
  in
  let env_ref = ref [] in
  let store_ref = ref [] in
  (* reverse featurelist *)
  let feature = List.rev main_features in
  List.iter (fun feature ->
    let so = Cool_Object("Main", !env_ref) in
    match feature with
    | Attribute((_, attr_name), _, Some(attr_expr)) ->
        let attr_value, new_store = eval so !store_ref !env_ref attr_expr in
        let new_loc = new_loc() in
        env_ref := (attr_name, new_loc) :: !env_ref;
        store_ref := (new_loc, attr_value) :: new_store;
    | Attribute((_, attr_name), _, None) -> 
        let new_loc = new_loc() in
        env_ref := (attr_name, new_loc) :: !env_ref;
        store_ref := (new_loc, Void) :: !store_ref;
    | _ -> ()
  ) main_features;
  
  (* Update the environment and store references *)
  let updated_env = !env_ref in
  let updated_store = !store_ref in
  let so = Cool_Object("Main", updated_env) in
  let (main_value : cool_value), _ = eval so updated_store updated_env main_body in
  let (main_value_str : string)  = value_to_str main_value in
  debug "main_value: %s\n" main_value_str;
end ;;
main() ;;
