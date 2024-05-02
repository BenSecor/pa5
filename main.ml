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
    | Dispatch of exp option  * string * (exp list) (* self.foo(a1, a2, ... an) *)
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


(* read in annotated ast cool file *)


(* Goal is to boil down expressions into values (and update the store) *)

(* Enviroment: Maps variable Names -> Cool Addresses *)
(* Use an association List*)

type enviroment = (string * cool_address) list

(* Store: Maps Cool  Addresses  -> Cool values  *)
type store = (cool_address * cool_value) list


(* Class Map  *)
(* Maps class names to a list of attributes and their types *)
(* FIX ME:  CHECK WHAT THE FULL VERSION SHOULD BE*)
type class_map = (string * (string * (exp option)) list) list

(* Implementation Map 
  Maps ("Class Name", "Method name") to 
  the method formal parameter names to the method body
  FIX ME :  CHECK WHAT THE FULL VERSION SHOULD BE*)
type impl_map = (string * (string * (string list * exp)) list ) list
  
  (* Parent Map 
    Maps class names to their parent class names *)
type parent_map = (string * string) list
  
  (* Global Variables *)
let class_map = ref ([]: class_map)
let impl_map = ref ([] : impl_map)
let parent_map = ref ([] : parent_map)

(* Evaluation *)
(* Convert expressions to strings for debugging *)
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

let rec exp_to_str (_,e) = 
  match e with
  | New(x) -> sprintf "New(%s)" x
  | Dispatch(Some(e0), fname, args) -> sprintf "Dispatch(%s, %s, [%s])" (exp_to_str e0) fname (String.concat "; " (List.map exp_to_str args))
  | Dispatch(None, fname, args) -> sprintf "Dispatch(NONE, %s, [%s])" fname (String.concat "; " (List.map exp_to_str args))
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
  | IsVoid(e) -> sprintf "isvoid %s" (exp_to_str e)
  | If(e1, e2, e3) -> sprintf "if %s then %s else %s" (exp_to_str e1) (exp_to_str e2) (exp_to_str e3)
  | While(e1, e2) -> sprintf "while %s loop %s pool" (exp_to_str e1) (exp_to_str e2)
  | Block(el) -> sprintf "Block{%s}" (String.concat "; " (List.map exp_to_str el))
  | Let(bindings, e1) -> sprintf "let bindings: [%s] , Exp %s" (String.concat "; " (List.map let_binding_to_str bindings)) (exp_to_str e1)
  | Case(exp, cl) -> sprintf "case %s of %s esac" (exp_to_str exp) (String.concat "; " (List.map (fun (x, t, e) -> sprintf "%s : %s => %s" x t (exp_to_str e)) cl))
  | Assign(x, e) -> sprintf "Assign(%s <- %s)" x (exp_to_str e)
  | Internal(extra_info) -> sprintf "Internal(%s)" extra_info
  | String(s) -> sprintf "String(%s)" s

and let_binding_to_str (b) =
  match b with
  | LetBindingInit((x, t, e)) -> sprintf "LetBindingInit(%s : %s <- %s)" (snd x) (snd t) (exp_to_str e)
  | LetBindingNoInit((x, t)) -> sprintf "LetBindingNoInit(%s : %s)" (snd x) (snd t)

let value_to_str v = 
  match v with
  | Cool_Int(i) -> sprintf "%ld" i
  | Cool_Bool(b) -> sprintf "Bool%b" b
  | Cool_String(s) -> sprintf "%s" (replace_all s "\\n" "\n")
  | Cool_Object(cname, attrs) -> 
      let attr_str = List.fold_left (fun acc (aname, aaddr) -> 
        sprintf "%s, %s=%d, " acc aname aaddr) "" attrs in 
        sprintf "%s(%s)" cname attr_str
  | Void -> sprintf "Void" 

let enviroment_to_str env = 
  let binding_str = List.fold_left (fun acc (aname, addr) -> 
    sprintf "%s, %s=%d" acc aname addr) "" (List.sort compare env) in
    sprintf "[%s]" binding_str

let store_to_str store =
  let binding_str = List.fold_left (fun acc (addr, value) -> 
    sprintf "%s, %d -> %s" acc addr (value_to_str value)) "" store in
    sprintf "[%s]" binding_str

    (* Debugging and Tracing*)
let do_debug = true


let debug fmt = 
  let handle result_string = 
    (* fix this line *)
    if do_debug then printf "%s" result_string
  in 
  ksprintf handle fmt

let indent_count = ref 0
let debug_indent() = 
  debug "%s" (String.make (!indent_count) ' ')

let new_location_counter = ref 1000
let new_loc() = 
  debug "new_loc\n";
  incr new_location_counter;
  !new_location_counter

  (* Evaluation *)
let is_subtype c t =
  let rec is_subtype_helper c t = 
    debug "is_subtype_helper: %s %s\n" c t;
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
  debug "compare_subtype: %s %s\n" t1 t2;
  if is_subtype t1 t2 then -1
  else if is_subtype t2 t1 then 1
  else 0

(* Evaluation *)
(* Evaluate an expression in a given enviroment and store *)
(* Returns a new value and a new store *)
(* FIX ME:  ADD SELF TYPE *)

(* Evaluation *)
(* Evaluate an expression in a given enviroment and store *)
(* Returns a new value and a new store *)
(* FIX ME:  ADD SELF TYPE *)

let rec eval (so : cool_value )
       (s : store)
       (env : enviroment)
       (exp : exp) 
       : 
       (cool_value * 
       store) =
  indent_count := !indent_count + 2;
  debug_indent(); debug "eval: %s\n" (exp_to_str exp);
  debug_indent(); debug "self: %s\n" (value_to_str so);
  debug_indent(); debug "stor: %s\n" (store_to_str s);
  debug_indent(); debug "env: %s\n\n" (enviroment_to_str env);
  let eloc, exp = exp in
  let (new_value, new_store) = match exp with
  (* need to add self type *)
  | New(class_name) -> 
    debug "new class_name: %s\n" class_name;
    begin
    match class_name with
    | "Int" -> Cool_Int(0l), s
    | "Bool" -> Cool_Bool(false), s
    | "String" -> Cool_String(""), s
    | _ -> 
        let attrs_and_inits = List.assoc class_name !class_map in
        let new_attr_loc = List.map (fun (aname, ainit) -> 
            new_loc()
        ) attrs_and_inits in
        let store_updates = List.map (fun new_loc -> 
          (new_loc, Cool_Int(0l)) 
        ) new_attr_loc in 
        let s2 = s @ store_updates in
        let attr_names = List.map (fun (aname, ainit) -> aname) attrs_and_inits in
        let ainits = List.map (fun (aname, ainit) -> ainit) attrs_and_inits in
        let attrs_and_locs = List.combine attr_names new_attr_loc in
        let v1 = Cool_Object(class_name, attrs_and_locs) in
        let final_store = List.fold_left (fun acc_store (aname, ainit) -> 
            debug "aname: %s\n" aname;
            match ainit with
            | None -> 
              debug "ainit with NONE: %s\n" aname;
              acc_store 
            | Some(ainit) -> 
                let _, updated_store = eval v1 acc_store attrs_and_locs (eloc, Assign(aname, ainit)) in
                updated_store
        ) s2 attrs_and_inits in
        v1, final_store
    end
  | Variable(vname) ->
    (match vname with 
    | "self" -> so, s
    | _ ->
      let location = List.assoc vname env in
      let final_value = List.assoc location s in
      final_value, s)
  | Integer(i) -> Cool_Int(i), s
  | Plus(e1, e2) -> 
  let (v1, s1) = eval so s env e1 in 
  let (v2, s2) = eval so s1 env e2 in 
  (match (v1, v2) with 
  | (Cool_Int(i1), Cool_Int(i2)) -> (Cool_Int(Int32.add i1 i2), s2)
  | _ -> failwith "Type error")
  | Minus(e1, e2) ->
  let (v1, s1) = eval so s env e1 in
  let (v2, s2) = eval so s1 env e2 in
  (match (v1, v2) with
  | (Cool_Int(i1), Cool_Int(i2)) -> (Cool_Int(Int32.sub i1 i2), s2)
  | _ -> failwith "Type error")
  | Times(e1, e2) ->
  let (v1, s1) = eval so s env e1 in
  let (v2, s2) = eval so s1 env e2 in
  (match (v1, v2) with
  | (Cool_Int(i1), Cool_Int(i2)) -> (Cool_Int(Int32.mul i1 i2), s2)
  | _ -> failwith "Type error")
  | Divide(e1, e2) ->
  let (v1, s1) = eval so s env e1 in
  let (v2, s2) = eval so s1 env e2 in
  (match (v1, v2) with
  | (Cool_Int(i1), Cool_Int(0l)) -> failwith "ERROR: %s:Exception: Division by Zero" eloc;
  | (Cool_Int(i1), Cool_Int(i2)) -> (Cool_Int(Int32.div i1 i2), s2)
  | _ -> failwith "Type error")
  | LessThan(e1, e2) ->
  let (v1, s1) = eval so s env e1 in
  let (v2, s2) = eval so s1 env e2 in
  (match (v1, v2) with
  | (Cool_Int(i1), Cool_Int(i2)) -> (Cool_Bool(i1 < i2), s2)
  | _ -> failwith "Type error")
  | LessThanEq(e1, e2) ->
    let (v1, s1) = eval so s env e1 in
    let (v2, s2) = eval so s1 env e2 in
    (match (v1, v2) with
    | (Cool_Int(i1), Cool_Int(i2)) -> (Cool_Bool(i1 <= i2), s2)
    | _ -> failwith "Type error")
  | Equal(e1, e2) ->
  let (v1, s1) = eval so s env e1 in
  let (v2, s2) = eval so s1 env e2 in
  (match (v1, v2) with
  | (Cool_Int(i1), Cool_Int(i2)) -> (Cool_Bool(i1 = i2), s2)
  | _ -> failwith "Type error")
  | Not(e) ->
  let (v, s1) = eval so s env e in 
  (match v with 
  | Cool_Bool(b) -> (Cool_Bool(not b), s1)
  | Cool_Object(_, _) -> (Cool_Bool(false), s1)
  | Void -> (Cool_Bool(true), s1)
  | _ -> failwith "Type error")
  | IsVoid(e) -> 
  let (v, s1) = eval so s env e in 
  (match v with 
  | Cool_Bool(b) -> (Cool_Bool(not b), s1)
  | Cool_Object(_, _) -> (Cool_Bool(false), s1)
  | Void -> (Cool_Bool(true), s1)
  | _ -> failwith "Type error")

  | If(e1, e2, e3) ->
  let (v1, s1) = eval so s env e1 in 
  (match v1 with 
  | Cool_Bool(true) -> eval so s1 env e2
  | Cool_Bool(false) -> eval so s1 env e3
  | _ -> failwith "Type error")
  | While(e1, e2) ->
  let (v1, s1) = eval so s env e1 in 
  (match v1 with 
    | Cool_Bool(true) -> 
      let (v2, s2) = eval so s1 env e2 in 
      eval so s2 env (eloc, While(e1, e2))
    | Cool_Bool(false) -> (Void, s1)
    | _ -> failwith "Type error")
  | Block(el) ->
  let (v, s1) = List.fold_left (fun (acc_val, acc_store) e -> 
    eval so acc_store env e) (Void, s) el in 
    (v, s1)
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
          debug "NO INIT x: %s\n" (snd x);
          debug "NO INIT TYPE: %s\n" (snd t);
          (* let (v, s1) = eval so acc_store acc_env New(t) in  *)
          let new_loc = new_loc() in
          let new_env = (snd x, new_loc) :: acc_env in 
          let v = 
            begin match snd t with
            | "Int" -> Cool_Int(0l)
            | "Bool" -> Cool_Bool(false)
            | "String" -> Cool_String("")
            | _ -> failwith "Type error";
            end in
          let new_store = (new_loc, v) :: new_store in 
          new_env, new_store
      ) (env, new_store) bindings in
      eval so new_store new_env e1 
  | Case(e1, branches) ->
    debug "case e1: %s\n" (exp_to_str e1);
    let v, s = eval so s env e1 in
    let c = begin match v with 
      | Cool_Object(cname, _) -> cname
      | Cool_String(_) -> "String"
      | Cool_Int(_) -> "Int"
      | Cool_Bool(_) -> "Bool"
      | Void -> "Void"
      | _ -> failwith "Type error"
    end in
    (* Sort branches based on subtype relationship *)
    let sorted_branches = List.sort (fun (_, t1, _) (_, t2, _) ->
      compare_subtype t1 t2
    ) branches in 
    let rec evaluate_branches = function
      | [] -> failwith "Error: No matching branch found in case expression."
      | (x, t, e) :: rest ->
          if is_subtype c t then
            let new_loc = new_loc() in
            let new_env = (x, new_loc) :: env in
            let new_store = (new_loc, v) :: s in
            let result_v, result_s = eval so new_store new_env e in
            result_v, result_s
          else
            evaluate_branches rest
    in
    evaluate_branches sorted_branches
  | Assign(vname, rhs) ->
    debug "assign: %s\n" vname;
    let v1, s2 = eval so s env rhs in 
    let l1 = List.assoc vname env in
    let s3 = (l1, v1) :: s2 in
    v1, s3
  | Dispatch(_, fname, args) -> 
    let current_store = ref s in
    let v0 = begin match exp with
      | Dispatch(Some(e0), _, _) ->let v, s = eval so !current_store env e0 in current_store := s ; v
      | _ -> so
    end in
    let arg_vals = List.map (fun arg_exp -> 
      let arg_val, arg_store = eval so !current_store env arg_exp in
      current_store := arg_store;
      arg_val
    ) args in
    debug "v0 = %s\n" (value_to_str v0);
    (begin match v0 with 
      | Cool_Object(cname, attrs_andlocs) ->
        (* FIX check to make sure it is in there if its not you have a pa5 bug *)
          debug "fname = %s " fname;
        (begin match fname with 
          | "out_string" ->
            output_string stdout (value_to_str (List.hd arg_vals));
            so, s
          | "out_int" ->
            output_string stdout (value_to_str (List.hd arg_vals));
            so, s
          | "in_string" -> 
            let str = read_line() in
            Cool_String(str), s
          | "in_int" -> 
            let i = Int32.of_string (read_line()) in
            Cool_Int(i), s
          | "length" -> (begin match List.hd arg_vals with
            | Cool_String(str) -> Cool_Int(Int32.of_int (String.length str)), s
            | _ -> failwith "str.len error" end)
          | "concat" -> (begin match arg_vals with
            | [Cool_String(s1); Cool_String(s2)] -> Cool_String(s1 ^ s2), s
            | _ -> failwith "concat error" end)
          | "substr" -> (begin match arg_vals with
            | [Cool_String(s1); Cool_Int(i); Cool_Int(j)] -> Cool_String(String.sub s1 (Int32.to_int i) (Int32.to_int j)), s
            | _ -> failwith "substring err" end)
          | "abort" -> failwith "abort %d" eloc;
          | "type_name" -> Cool_String(cname), s
          | "copy" -> 
            let new_store_updates = List.map (fun (aname, aaddr) -> 
              let v = List.assoc aaddr !current_store in
              (aaddr, v)
            ) attrs_andlocs in
            let new_store = !current_store @ new_store_updates in
            Cool_Object(cname, attrs_andlocs), new_store
          | _ ->  
            let class_methods = List.assoc cname !impl_map in
            let formals, body  = List.assoc fname class_methods in
            let new_arg_locs = List.map (fun arg_val -> 
              new_loc()
            ) args in 
            let store_updates = List.combine new_arg_locs arg_vals in
            let s_n3 = store_updates @s in
            eval v0 s_n3 attrs_andlocs body
            end )
      | _ -> 
        debug "fname f out %s\n" fname; 
        (begin match fname with 
          | "out_string" ->
            output_string stdout (value_to_str (List.hd arg_vals));
            so, s
          | "out_int" ->
            output_string stdout (value_to_str (List.hd arg_vals));
            so, s
          | "in_string" -> 
            let str = read_line() in
            Cool_String(str), s
          | "in_int" -> 
            let i = Int32.of_string (read_line()) in
            Cool_Int(i), s
          | "length" -> (begin match List.hd arg_vals with
            | Cool_String(str) -> Cool_Int(Int32.of_int (String.length str)), s
            | _ -> failwith "str.len error" end)
          | "concat" -> (begin match arg_vals with
            | [Cool_String(s1); Cool_String(s2)] -> Cool_String(s1 ^ s2), s
            | _ -> failwith "concat error" end)
          | "substr" -> (begin match arg_vals with
            | [Cool_String(s1); Cool_Int(i); Cool_Int(j)] -> Cool_String(String.sub s1 (Int32.to_int i) (Int32.to_int j)), s
            | _ -> failwith "substring err" end)
          | "abort" -> failwith "ABORT"
          | "type_name" -> Cool_String(fname), s
          (* CAN YOU HAVE COPY IN SELF DISPATCH ??*)
          (* | "copy" -> 
            let new_attrs_andlocs = List.map (fun (aname, aaddr) -> 
              (aname, new_loc())
            ) attrs_andlocs in
            let new_store_updates = List.map (fun (aname, aaddr) -> 
              let v = List.assoc aaddr !current_store in
              (new_loc(), v)
            ) new_attrs_andlocs in
            let new_store = !current_store @ new_store_updates in
            Cool_Object(cname, new_attrs_andlocs), new_store *)
          | _ -> failwith "Not implemented %s" fname
        end)
      end)
  | String(str) -> Cool_String(str), s
  | _ -> failwith "Not implemented"
  in
  debug_indent(); debug "result: %s\n" (value_to_str new_value);
  debug_indent(); debug "rets: %s\n\n" (store_to_str new_store);
  indent_count := !indent_count - 2; 
  new_value, new_store
let main() = begin
  let fname = Sys.argv.(1) in
  let ic = open_in fname in
  
  let read() =
    (* increment i *)
    let line = input_line ic in 
    debug "read: %s\n" line;
    line 
  in
  let rec range k =
    if k <= 0 then []
    else k :: range (k-1)
  in 
  let read_list worker = 
    let str = read() in
    debug "read_list: %s\n" str;
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
    debug "read_class_map: %s\n" start_map;
    let str = read() in
    debug "num classes: %s\n" str;
    let n = int_of_string str in
    let lst = range n in
    List.map (fun _ -> 
      let cname = read() in
      debug "CLASS: %s\n" cname;
      let str = read() in
      let n = int_of_string str in
      let lst = range n in
      let attrs = List.map (fun _ -> 
        let ainit = read() in
        let aname = read() in
        (* (do I need to add these to enviroment ? /  ) *)
        debug "aname: %s\n" aname;
        let atype = read() in
       (* if ainit == no initializer  *) 
        let exp = if ainit = "no_initializer" then None else Some(read_exp()) in
        (aname, exp)
      ) lst in
      (cname, attrs)
    ) lst
  and read_impl_map () =
    let start_map = read() in
    debug "read_impl_map: %s\n" start_map;
    let str = read() in
    debug "num_classes: %s\n" str;
    let n = int_of_string str in
    let lst = range n in
    List.map (fun _ -> 
      let cname = read() in
      debug "cname: %s\n" cname;
      let methods = read() in
      debug "methods: %s\n" methods;
      let num_methods = int_of_string methods in
      let m_lst = range num_methods in
      let methods_list = List.map (fun _ -> 
        let mname = read() in
        debug "mname: %s\n" mname;
        let formals = read_list (fun () -> 
          let fname = read() in
          debug "read_impl_map: %s\n" fname;
          fname
        ) in 
        let inherits = read() in
        debug "inherits: %s\n" inherits;
        let body = read_exp() in
        (mname, (formals, body))
      ) m_lst in
      (cname, methods_list)
    ) lst
  and read_parent_map() = 
    let parent_map = read() in
    debug "read_parent_map: %s\n" parent_map;
    let str = read() in
    let n = int_of_string str in
    let lst = range n in
    List.map (fun _ -> 
      let cname = read() in
      let pname = read() in
      (cname, pname)
    ) lst
  and read_annotated_ast () = 
    debug "read_annotated_ast\n";
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
      debug "eloc: %s\n" eloc;
      let etype = read() in
      debug "etype: %s\n" etype;
      let ename = read() in
      debug "ename: %s\n" ename;
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
        debug "NEW cname: %s\n" cname;
        New(cname)
      | "dynamic_dispatch" ->
        let e0 = read_exp() in
        let eloc2 = read() in
        let fname = read() in
        debug "DISPATCH fname: %s\n" fname;
        let args = read_list read_exp in
        Dispatch(Some(e0), fname, args)
      | "static_dispatch" ->
        let e0 = read_exp() in
        debug "STATIC DISPATCH e0: %s\n" (exp_to_str e0);
        let eloc2 = read() in
        debug "STATIC DISPATCH eloc2: %s\n" eloc2;
        let eloc3 = read() in
        debug "STATIC DISPATCH eloc3: %s\n" eloc3;
        let cname = read() in
        debug "STATIC DISPATCH cname: %s\n" cname;
        let mname = read() in
        debug "STATIC DISPATCH mname: %s\n" mname;
        let args = read_list read_exp in
        Dispatch(Some(e0), mname, args)
      | "self_dispatch" ->
        let mloc = read() in
        let mname = read() in
        let args = read_list read_exp in
        Dispatch(None,mname, args)
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
      | "negate" ->
        let e = read_exp() in
        Not(e)
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
        let vname = read() in
        let eloc2 = read() in
        let e = read_exp() in
        Assign(vname, e)
      | "identifier" -> 
        let eloc = read() in
        debug "ID eloc: %s\n" eloc;
        let vname = read() in
        debug "ID vname: %s\n" vname;
        Variable(vname)
      | "self" -> 
        let vname = read() in
        debug "SELF vname: %s\n" vname;
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
      debug "CASE var: %s\n" var;
      let eloc2 = read() in
      let case_type = read() in
      debug "BRANCH type: %s\n" case_type;
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
  let main_method = List.find ( fun feature ->
    match feature with 
    |Method((_,"main"), _, _, _) -> true
    |_ -> false
    ) main_features in
  let main_body = match main_method with
  | Method(_, _, _, body) -> body
  | _ -> failwith "cannot happen"
  in
  (* need to evaluate attributes if they have expressions before evaluating the body of the main method *)
  let env_ref = ref [] in
  let store_ref = ref [] in
  List.iter (fun feature ->
    match feature with
    | Attribute((_, attr_name), _, Some(attr_expr)) ->
        let attr_value, new_store = eval Void !store_ref !env_ref attr_expr in
        let new_loc = new_loc() in
        env_ref := (attr_name, new_loc) :: !env_ref;
        store_ref := (new_loc, attr_value) :: !store_ref;
    | Attribute((_, _), _, None) -> () (* No expression to evaluate *)
    | _ -> ()
  ) main_features;
  
  (* Update the environment and store references *)
  let updated_env = !env_ref in
  let updated_store = !store_ref in
  let (main_value : cool_value), _ = eval Void updated_store updated_env main_body in
  let (main_value_str : string)  = value_to_str main_value in
  debug "main_value: %s\n" main_value_str;
end ;;
main() ;;
