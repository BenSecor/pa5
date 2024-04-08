(* PA5c *)
open Printf

type exp = 
    | New of string (* new point*)
    | Dispatch of exp * string * (exp list) (* self.foo(a1, a2, ... an) *)
    | Variable of string (* x *)
    | Integer of Int32.t (* 1 *)
    | Plus of exp * exp (* e1 + e2 *)
    | Minus of exp * exp (* e1 - e2 *)
    | Times of exp * exp (* e1 * e2 *)
    | Divide of exp * exp (* e1 / e2 *)
    | LessThan of exp * exp (* e1 < e2 *)
    | Equal of exp * exp (* e1 = e2 *)
    | Not of exp (* not e *)
    | IsVoid of exp (* isvoid e *)
    | If of exp * exp * exp (* if e1 then e2 else e3 *)
    | While of exp * exp (* while e1 loop e2 pool *)
    | Block of exp list (* {e1; e2; ... en} *)
    | Let of string * string * exp * exp (* let x : T <- e1 in e2 *)
    | Case of exp * ((string * string * exp) list) (* case e of x1 : T1 => e1; x2 : T2 => e2; ...; xn : Tn => en esac *)
    | Assign of string * exp (* x <- e *)

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

let new_location_counter = ref 1000
let new_loc() = 
  incr new_location_counter;
  !new_location_counter

(* Class Map  *)
(* Maps class names to a list of attributes and their types *)
(* FIX ME:  CHECK WHAT THE FULL VERSION SHOULD BE*)

(* Class Map  *)
(* Maps class names to a list of attributes and their types *)
(* FIX ME:  CHECK WHAT THE FULL VERSION SHOULD BE*)
type class_map = (string * ((string * exp) list)) list

(* Implementation Map 
  Maps ("Class Name", "Method name") to 
  the method formal parameter names to the method body
  FIX ME :  CHECK WHAT THE FULL VERSION SHOULD BE*)
type impl_map = ((string * string) * (string list * exp)) list

let class_map : class_map = 
  [("Main" , ["x", Integer(5l) ; 
              "y", Plus(Variable("x"), Integer(2l))])]
let impl_map : impl_map = 
  [("Main", "main"), ([], 
                      (Plus(Variable("x"), (Variable("y"))))) ]
  

(* Evaluation *)

(* Convert expressions to strings for debugging *)

let rec exp_to_str e = 
  match e with
  | New(x) -> sprintf "New(%s)" x
  | Dispatch(e0, fname, args) -> sprintf "Dispatch(%s, %s, [%s])" (exp_to_str e0) fname (String.concat "; " (List.map exp_to_str args))
  | Variable(x) -> sprintf "Var(%s) \n" x
  | Integer(i) -> Int32.to_string i
  | Plus(e1, e2) -> sprintf "%s + %s" (exp_to_str e1) (exp_to_str e2)
  | Minus(e1, e2) -> sprintf "%s - %s" (exp_to_str e1) (exp_to_str e2)
  | Times(e1, e2) -> sprintf "%s * %s" (exp_to_str e1) (exp_to_str e2)
  | Divide(e1, e2) -> sprintf "%s / %s" (exp_to_str e1) (exp_to_str e2)
  | LessThan(e1, e2) -> sprintf "%s < %s" (exp_to_str e1) (exp_to_str e2)
  | Equal(e1, e2) -> sprintf "%s = %s" (exp_to_str e1) (exp_to_str e2)
  | Not(e) -> sprintf "not %s" (exp_to_str e)
  | IsVoid(e) -> sprintf "isvoid %s" (exp_to_str e)
  | If(e1, e2, e3) -> sprintf "if %s then %s else %s" (exp_to_str e1) (exp_to_str e2) (exp_to_str e3)
  | While(e1, e2) -> sprintf "while %s loop %s pool" (exp_to_str e1) (exp_to_str e2)
  | Block(el) -> sprintf "Block{%s}" (String.concat "; " (List.map exp_to_str el))
  | Let(x, t, e1, e2) -> sprintf "let %s : %s <- %s in %s" x t (exp_to_str e1) (exp_to_str e2)
  | Case(e, cl) -> sprintf "case %s of %s esac" (exp_to_str e) (String.concat "; " (List.map (fun (x, t, e) -> sprintf "%s : %s => %s" x t (exp_to_str e)) cl))
  | Assign(x, e) -> sprintf "Assign(%s <- %s)" x (exp_to_str e)

let value_to_str v = 
  match v with
  | Cool_Int(i) -> sprintf "%ld" i
  | Cool_Bool(b) -> sprintf "Bool%b" b
  | Cool_String(s) -> sprintf "%s" s
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


(* Evaluation *)

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
  let (new_value, new_store) = match exp with
  (* need to add self type *)
  | New(class_name) -> 
  let attrs_and_inits = List.assoc class_name class_map in
  let new_attr_loc = List.map (fun (aname, ainit) -> 
    new_loc()
  ) attrs_and_inits in
  let attr_names = List.map (fun (aname, ainit) -> aname) attrs_and_inits in
  let attrs_and_locs = List.combine attr_names new_attr_loc in
  let v1 = Cool_Object(class_name, List.combine attr_names new_attr_loc) in
  (* Default Values based on the class_names, cool manual*)
  let store_updates = List.map (fun new_loc -> 
      (new_loc, Cool_Int(0l)) 
  ) new_attr_loc in 
  let s2 = s @ store_updates in
  let final_store = List.fold_left (fun acc_store (aname, ainit) -> 
    let _, updated_store = eval v1 acc_store attrs_and_locs (Assign(aname, ainit)) in
    updated_store
  ) s2 attrs_and_inits in
  v1, final_store
  | Variable(vname) ->
  printf "vname: %s\n" vname;
  let l = List.assoc vname env in
  let final_value = List.assoc l s in
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
  | (Cool_Int(i1), Cool_Int(i2)) -> (Cool_Int(Int32.div i1 i2), s2)
  | _ -> failwith "Type error")
  | LessThan(e1, e2) ->
  let (v1, s1) = eval so s env e1 in
  let (v2, s2) = eval so s1 env e2 in
  (match (v1, v2) with
  | (Cool_Int(i1), Cool_Int(i2)) -> (Cool_Bool(i1 < i2), s2)
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
    eval so s2 env (While(e1, e2))
  | Cool_Bool(false) -> (Void, s1)
  | _ -> failwith "Type error")
  | Block(el) ->
  let (v, s1) = List.fold_left (fun (acc_val, acc_store) e -> 
    eval so acc_store env e) (Void, s) el in 
    (v, s1)
  | Let(x, t, e1, e2) ->
  let (v1, s1) = eval so s env e1 in 
  let new_addr = List.length s1 in 
  let new_env = (x, new_addr) :: env in 
  let new_store = s1 @ [(new_addr, v1)] in 
  eval so new_store new_env e2
  (* | Case(e, cl) ->
  let (v, s1) = eval so s env e in 
  (match v with 
  | Cool_Object(cname, attrs) -> 
    let (x, t, e) = List.assoc cname cl in 
    let new_addr = List.length s1 in 
    let new_env = (x, new_addr) :: so in 
    let new_store = s1 @ [(new_addr, v)] in 
    eval new_env new_store e
  | _ -> failwith "Type error") *)
  | Assign(vname, rhs) ->
  let v1, s2 = eval so s env rhs in 
  let l1 = List.assoc vname env in
  let s3 = (l1, v1) :: List.remove_assoc l1 s2 in
  v1, s3
  | Dispatch(e0, fname, args) -> 
    let current_store = ref s in
    let arg_vals = List.map (fun arg_exp -> 
      let arg_val, arg_store = eval so !current_store env arg_exp in
      current_store := arg_store;
      arg_val
    ) args in
    let v0, sn1 = eval so !current_store env e0 in
    (begin match v0 with 
      | Cool_Object(cname, attrs_andlocs) ->
        (* FIX check to make sure it is in there if its not you have a pa5 bug *)
        let formals, body  = List.assoc (cname, fname) impl_map in
        let new_arg_locs = List.map (fun arg_val -> 
          new_loc()
        ) args in 
        let store_updates = List.combine new_arg_locs arg_vals in
        let s_n3 = store_updates @sn1 in
        eval v0 s_n3 attrs_andlocs body
      | _ -> failwith "Type error"
        end)
  | _ -> failwith "Not implemented"
  in
  debug_indent(); debug "result: %s\n" (value_to_str new_value);
  debug_indent(); debug "rets: %s\n\n" (store_to_str new_store);
  indent_count := !indent_count - 2; 
  (new_value, new_store)


let main()= begin
  let my_exp = Dispatch(New("Main"), "main", []) in
  debug "my exp %s\n" (exp_to_str my_exp);
  let so = Void in
  let s = [] in 
  let env = [] in
  let (v, s1) = eval so s env my_exp in
  debug "my value %s\n" (value_to_str v);
end ;;


main() ;;
