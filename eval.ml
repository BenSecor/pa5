(* PA5c *)
open Printf

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
    | Dispatch of exp * string * (exp list) (* self.foo(a1, a2, ... an) *)
    | Self_Dispatch of string * (exp list) (* foo(a1, a2, ... an) *)
    | String of string (* "hello" *)
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
    | Internal of string (* empty exp for the method body of internal methods*)

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

(* Evaluation *)
(* Convert expressions to strings for debugging *)

(* Evaluation *)
(* Convert expressions to strings for debugging *)

(* Evaluation *)
(* Convert expressions to strings for debugging *)

let rec exp_to_str (_,e) = 
  match e with
  | New(x) -> sprintf "New(%s)" x
  | Dispatch(e0, fname, args) -> sprintf "Dispatch(%s, %s, [%s])" (exp_to_str e0) fname (String.concat "; " (List.map exp_to_str args))
  | Self_Dispatch(fname, args) -> sprintf "Self_Dispatch(%s, [%s])" fname (String.concat "; " (List.map exp_to_str args))
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
  | Internal(extra_info) -> sprintf "Internal(%s)" extra_info
  | String(s) -> sprintf "String(%s)" s

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
  let eloc, exp = exp in
  let (new_value, new_store) = match exp with
  (* need to add self type *)
  | New(class_name) -> 
  let attrs_and_inits = List.assoc class_name !class_map in
  let new_attr_loc = List.map (fun (aname, ainit) -> 
    new_loc()
  ) attrs_and_inits in
  let attr_names = List.map (fun (aname, ainit) -> aname) attrs_and_inits in
  let attrs_and_locs = List.combine attr_names new_attr_loc in
  let v1 = Cool_Object(class_name, List.combine attr_names new_attr_loc) in
  (* DO THIS : Default Values based on the class_names, cool manual*)
  let store_updates = List.map (fun new_loc -> 
      (new_loc, Cool_Int(0l)) 
  ) new_attr_loc in 
  let s2 = s @ store_updates in
  let final_store = List.fold_left (fun acc_store (aname, ainit) -> 
    match ainit with
    | None -> acc_store
    | Some(ainit) -> 
    let _, updated_store = eval v1 acc_store attrs_and_locs (eloc, Assign(aname, ainit)) in
    updated_store
    (*none case *)
  ) s2 attrs_and_inits in
  v1, final_store
  | Variable(vname) ->
  printf "vname: %s\n" vname;
  let l = List.assoc vname env in
  let final_value = List.assoc l s in
  final_value, s
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
    eval so s2 env (eloc, While(e1, e2))
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
        let class_methods = List.assoc cname !impl_map in
        let formals, body  = List.assoc fname class_methods in
        let new_arg_locs = List.map (fun arg_val -> 
          new_loc()
        ) args in 
        let store_updates = List.combine new_arg_locs arg_vals in
        let s_n3 = store_updates @sn1 in
        eval v0 s_n3 attrs_andlocs body
      | _ -> failwith "Type error"
        end)
  | Self_Dispatch(fname, args) ->
    let current_store = ref s in
    let arg_vals = List.map (fun arg_exp -> 
      let arg_val, arg_store = eval so !current_store env arg_exp in
      current_store := arg_store;
      arg_val
    ) args in
    let v0, sn1 = eval so !current_store env (eloc, Variable("self")) in
    (begin match v0 with 
      | Cool_Object(cname, attrs_andlocs) ->
        (* FIX check to make sure it is in there if its not you have a pa5 bug *)
        let class_methods = List.assoc cname !impl_map in
        let formals, body  = List.assoc fname class_methods in
        let new_arg_locs = List.map (fun arg_val -> 
          new_loc()
        ) args in 
        let store_updates = List.combine new_arg_locs arg_vals in
        let s_n3 = store_updates @sn1 in
        eval v0 s_n3 attrs_andlocs body
      | _ -> failwith "Type error"
        end)
  | String(s) -> Cool_String(s)
  | Internal(extra_info) -> Void
  | _ -> failwith "Not implemented"
  in
  debug_indent(); debug "result: %s\n" (value_to_str new_value);
  debug_indent(); debug "rets: %s\n\n" (store_to_str new_store);
  indent_count := !indent_count - 2; 
  (new_value, new_store)


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
        let aname = read() in
       (* if anane == no initializer  *) 
        let ainit = if aname = "no_initializer" then None else Some(read_exp()) in
        (aname,ainit)
      ) lst in
      (cname, attrs)
    ) lst
  and read_impl_map () =
    let start_map = read() in
    debug "read_impl_map: %s\n" start_map;
    let str = read() in
    debug "read_impl_map: %s\n" str;
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
        let cname = read() in
        New(cname)
      | "dispatch" ->
        let e0 = read_exp() in
        let fname = read() in
        let args = read_list read_exp in
        Dispatch(e0, fname, args)
      | "self_dispatch" ->
        let mloc = read() in
        let mname = read() in
        let args = read_list read_exp in
        Self_Dispatch("mname", args)
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
      | "lessthan" ->
        let e1 = read_exp() in
        let e2 = read_exp() in
        LessThan(e1, e2)
      | "equal" ->
        let e1 = read_exp() in
        let e2 = read_exp() in
        Equal(e1, e2)
      | "not" ->
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
        let x = read() in
        let t = read() in
        let e1 = read_exp() in
        let e2 = read_exp() in
        Let(x, t, e1, e2)
      | "case" ->
        let e = read_exp() in
        let cl = read_list read_case_branch in
        Case(e, cl)
      | "assign" ->
        let vname = read() in
        let e = read_exp() in
        Assign(vname, e)
      in
     (eloc, ekind)
  and read_case_branch() =
      let x = read() in
      let t = read() in
      let e = read_exp() in
      (x, t, e)
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
    |Attribute _ -> 
      false
    |Method((_,mname), _, _, _) ->
      mname = "main"
    ) main_features in
  let main_body = match main_method with
  | Method(_, _, _, body) -> body
  | _ -> failwith "cannot happen"
  in
  let (main_value : cool_value), _ = eval Void [] [] main_body in
  let (main_value_str : string)  = value_to_str main_value in
  output_string stdout main_value_str
end ;;
main() ;;
