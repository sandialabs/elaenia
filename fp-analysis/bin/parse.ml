(* Uses CIL to parse the C AST *)
module U = Util

open List
open GoblintCil
open Tree
open Printing

module E = Errormsg
module F = Frontc
module C = Cil

exception ParseError of string ;;

let parse_file fname = 
    let _, cil = F.parse_with_cabs fname () in
    RmUnused.removeUnused cil ;
    cil ;;

let transform_const c =
    match c with
    | CReal (f,_,_) ->
        CVal (CFloat f)
    | CInt (i,_,_) ->
        CVal (CInt (Cilint.int_of_cilint i))
    | CStr (_,_) ->
        raise (ParseError "CStr\n")
    | CWStr (_,_) ->
        raise (ParseError "CWStr\n")
    | CChr _ ->
        raise (ParseError "CChr\n")
    | CEnum (_,_,_) ->
        raise (ParseError "CEnum")
    ;;

let rec transform_arith_binop (op : binop) (l : exp) (r : exp) : caexp =
    let new_l, new_r = (transform_aexp l, transform_aexp r) in
    match op with
    | PlusA ->
        CAdd (new_l, new_r)
    | MinusA ->
        CSub (new_l, new_r)
    | Mult ->
        CMul (new_l, new_r)
    | Div ->
        CDiv (new_l, new_r)
    | IndexPI -> failwith "indexpi"
    | _ -> 
        raise (ParseError "Expected Arithmetic Binop\n") ; 
        (*
    | Lt ->
        CLt (new_l, new_r)
    | Gt ->
        CGt (new_l, new_r)
    | Le ->
        CLe (new_l, new_r)
    | Ge ->
        CGe (new_l, new_r)
    | Eq ->
        CEq (new_l, new_r)
    | Ne ->
        CNe (new_l, new_r)
        *)
    (*
    | LAnd ->
    | LOr ->
    *)
    
and transform_aexp (e : exp) : caexp =
    match e with
    | Cil.Const c ->
        transform_const c
    | BinOp (op, l, r, _) ->
        transform_arith_binop op l r
    | Lval lv -> (
        let (name, index, typ) = transform_lval lv in
        match index with
        | Some _ -> CAcc (name, index, typ)
        | None -> CVar (name, typ))
    | CastE (ty, e) -> (
        match ty with
        | TInt _ | TFloat _ ->  (* TODO: note the loss of precision for float -> int casts *)
            transform_aexp e
        | _ -> raise (ParseError "Unsupported Cast\n") );
    | UnOp (op,exp,_) -> (
        match op with
        | Neg  -> CMul (CVal (CFloat (-1.)), (transform_aexp exp))
        | BNot -> raise (ParseError "Bitwise complement not supported\n")
        | LNot -> raise (ParseError "logical not unsupported\n")
        )
    | Real _ ->
        raise (ParseError "Real unsupported\n") 
    | AddrOf (_) ->
        raise (ParseError "AddrOf unsupported\n")
    | SizeOf _ ->
        raise (ParseError "SizeOf unsupported\n")
    | Imag _ ->
        raise (ParseError "Imag unsupported\n")
    | SizeOfE _ ->
        raise (ParseError "SizeOfE unsupported\n")
    | SizeOfStr _ ->
        raise (ParseError "SizeOfStr unsupported\n")
    | AlignOf _ ->
        raise (ParseError "AlignOf unsupported\n")
    | Question (_,_,_,_) ->
        raise (ParseError "Question unsupported\n")
    | AddrOfLabel _ ->
        raise (ParseError "AddrOfLabel unsupported\n")
    | StartOf _ ->
        raise (ParseError "StartOf unsupported\n")
    | AlignOfE _ ->
        raise (ParseError "AlignOfE unsupported\n")

(* Gets the name of the variable *)
and transform_lval ((lhost, offset) : lval) : (string * caexp option * ctyp) =
    match lhost with
    | Var vi -> (vi.vname, offset_index offset, get_type_varinfo vi)
    (* Assigning to pointers, assuming only arrays now *)
    | Mem l -> (
        match l with
        (* Binop because x[exp] is a binary operation apparently *)
        | BinOp (IndexPI, (Lval ((Var vi), _)), ex2, t) ->
            (vi.vname, Some (transform_aexp ex2), get_type t)
        | _ -> raise (ParseError "Non-array pointers are not supported\n"))

and offset_index (off : offset) : caexp option = 
    match off with
    | Index (e, _) -> Some (transform_aexp e)
    | _ -> None 

and get_type_varinfo (vi : varinfo) : ctyp = get_type vi.vtype

and get_type (t : typ) : ctyp =
    match t with
    | TInt   (_,_) -> IntTyp
    | TFloat (_,_) -> FloatTyp
    | TArray (t,_,_) -> ArrTyp (get_type t) 
    | TPtr (t, _) -> get_type t
    | _ -> raise (ParseError "Unsupported variable type") ;;


let rec transform_bexp e =
    match e with
    | BinOp (op, l, r, _) -> transform_bool_binop op l r
    (*
    | Cil.Const c ->
        transform_const c
    *)
    | _ -> 
        raise (ParseError "Unknown exp\n") ;
    
and transform_bool_binop op l r =
    let new_l, new_r = (transform_aexp l, transform_aexp r) in
    match op with
    | Lt ->
        CLt (new_l, new_r)
    | Gt ->
        CGt (new_l, new_r)
    | Le ->
        CLe (new_l, new_r)
    | Ge ->
        CGe (new_l, new_r)
    | Eq ->
        CEq (new_l, new_r)
    | Ne ->
        CNe (new_l, new_r)
    | _ -> 
        raise (ParseError "Expected comparison operator\n") ;;
    (*
    | LAnd ->
    | LOr ->
    *)
    

let transform_instr i =
    match i with
    | Set (lv, e, _, _) -> (
        let (name, index, _) = transform_lval lv in
        CAsgn ((name, index), (transform_aexp e)))
    | VarDecl (_,_) ->
        raise (ParseError "Variable declarations are not supported") ;
    | Call (_,_,_,_,_) ->
        raise (ParseError "Function calls are not supported\n") ;
    | Asm (_,_,_,_,_,_) ->
        raise (ParseError "Assembly is not supported\n") ;
    ;;

let rec transform_stmt s =
    match s.skind with
    | Instr is -> (transform_instrs is)
    | If (c, b1, b2,_,_) -> 
        CIf (transform_bexp c, transform_block b1, transform_block b2)
    | Return (e, _, _) -> (
        match e with
        | Some exp -> CRet (transform_aexp exp)
        | _ -> CRet (CVal (CInt 1)))
    | Loop (body, _,_, _, _) ->
        transform_loop body (hd s.preds)
    | Goto (_,_) ->
        raise (ParseError "Goto unsupported\n")
    | ComputedGoto (_,_) ->
        raise (ParseError "ComputedGoto unsupported\n")
    | Break _ -> 
        raise (ParseError "Break unsupported\n")
    | Continue _ ->
        raise (ParseError "Continue unsupported\n")
    | Switch (_,_,_,_,_) ->
        raise (ParseError "Switch unsupported\n")
    | Block _ ->
        raise (ParseError "Block unsupported\n")

and transform_instrs is =
    match is with
    | i1 :: is ->
        List.fold_left 
            (fun acc i -> CCol (acc, transform_instr i)) 
            (transform_instr i1) 
            is
    | [] -> raise (ParseError "Empty Instr") 

and str_stmt (s : stmt) : string =
    match s.skind with
    | Instr _ -> "Instrs"
    | Return _ -> "Return"
    | Goto _ -> "Goto"
    | ComputedGoto _ -> "ComputedGoto"
    | Break _ -> "Break"
    | Continue _ -> "Continue"
    | If _ -> "If"
    | Switch _ -> "Switch"
    | Loop _ -> "Loop"
    | Block _ -> "Block"

and transform_block (b : block) : cstmt = 
    let stmts = 
        List.filter (fun s -> 
                        match s.skind with
                        | Break _ -> false 
                        | _ -> true) 
                    b.bstmts in
    match to_cstmts stmts with
    | s1 :: [] -> s1
    | s1 :: s -> List.fold_left (fun acc s -> CCol (acc, s)) s1 s
    | [] -> raise (ParseError "Empty block")


(* This "disgusting bespoke for-loop mangling" Is needed to get the
   initialization statement from the previous Instr list *)
and to_cstmts stmts = 
    List.mapi 
        (fun i s ->
            try let next_stmt = nth stmts (i + 1) in
                match s.skind, next_stmt.skind with
                | Instr is, Loop _ ->
                    (* let the loop know about the init *)
                    next_stmt.preds <- [s] ; 
                    (* then deal with the pre-loop stuff *)
                    transform_instrs (U.remove_last is)
                | _ -> transform_stmt s
            with 
            | (Failure _) -> transform_stmt s)
        stmts


and transform_loop block init = 
    let last_instr is = 
        match is.skind with
        | Instr is -> U.last is
        | _ -> raise (ParseError "Expected instructions at end of loop") in
    let init_instr = 
        match init.skind with
        | Instr is -> U.last is
        | _ -> raise (ParseError "Init instruction not added to beginning of loop") in
    let stmts = block.bstmts in
    CFor (transform_instrs [init_instr],
          extract_condition (hd stmts),
          transform_instr (last_instr (U.last stmts)),
          transform_loop_block {battrs = block.battrs ; bstmts = (tl stmts)})

(* Need to remove the last instruction from the last statment *)
and transform_loop_block block =
    let cleaned = 
        match (U.last block.bstmts).skind with
        | Instr is -> 
            (U.remove_last block.bstmts) @ [mkStmt (Instr (U.remove_last is))]
        | _ -> raise 
            (ParseError "Expected an Instr at the end of the loop body") 
    in
        transform_block {battrs = block.battrs ; bstmts = cleaned}

and extract_condition stmt =
    match stmt.skind with
    | If (c, _, _, _, _) -> transform_bexp c
    | _ -> raise (ParseError "Expected if condition from for loop")
    ;;

let transform_fun f =
    let { sformals = _; sbody = body ; _ } = f in
    transform_block body ;;

let transform_global g =
    match g with
    | GFun (dec,_) ->
        transform_fun dec
    | _ -> 
        raise (ParseError "Non-function globals not supported\n") ;
    (*
    | GType (_,_) -> 
        E.log "GType"
    | GCompTag (_,_) ->
        E.log "GCompTag"
    | GCompTagDecl (_,_) ->
        E.log "GCompTagDecl"
    | GEnumTag (_,_) ->
        E.log "GEnumTag"
    | GEnumTagDecl (_,_) ->
        E.log "GEnumTagDecl"
    | GVarDecl (_,_) ->
        E.log "GVarDecl"
    | GVar (_,_,_) ->
        E.log "GVar"
    | GAsm (_,_) ->
        E.log "GAsm"
    | GPragma (_,_) ->
        E.log "GPragma"
    | GText _ ->
        E.log "GText"
    *)
    ;;

let transform file fun_name = 
    transform_global 
        (List.find (fun g -> 
            match g with
            | GFun (dec,_) -> dec.svar.vname = fun_name
            | _ -> false) 
        file.globals ) ;;

(* Getting the function declaration *)
(* ----------------------------------------- *)
let get_int_string (i : ikind) : string =
    match i with
    | IChar      -> "unsigned char"
    | ISChar     -> "signed char"
    | IUChar     -> "unsigned char"
    | IBool      -> "bool"
    | IInt       -> "int"
    | IUInt      -> "unsigned int"
    | IShort     -> "short"
    | IUShort    -> "unsigned short"
    | ILong      -> "long"
    | IULong     -> "unsigned long"
    | ILongLong  -> "long long"
    | IULongLong -> "unsigned long long"
    | IInt128    -> "__int128"
    | IUInt128   -> "unsigned __int128"
;;


let get_float_string (f : fkind) : string =
    match f with
    | FFloat             -> "float"
    | FDouble            -> "double"
    | FLongDouble        -> "long double"
    | FFloat128          -> "float128"
    | FComplexFloat      -> "float _Complex"
    | FComplexDouble     -> "double _Complex"
    | FComplexLongDouble -> "long double _Complex"
    | FComplexFloat128   -> "_float128 _Complex"
;;


let rec get_typ_string (t : typ) : string =
    match t with
    | TVoid  _      -> "void"
    | TInt   (i, _) -> get_int_string i
    | TFloat (f, _) -> get_float_string f
    | TPtr   (ty, _) -> get_typ_string ty ^ "*"
    | TArray (ty, _, _) -> get_typ_string ty ^ "*"
    | TFun (ty, params,_,_) -> get_typ_string ty
    | _ -> raise (ParseError "Function type not supported")


let get_decl_params (formals : varinfo list) =
    let params = 
        (fold_left (fun acc f -> acc ^ Format.sprintf ", %s %s" (get_typ_string f.vtype) f.vname) 
                    "" 
                    formals)
    in 
        if String.length params > 2 then String.sub params 2 ((String.length params) - 2)
        else params


let get_decl_string f = 
    let { svar = fn ; sformals = formals ; } = f in
    let { vname = name ; vtype = typ ; } = fn in
    Format.sprintf "%s %s (%s);" (get_typ_string typ) name (get_decl_params formals) ;;


let get_global_decl g =
    match g with
    | GFun (dec,_) ->
        get_decl_string dec
    | _ -> 
        raise (ParseError "Non-function globals not supported\n") ;;


let get_fun_decl file fun_name =
    get_global_decl
        (List.find (fun g ->
            match g with
            | GFun (dec,_) -> dec.svar.vname = fun_name
            | _ -> false)
        file.globals) ;;
