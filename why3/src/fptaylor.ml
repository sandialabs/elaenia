(* open Why3
open Pmodule
open Printf *)
open Why3
open Compile
open Format
open Ident
open Pp
open Ity
open Term
open Expr
open Ty
open Theory
open Pmodule
open Wstdlib
open Pdecl
open Printer
open Ity 

open Format
open Ident
open Printer



let rec print_decl args ?old:_ fmt task =
  Format.fprintf fmt "hello world"


let ng suffix ?fname m =
  let mod_name = m.mod_theory.th_name.id_string in
  let path     = m.mod_theory.th_path in
  "test.fptaylor"
  (* (module_name ?fname path mod_name) ^ suffix *)

let fptaylor_printer = Pdriver.{
    desc = "printer for FPtaylor";
    implem_printer = {
        filename_generator = ng ".fptaylor";
        decl_printer = print_decl;
        prelude_printer = dummy_prelude_printer;
        header_printer = dummy_border_printer;
        footer_printer = dummy_border_printer;
      };
    interf_printer = None
  }


let () = Pdriver.register_printer "fptaylor" print_task