(* Automatically generated with `-i` *)
val print_stmt : Format.formatter -> Cil_types.stmtkind -> unit
class find_flops :
  Format.formatter ->
  object
    method behavior : Visitor_behavior.t
    method current_func : Cil_types.fundec option
    method current_kf : Cil_types.kernel_function option
    method current_kinstr : Cil_types.kinstr
    method current_stmt : Cil_types.stmt option
    method fill_global_tables : unit
    method frama_c_plain_copy : Visitor.frama_c_visitor
    method get_filling_actions : (unit -> unit) Queue.t
    method plain_copy_visitor : Cil.cilVisitor
    method pop_stmt : Cil_types.stmt -> unit
    method project : Project.t option
    method push_stmt : Cil_types.stmt -> unit
    method queueInstr : Cil_types.instr list -> unit
    method reset_current_func : unit -> unit
    method reset_current_kf : unit -> unit
    method set_current_func : Cil_types.fundec -> unit
    method set_current_kf : Cil_types.kernel_function -> unit
    method unqueueInstr : unit -> Cil_types.instr list
    method vallocates :
      Cil_types.identified_term list ->
      Cil_types.identified_term list Cil.visitAction
    method vallocation :
      Cil_types.allocation -> Cil_types.allocation Cil.visitAction
    method vannotation :
      Cil_types.global_annotation ->
      Cil_types.global_annotation Cil.visitAction
    method vassigns : Cil_types.assigns -> Cil_types.assigns Cil.visitAction
    method vattr :
      Cil_types.attribute -> Cil_types.attribute list Cil.visitAction
    method vattrparam :
      Cil_types.attrparam -> Cil_types.attrparam Cil.visitAction
    method vbehavior :
      Cil_types.funbehavior -> Cil_types.funbehavior Cil.visitAction
    method vblock : Cil_types.block -> Cil_types.block Cil.visitAction
    method vcode_annot :
      Cil_types.code_annotation -> Cil_types.code_annotation Cil.visitAction
    method vcompinfo :
      Cil_types.compinfo -> Cil_types.compinfo Cil.visitAction
    method vdeps : Cil_types.deps -> Cil_types.deps Cil.visitAction
    method venuminfo :
      Cil_types.enuminfo -> Cil_types.enuminfo Cil.visitAction
    method venumitem :
      Cil_types.enumitem -> Cil_types.enumitem Cil.visitAction
    method vexpr : Cil_types.exp -> Cil_types.exp Cil.visitAction
    method vfieldinfo :
      Cil_types.fieldinfo -> Cil_types.fieldinfo Cil.visitAction
    method vfile : Cil_types.file -> Cil_types.file Cil.visitAction
    method vfrees :
      Cil_types.identified_term list ->
      Cil_types.identified_term list Cil.visitAction
    method vfrom : Cil_types.from -> Cil_types.from Cil.visitAction
    method vfunc : Cil_types.fundec -> Cil_types.fundec Cil.visitAction
    method vglob : Cil_types.global -> Cil_types.global list Cil.visitAction
    method vglob_aux :
      Cil_types.global -> Cil_types.global list Cil.visitAction
    method videntified_predicate :
      Cil_types.identified_predicate ->
      Cil_types.identified_predicate Cil.visitAction
    method videntified_term :
      Cil_types.identified_term -> Cil_types.identified_term Cil.visitAction
    method vimpact_pragma :
      Cil_types.impact_pragma -> Cil_types.impact_pragma Cil.visitAction
    method vinit :
      Cil_types.varinfo ->
      Cil_types.offset -> Cil_types.init -> Cil_types.init Cil.visitAction
    method vinitoffs : Cil_types.offset -> Cil_types.offset Cil.visitAction
    method vinst : Cil_types.instr -> Cil_types.instr list Cil.visitAction
    method vlocal_init :
      Cil_types.varinfo ->
      Cil_types.local_init -> Cil_types.local_init Cil.visitAction
    method vlogic_ctor_info_decl :
      Cil_types.logic_ctor_info -> Cil_types.logic_ctor_info Cil.visitAction
    method vlogic_ctor_info_use :
      Cil_types.logic_ctor_info -> Cil_types.logic_ctor_info Cil.visitAction
    method vlogic_info_decl :
      Cil_types.logic_info -> Cil_types.logic_info Cil.visitAction
    method vlogic_info_use :
      Cil_types.logic_info -> Cil_types.logic_info Cil.visitAction
    method vlogic_label :
      Cil_types.logic_label -> Cil_types.logic_label Cil.visitAction
    method vlogic_type :
      Cil_types.logic_type -> Cil_types.logic_type Cil.visitAction
    method vlogic_type_def :
      Cil_types.logic_type_def -> Cil_types.logic_type_def Cil.visitAction
    method vlogic_type_info_decl :
      Cil_types.logic_type_info -> Cil_types.logic_type_info Cil.visitAction
    method vlogic_type_info_use :
      Cil_types.logic_type_info -> Cil_types.logic_type_info Cil.visitAction
    method vlogic_var_decl :
      Cil_types.logic_var -> Cil_types.logic_var Cil.visitAction
    method vlogic_var_use :
      Cil_types.logic_var -> Cil_types.logic_var Cil.visitAction
    method vloop_pragma :
      Cil_types.loop_pragma -> Cil_types.loop_pragma Cil.visitAction
    method vlval : Cil_types.lval -> Cil_types.lval Cil.visitAction
    method vmodel_info :
      Cil_types.model_info -> Cil_types.model_info Cil.visitAction
    method voffs : Cil_types.offset -> Cil_types.offset Cil.visitAction
    method vpredicate :
      Cil_types.predicate -> Cil_types.predicate Cil.visitAction
    method vpredicate_node :
      Cil_types.predicate_node -> Cil_types.predicate_node Cil.visitAction
    method vquantifiers :
      Cil_types.quantifiers -> Cil_types.quantifiers Cil.visitAction
    method vslice_pragma :
      Cil_types.slice_pragma -> Cil_types.slice_pragma Cil.visitAction
    method vspec : Cil_types.funspec -> Cil_types.funspec Cil.visitAction
    method vstmt : Cil_types.stmt -> Cil_types.stmt Cil.visitAction
    method vstmt_aux : Cil_types.stmt -> Cil_types.stmt Cil.visitAction
    method vterm : Cil_types.term -> Cil_types.term Cil.visitAction
    method vterm_lhost :
      Cil_types.term_lhost -> Cil_types.term_lhost Cil.visitAction
    method vterm_lval :
      Cil_types.term_lval -> Cil_types.term_lval Cil.visitAction
    method vterm_node :
      Cil_types.term_node -> Cil_types.term_node Cil.visitAction
    method vterm_offset :
      Cil_types.term_offset -> Cil_types.term_offset Cil.visitAction
    method vtype : Cil_types.typ -> Cil_types.typ Cil.visitAction
    method vvdec : Cil_types.varinfo -> Cil_types.varinfo Cil.visitAction
    method vvrbl : Cil_types.varinfo -> Cil_types.varinfo Cil.visitAction
  end
