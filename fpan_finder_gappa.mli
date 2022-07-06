val print_stmt : Format.formatter -> Cil_types.stmtkind -> unit

class find_flops_gappa : Format.formatter -> object
  inherit Visitor.frama_c_inplace
end

