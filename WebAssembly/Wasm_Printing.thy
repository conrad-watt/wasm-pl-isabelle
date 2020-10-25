theory Wasm_Printing imports Wasm_Instantiation_Printing Wasm_Checker_Printing Wasm_Interpreter_Printing Wasm_Type_Printing "HOL-Library.Code_Target_Nat" begin

lemma [code]: "pred_option P None = True"
  using Option.option.pred_inject(1)
  by auto

lemmas[code] = Option.option.pred_inject(2)

export_code open interp_instantiate typing run in OCaml module_name WasmRef_Isa file "code/Wasm_Executable.ml"

end