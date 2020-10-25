theory Wasm_Printing imports Wasm_Checker_Printing Wasm_Interpreter_Printing Wasm_Type_Printing "HOL-Library.Code_Target_Nat" begin

lemma [code]: "pred_option P None = True"
  using Option.option.pred_inject(1)
  by auto

lemmas[code] = Option.option.pred_inject(2)

export_code open typing run in OCaml file "code/Wasm_Executable.ml"

end