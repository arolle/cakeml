open preamble ml_translatorLib ml_progLib std_preludeTheory
     mloptionTheory basisFunctionsLib

val _ = new_theory"RuntimeProg"

val _ = translation_extends"std_prelude"

val () = generate_sigs := true;

val _ = concretise_all () (* TODO: better to leave more abstract longer... *)

val _ = ml_prog_update (open_module "Runtime");

val fullGC_def = Define `
  fullGC (u:unit) = force_gc_to_run 0 0`;

val () = next_ml_names := ["fullGC"];
val result = translate fullGC_def;

val debugMsg_def = Define `
  debugMsg s = empty_ffi s`;

val () = next_ml_names := ["debugMsg"];
val result = translate debugMsg_def;

val exit =
 ``[Dletrec (unknown_loc)
     ["exit","u",
      Let (SOME "x") (App Aw8alloc [Lit(IntLit 0); Lit(Word8 0w)])
          (App (FFI "exit") [Lit (StrLit ""); Var (Short "x")])]]``

val _ = append_prog exit

val sigs = module_signatures ["fullGC", "debugMsg","exit"];

val _ = ml_prog_update (close_module (SOME sigs));

val _ = export_theory();
