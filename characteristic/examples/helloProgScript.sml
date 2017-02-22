open  preamble ml_progLib ioProgLib ml_translatorLib
      cfTacticsLib

val _ = new_theory "helloProg"

val _ = translation_extends"ioProg";

val hello = process_topdecs
  `fun hello u = print "Hello World!\n"`

val res = ml_prog_update(ml_progLib.add_prog hello pick_name)

val st = get_ml_prog_state ()

val hello_spec = Q.store_thm ("hello_spec",
  `!cv input output.
      app (p:'ffi ffi_proj) ^(fetch_v "hello" st)
        [Conv NONE []]
        (STDOUT [] * frame)
        (POSTv uv. &UNIT_TYPE () uv * (STDOUT ("Hello World!\n") * frame))`,
  xcf "hello" st 
  \\ xapp 
  \\ xsimpl \\ qexists_tac `frame` \\ qexists_tac `[]` \\ xsimpl 
); 

val st = get_ml_prog_state();
val spec = hello_spec |> SPEC_ALL |> UNDISCH_ALL |> add_basis_proj;
val name = "hello";
val (call_thm_hello, hello_prog_tm) = call_thm st name spec;
val hello_prog_def = Define`hello_prog = ^hello_prog_tm`;

val _ = export_theory ()