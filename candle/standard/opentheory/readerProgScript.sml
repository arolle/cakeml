open preamble
     readerTheory
     ml_monad_translatorLib
     ml_hol_kernelProgTheory

val _ = new_theory "readerProg"
val _ = m_translation_extends "ml_hol_kernelProg"

(* --- Translate readerTheory ---------------------------------------------- *)

val _ = translate init_state_def
val _ = translate mk_BN_def
val _ = translate mk_BS_def
val _ = translate insert_def
val _ = translate delete_def
val _ = translate lookup_def
val _ = translate push_def
val _ = translate insert_dict_def
val _ = translate delete_dict_def
val _ = translate first_def
val _ = translate stringTheory.isDigit_def

val rev_assocd_thm = Q.prove (
  `!a l d. REV_ASSOCD a l d = rev_assocd a l d`,
  recInduct (fetch "holKernel" "rev_assocd_ind") \\ rw []
  \\ Cases_on `l` \\ fs []
  \\ once_rewrite_tac [holKernelTheory.rev_assocd_def]
  \\ fs [holSyntaxLibTheory.REV_ASSOCD_def]
  \\ PairCases_on `h` \\ fs [])

val _ = translate rev_assocd_thm;

val _ = (use_mem_intro := true)
val _ = translate holSyntaxExtraTheory.tymatch_def
val _ = (use_mem_intro := false)
val _ = translate OPTION_MAP_DEF
val _ = translate holSyntaxExtraTheory.match_type_def

val _ = m_translate find_axiom_def
val _ = m_translate getNum_def
val _ = m_translate getName_def
val _ = m_translate getList_def
val _ = m_translate getTypeOp_def
val _ = m_translate getType_def
val _ = m_translate getConst_def
val _ = m_translate getVar_def
val _ = m_translate getTerm_def
val _ = m_translate getThm_def
val _ = m_translate pop_def
val _ = m_translate peek_def
val _ = m_translate getPair_def
val _ = m_translate getNvs_def
val _ = m_translate getCns_def
val _ = m_translate getTys_def
val _ = m_translate getTms_def
val _ = m_translate readLine_def

val readline_side = Q.store_thm("readline_side",
  `!st1 l s. readline_side st1 l s <=> T`,
  rw [fetch "-" "readline_side_def"] \\ intLib.COOPER_TAC)
  |> update_precondition;

(* --- CakeML wrapper ------------------------------------------------------ *)

open basisProgTheory basis_ffiTheory basis_ffiLib basisFunctionsLib
     cfTacticsLib cfLib fsFFITheory
open cfMonadTheory cfMonadLib
open ml_translatorTheory fsFFIPropsTheory

val msg_usage_def = Define `msg_usage = strlit"Usage: reader <article>\n"`

val msg_bad_name_def = Define `
  msg_bad_name s = concat
    [strlit"Bad filename: "; s; strlit".\n"]
  `;

val msg_failure_def = Define `
  msg_failure loc = concat
    [strlit"Reader threw exception: "; loc; strlit".\n"]
  `;

val _ = translate msg_usage_def
val _ = translate msg_bad_name_def
val _ = translate msg_failure_def

val _ = process_topdecs `
  fun read_line st0 ins =
    case TextIO.inputLine ins of
      NONE    => NONE (* EOF *)
    | SOME ln =>
        let val len = String.size ln in
          if len <= 1 then SOME st0 (* Invalid line; "" or "\n" *)
          else if String.sub ln 0 = #"#" then SOME st0 (* Comment *)
          else
            let
              val pfx = String.extract ln 0 (SOME (len-1))
            in
              SOME (readline pfx st0)
            end
        end`
  |> append_prog;

val Valid_line_def = Define `
  Valid_line str <=>
    STRLEN str > 1 /\
    ~IS_PREFIX str "#"`;

val str_prefix_def = Define `
  str_prefix str = extract str 0 (SOME (strlen str - 1))`;

val readline_spec = save_thm (
  "readline_spec",
  mk_app_of_ArrowP ``p: 'ffi ffi_proj`` (theorem "readline_v_thm"));

(* Additional definitions *)
open holKernelTheory ml_monadBaseTheory mlstringTheory

val read_line_spec = Q.store_thm("read_line_spec",
  `!fs fd fdv st stv refs.
     WORD (n2w fd : word8) fdv /\ fd <= 255 /\
     IS_SOME (get_file_content fs fd) /\
     STATE_TYPE st stv
     ==>
     app (p: 'ffi ffi_proj) ^(fetch_v "read_line" (get_ml_prog_state()))
       [stv; fdv]
       (STDIO fs * HOL_STORE refs)
       (POST
         (\stov.
          case lineFD fs fd of
            NONE =>
              STDIO (lineForwardFD fs fd) *
              HOL_STORE refs *
              &OPTION_TYPE STATE_TYPE NONE stov
          | SOME ln =>
              if Valid_line ln then
                SEP_EXISTS sto refs'.
                  STDIO (lineForwardFD fs fd) * HOL_STORE refs' *
                  &(readLine (str_prefix (strlit ln)) st refs = (Success sto, refs')) *
                  &OPTION_TYPE STATE_TYPE (SOME sto) stov
              else
                STDIO (lineForwardFD fs fd) *
                HOL_STORE refs *
                &OPTION_TYPE STATE_TYPE (SOME st) stov)
         (\ev.
           SEP_EXISTS e ln refs'.
             STDIO (lineForwardFD fs fd) * HOL_STORE refs' *
             &(readLine (str_prefix (strlit ln)) st refs = (Failure e, refs')) *
             &HOL_EXN_TYPE e ev *
             &(lineFD fs fd = SOME ln /\
               STRLEN ln > 1 /\
               ~IS_PREFIX ln "#")))`,
  xcf "read_line" (get_ml_prog_state())
  \\ xlet_auto >- xsimpl
  \\ Cases_on `lineFD fs fd` \\ fs [OPTION_TYPE_def] \\ xmatch
  >- (xvar \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xif \\ fs [Valid_line_def]
  >- (xcon \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xif
  >-
   (`?t. x = #"#"::t` by (Cases_on `x` \\ fs [implode_def]) \\ fs []
    \\ xcon \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ `OPTION_TYPE NUM (SOME (STRLEN x - 1)) v'` by
   (fs [OPTION_TYPE_def, NUM_def, INT_def]
    \\ Cases_on `x` \\ fs []
    \\ intLib.COOPER_TAC)
  \\ rveq
  \\ xlet_auto >- xsimpl
  \\ xlet_auto \\ xsimpl
  >-
   (qexists_tac `STDIO (lineForwardFD fs fd)`
    \\ qexists_tac `refs`
    \\ xsimpl)
  >-
   (fs [implode_def, str_prefix_def]
    \\ rw [] \\ xsimpl
    \\ CASE_TAC \\ fs [])
  \\ xcon
  >-
   (fs [implode_def, str_prefix_def]
    \\ CASE_TAC \\ fs []
    \\ xsimpl)
  \\ xsimpl
  \\ CASE_TAC \\ fs []
  \\ fs [implode_def, str_prefix_def]);

(* Read all lines until input is exhausted *)
val _ = process_topdecs `
  fun read_file file =
    let
      val ins = TextIO.openIn file

      fun go st0 =
        case read_line st0 ins of
          NONE => TextIO.print_string "OK!\n"
        | SOME st1 => go st1
        handle Fail e => TextIO.prerr_string (msg_failure e)
             | Clash e => TextIO.prerr_string "KERNEL CLASH.\n"

    in
      go init_state;
      TextIO.closeIn ins
    end
    handle TextIO.BadFileName e => TextIO.prerr_string (msg_bad_name file)`
  |> append_prog;

val fix_lines_def = Define `
  fix_lines ss = MAP strlit (FILTER (\s. ~(IS_PREFIX s "#" \/ NULL s)) ss)`;

val read_file_spec = Q.store_thm("read_file_spec",
  `FILENAME fnm fnv /\
   hasFreeFD fs
   ==>
   app (p: 'ffi ffi_proj) ^(fetch_v "read_file" (get_ml_prog_state())) [fnv]
     (STDIO fs * HOL_STORE refs)
     (POSTv u.
       &UNIT_TYPE () u *
       (case ALOOKUP fs.files (File fnm) of
          SOME content =>
            (case readLines (fix_lines (splitlines content)) init_state refs of
              (Success s, refs') =>
                  STDIO (add_stdout fs "OK!\n") *
                  HOL_STORE refs'
            | (Failure (Fail e), refs') =>
                  STDIO (add_stderr fs (explode (msg_failure e))) *
                  HOL_STORE refs'
            | (Failure (Clash e), refs') =>
                  STDIO (add_stderr fs "KERNEL CLASH.\n") *
                  HOL_STORE refs')
       | NONE =>
           STDIO (add_stderr fs (explode (msg_bad_name fn))) *
           HOL_STORE refs))`,

  xcf "read_file" (get_ml_prog_state())
  \\ reverse (Cases_on `STD_streams fs`)
  >- (fs [TextIOProofTheory.STDIO_def] \\ xpull)
  \\ xhandle
    `POST
      (\u.
        SEP_EXISTS content.
          &UNIT_TYPE () u *
          &(ALOOKUP fs.files (File fnm) = SOME content) *
          (case readLines (fix_lines (splitlines content)) init_state refs of
            (Success s, refs') =>
                STDIO (add_stdout fs "OK!\n") *
                HOL_STORE refs'
          | (Failure (Fail e), refs') =>
                STDIO (add_to_stderr fs (explode (msg_failure e))) *
                HOL_STORE refs'
          | (Failure (Clash e), refs') =>
                STDIO (add_to_stderr fs "KERNEL CLASH.\n") *
                HOL_STORE refs'))
      (\e.
        &BadFileName_exn e *
        &(~inFS_fname fs (File fnm)) *
        STDIO fs * HOL_STORE refs)` \\ xsimpl
  >-
   (
    xlet_auto_spec (SOME (SPEC_ALL TextIOProofTheory.openIn_STDIO_spec)) \\ xsimpl
    \\ imp_res_tac nextFD_leX
    \\ qspec_then `0` drule (GEN_ALL ALOOKUP_inFS_fname_openFileFS_nextFD) \\ fs []
    \\ strip_tac
    \\ imp_res_tac STD_streams_nextFD
    \\ qabbrev_tac `fd = nextFD fs`
    \\ xfun_spec `go`
      `!m n stg stvg fsg refsg.
         STATE_TYPE stg stvg /\
         m = STRLEN content - n /\
         n <= STRLEN content /\
         STD_streams fsg /\
         get_file_content fsg fd = SOME (content, n)
         ==>
         app p go [stvg]
           (STDIO fsg * HOL_STORE refsg)
           (POSTv u.
             &UNIT_TYPE () u *
             (case readLines (fix_lines (splitlines (DROP n content))) init_state refsg of
               (Success s, refs') =>
                   STDIO (add_stdout (fastForwardFD fsg fd) "OK!\n") *
                   HOL_STORE refs'
             | (Failure (Fail e), refs') =>
                   STDIO (add_stderr (forwardFD fsg fd n) (explode (msg_failure e))) *
                   HOL_STORE refs'
             | (Failure (Clash e), refs') =>
                   STDIO (add_stderr (forwardFD fsg fd n) "KERNEL CLASH.\n") *
                   HOL_STORE refs'))`
    >-
     (
      Induct
      >-
       (rpt strip_tac
        \\ `n = STRLEN content` by fs [] \\ fs [] \\ rveq
        \\ imp_res_tac get_file_content_eof \\ fs []
        \\ xapp
        \\ `IS_SOME (get_file_content fsg fd)` by fs []
        \\ `lineFD fsg fd = NONE` by fs [lineFD_def]
        \\ xlet_auto_spec
          (SOME (Q.SPECL [`fsg: IO_fs`,`fd`] read_line_spec)) \\ xsimpl
        >-
         (qexists_tac `GC`
          \\ qexists_tac `refsg`
          \\ xsimpl)
        \\ fs [DROP_LENGTH_NIL, fix_lines_def]
        \\ once_rewrite_tac [readLines_def]
        \\ fs [st_ex_return_def, OPTION_TYPE_def]
        \\ xmatch
        \\ xapp \\ xsimpl
        \\ imp_res_tac lineFD_NONE_lineForwardFD_fastForwardFD \\ fs []
        \\ qexists_tac `HOL_STORE refsg` \\ xsimpl
        \\ qexists_tac `fastForwardFD fsg fd` \\ xsimpl)
      \\ rpt strip_tac
      \\ last_assum xapp_spec
      \\ xlet_auto_spec
        (SOME (Q.SPECL [`fsg: IO_fs`,`fd`] read_line_spec)) \\ xsimpl
      >- cheat (* TODO *)
      >- cheat (* TODO *)
      \\ cheat (* TODO *)
     )
    \\ cheat (* TODO *)
   )
  \\ cheat (* TODO *)
  );

val _ = process_topdecs `
  fun reader_main u =
    case CommandLine.arguments () of
      [file] => read_file file
    | _      => TextIO.prerr_string msg_usage
  ` |> append_prog;

val st = get_ml_prog_state ();
val name = "reader_main"

(*open ml_progLib*)

(*[> TODO: Replace with call_thm <]*)
(*val reader_prog_tm =*)
  (*let*)
    (*val th =*)
      (*call_main_thm_basis*)
      (*|> C MATCH_MP (st |> get_thm |> GEN_ALL |> ISPEC basis_ffi_tm)*)
      (*|> SPEC(stringSyntax.fromMLstring name)*)
      (*|> CONV_RULE(QUANT_CONV(LAND_CONV(LAND_CONV EVAL THENC SIMP_CONV std_ss [])))*)
      (*|> CONV_RULE(HO_REWR_CONV UNWIND_FORALL_THM1)*)
      (*[>|> C HO_MATCH_MP spec<]*)
    (*val prog_with_snoc = th |> concl |> find_term listSyntax.is_snoc*)
    (*val prog_rewrite = EVAL prog_with_snoc*)
  (*in*)
    (*rhs (concl prog_rewrite)*)
  (*end*)

val reader_prog_def = Define `reader_prog = ^reader_prog_tm`

val _ = export_theory ();

