(** The same as OCanren.tester but with timeing *)

open Printf
open OCanren

(** {3 Helper functions to provide names for top-level variables } *)

let print_span span =
  let ms = Mtime.Span.to_ms span in
  if ms > 10000.0 then printf "%10.0fs \n%!" (Mtime.Span.to_s span)
  else printf "%10.0fms\n%!" ms

let wrap ~span onOK i (name, x) = onOK i name ~span x

let qh onOK q ~span () =
  print_span span;
  List.iteri (wrap ~span onOK) @@ [ ("q", q) ]

let qrh onOK q r ~span () =
  print_span span;
  List.iteri (wrap ~span onOK) @@ [ ("q", q); ("r", r) ]

let qrsh onOK q r s ~span () =
  print_span span;
  List.iteri (wrap ~span onOK) @@ [ ("q", q); ("r", r); ("s", s) ]

let qrsth onOK q r s t ~span () =
  print_span span;
  List.iteri (wrap ~span onOK) @@ [ ("q", q); ("r", r); ("s", s); ("t", t) ]

let make_title n msg =
  printf "%s, %s answer%s {\n%!" msg
    (if n = -1 then "all" else string_of_int n)
    (if n <> 1 then "s" else "")

exception NoMoreAnswers

let run_gen onOK n num handler (repr, goal) =
  make_title n repr;
  let rec loop st = function
    | k when k > n && n >= 0 -> ()
    | k -> (
        let start = Mtime_clock.counter () in
        let stream_rez = Stream.retrieve ~n:1 st in
        let span = Mtime_clock.count start in
        match stream_rez with
        | [], _ ->
            print_span span;
            raise NoMoreAnswers
        | [ f ], tl ->
            f ~span ();
            printf "\n%!";
            loop tl (k + 1)
        | _ -> assert false)
  in
  let handler = handler onOK in
  let () = try loop (run num goal handler) 1 with NoMoreAnswers -> () in
  printf "}\n%!"

(**
  [run_exn printer n name_helper goal] prints answers supposing there are no free variables there
  (i.e. reification is not required)
*)

(* let run_exn printer =
   run_gen
     (fun i name ~span x ->
       printf "%s%s=%s;%!" (if i <> 0 then " " else "") name (printer x#prj))
     (fun _ _ ~span:_ _ -> failwith "Free logic variables in the answer")
*)
(**
  [runR reifier print_plain print_injected n name_helper goal] prints answers both with free varibles and
  without them. In the first cases it uses [print_plain] as printer fuction. In the latter case it does
  reification using [reifier] and prints the result wit [print_ibjected]
*)

(* let runR reifier printerNoFree printerR = run_gen
   (fun i name ~span x ->
     (* i is a answer part (depends on qh, qrh sizes). It is not index of an answer *)
     printf "%s%s=%s;%!" (if i<>0 then " " else "") name (printerNoFree ~span x#prj)
   )
   (fun i name ~span func  ->
     let ans = func#reify reifier in
     printf "%s%s=%s;%!" (if i<>0 then " " else "") name (printerR ~span ans)
     )
*)

let run_r reifier printer =
  run_gen (fun i name ~span (x : _ OCanren.reified) ->
      let ans = x#reify reifier in
      printf "%s%s=%s;%!" (if i <> 0 then " " else "") name (printer ~span ans))
(* (fun i name ~span func ->
   let ans = func#prjc reifier in
   printf "%s%s=%s;%!" (if i <> 0 then " " else "") name (printer ~span ans))
*)

let%expect_test " " =
  run_r OCanren.prj_exn
    (fun ~span:_ -> string_of_int)
    1 q qh
    ("", fun q -> q === !!11);
  [%expect {|
    , 1 answer {
             0ms
    q=11;
    } |}]
