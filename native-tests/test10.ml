effect E : unit
let () =
  Printf.printf "%d" @@ try 10 with effect E k -> 11
