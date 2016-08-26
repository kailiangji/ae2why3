let new_file hd ori_file =
  let n = String.length ori_file in
  let j = ref (n-1) in
  while !j <> 0 && String.get ori_file !j <> '/' do
    j := !j - 1
  done;
  if !j = 0 then
    hd ^ ori_file
  else
  (String.sub ori_file 0 (!j + 1))
    ^ hd ^ (String.sub ori_file (!j+1) (n-1-(!j)))

let get_file() = Sys.argv.(1)

let output_file() =
  let file = get_file() in
  if Array.length Sys.argv = 2 then
    new_file "why3_" file
  else
    Sys.argv.(2)
