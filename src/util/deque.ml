(*
 * deque.ml --- Persistent functional double-ended queues
 *
 *
 * Copyright (C) 2008-2019  INRIA and Microsoft Corporation
 *)

open Ext

type 'a dq = { front : 'a list ; flen : int ;
               rear : 'a list  ; rlen : int }

let empty = { front = [ ] ; flen = 0 ;
              rear  = [ ] ; rlen = 0 }

let size q =
  q.flen + q.rlen

let cons x q =
  { q with front = x :: q.front ; flen = q.flen + 1 }

let snoc q x =
  { q with rear = x :: q.rear ; rlen = q.rlen + 1 }

let front q =
  match q.front with
    | h :: front -> Some (h, { q with front = front ; flen = q.flen - 1 })
    | _ ->
        match q.rear with
          | [] -> None
          | _ ->
              let front = List.rev q.rear in
              Some (List.hd front, { front = List.tl front ;
                                     flen = q.rlen - 1 ;
                                     rear = [] ;
                                     rlen = 0 })

let rear q =
  match q.rear with
    | t :: rear -> Some ({ q with rear = rear ; rlen = q.rlen - 1 }, t)
    | _ ->
        match q.front with
          | [] -> None
          | _ ->
              let rear = List.rev q.front in
              Some ({ front = [] ; flen = 0 ;
                      rear = List.tl rear ; rlen = q.flen - 1 },
                    List.hd rear)

let rev q = { front = q.rear ; flen = q.rlen ;
              rear = q.front ; rlen = q.flen }

let of_list l = { front = l ; flen = List.length l ;
                  rear = [] ; rlen = 0 }

let null q = size q = 0

let append_rl q r =
  let rec spin rear = function
    | [] -> r.rear @ rear
    | x :: rfront ->
        spin (x :: rear) rfront
  in { q with
         rlen = q.rlen + size r ;
         rear = spin q.rear r.front }

let append_lr q r =
  let rec spin front = function
    | [] -> q.front @ front
    | x :: qrear ->
        spin (x :: front) qrear
  in { r with
         flen = r.flen + size q ;
         front = spin r.front q.rear }

let append q r =
  if size q > size r then
    append_rl q r
  else
    append_lr q r

let append_list q l =
  let n = List.length l in
  let rec spin rear = function
    | [] -> rear
    | x :: l -> spin (x :: rear) l
  in { q with
         rear = spin q.rear l ;
         rlen = q.rlen + n }

let prepend_list l q =
  let n = List.length l in
  { q with
      front = l @ q.front ;
      flen = q.flen + n }

let nth ?(backwards=false) q n =
  (* Return item `n` from `q`.

  Define `m == (size q) - 1`.

  Indexing starts from 0, thus `q` contains
  elements indexed with:

    0, 1, ..., m

  If `backwards=true`, then count from the end,
  so the indexing becomes:

    m, m - 1, ..., 0
  *)
  if n < 0 then failwith "Deque.nth: internal error"
  else if n >= size q then None
  else
    let index = if backwards then size q - n - 1 else n in
    if index < q.flen then Stdlib.List.nth_opt q.front index
    else Stdlib.List.nth_opt q.rear (size q - index - 1)

let first_n q n =
    let length = size q in
    if n < 0 then
        failwith (Printf.sprintf "Deque.first_n:  n = %d < 0" n);
    if n > length then
        failwith (Printf.sprintf "Deque.first_n:  n = %d > size q = %d" n length);
    if n = 0 then empty
    else if n = length then q
    else if n >= q.flen then
        (* The discarded suffix is a prefix of the reversed rear list. *)
        let rec drop count = function
          | xs when count = 0 -> xs
          | _ :: xs -> drop (count - 1) xs
          | [] -> assert false
        in
        { q with rear = drop (length - n) q.rear; rlen = n - q.flen }
    else
        let rec take count = function
          | _ when count = 0 -> []
          | x :: xs -> x :: take (count - 1) xs
          | [] -> assert false
        in
        { empty with front = take n q.front; flen = n }

let iter f q =
  let rec go n xs tail = match xs with
    | [] ->
        if tail <> [] then go n (List.rev tail) []
    | x :: xs ->
        f n x;
        go (n + 1) xs tail
  in
  go 0 q.front q.rear

let map f q =
  let rear = ref [] in
  iter (fun n x -> rear := f n x :: !rear) q;
  { empty with rear = !rear; rlen = size q }

let fold_left fn acc q =
  let acc = List.fold_left fn acc q.front in
  List.fold_left fn acc (List.rev q.rear)

let fold_right fn q acc =
  let step acc x = fn x acc in
  let acc = List.fold_left step acc q.rear in
  List.fold_left step acc (List.rev q.front)

let to_list q =
  match q.rear with
  | [] -> q.front
  | rear -> List.rev_append (List.rev q.front) (List.rev rear)

let find ?(backwards=false) q test =
  let rec spin k f r = match f with
    | [] -> begin match r with
        | [] -> None
        | _ -> spin k (List.rev r) []
      end
    | x :: f ->
        if test x then Some (k, x)
        else spin (k + 1) f r
  in
  if backwards then
    spin 0 q.rear q.front
  else
    spin 0 q.front q.rear

let shared_prefix_length q r =
  if q.front != r.front then 0
  else
    let rec align left left_len right right_len =
      if left_len > right_len then
        align (List.tl left) (left_len - 1) right right_len
      else if right_len > left_len then
        align left left_len (List.tl right) (right_len - 1)
      else if left == right then q.flen + left_len
      else align (List.tl left) (left_len - 1) (List.tl right) (right_len - 1)
    in
    align q.rear q.rlen r.rear r.rlen

let alter ?(backwards=false) q n alt_fn =
  let n = if backwards then size q - n - 1 else n in
  let newq = ref empty in
  let rec spin k q = match front q with
    | None -> invalid_arg "alter"
    | Some (x, q) ->
        if k = n then
          append !newq (cons (alt_fn x) q)
        else begin
          newq := snoc !newq x ;
          spin (k + 1) q
        end
  in
  spin 0 q

(* Compare deques `q1` and `q2`, using `cmp` to compare their elements. *)
let equal cmp q1 q2 =
  let rec diff l1 l2 =
    match l1, l2 with
    | x1 :: ll1, x2 :: ll2 when cmp x1 x2 -> diff ll1 ll2
    | [], _ -> Some l2
    | _, [] -> Some l1
    | _ -> None
  in
  q1.flen + q1.rlen = q2.flen + q2.rlen && begin
    let f = diff q1.front q2.front in
    let r = diff q1.rear q2.rear in
    match f, r with
    | Some lf, Some lr -> List.for_all2 cmp lf (List.rev lr)
    | _, _ -> false
  end

let%test "first_n preserves order across the front and rear lists" =
  let q = snoc (snoc (of_list [1; 2]) 3) 4 in
  let check n expected =
    let prefix = first_n q n in
    let flat = of_list expected in
    to_list prefix = expected && equal (=) prefix flat && equal (=) flat prefix
  in
  check 0 [] && check 1 [1] && check 2 [1; 2] &&
  check 3 [1; 2; 3] && check 4 [1; 2; 3; 4]

let%test_unit "indexing and traversal preserve mixed deque order" =
  let q = snoc (snoc (of_list [1; 2]) 3) 4 in
  let values = [1; 2; 3; 4] in
  let some x = Some x in
  assert (List.init 4 (nth q) = List.map some values);
  assert (List.init 4 (nth ~backwards:true q) = List.map some (List.rev values));
  assert (nth q 4 = None);
  assert (fold_left (fun xs x -> x :: xs) [] q = List.rev values);
  assert (fold_right (fun x xs -> x :: xs) q [] = values);
  let visited = ref [] in
  let mapped = map (fun i x -> visited := i :: !visited; x + i) q in
  assert (!visited = [3; 2; 1; 0]);
  assert (to_list mapped = [1; 3; 5; 7])
