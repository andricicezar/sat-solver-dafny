module Fstar_Perm 

#set-options "--use_two_phase_tc true"

open FStar.HyperStack.ST

module S = FStar.Seq
module B = LowStar.Buffer
module M = LowStar.Modifies
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

open LowStar.BufferOps

let n = 11ul

let arr: b:B.buffer FStar.UInt32.t =
  B.gcmalloc HS.root 0ul n

let vis: b:B.buffer bool =
  B.gcmalloc HS.root false n

let rec generate (i : U32.t) : Stack unit
  (requires fun h0 ->
    let l_arr = M.loc_buffer arr in
    let l_vis = M.loc_buffer vis in
    B.live h0 arr /\ B.live h0 vis /\
    U32.lte i n /\
    B.length arr = n /\
    B.length vis = n /\
    M.loc_disjoint l_arr l_vis)
  (ensures fun h0 () h1 ->
    let l_arr = M.loc_buffer arr in
    let l_vis = M.loc_buffer vis in
    B.live h1 arr /\
    B.live h1 vis /\
    M.(modifies l_arr h0 h1) /\
    M.(modifies l_vis h0 h1)) =

  let h0 = ST.get() in
  if i = n then ()
  else begin
    let inv h (i: nat) =
      B.live h arr /\ B.live h vis /\
      // M.(modifies (loc_buffer vis) h0 h) /\
      // M.(modifies (loc_buffer vis) h0 h) /\
      i <= U32.v n
    in
    let body (j: U32.t{ U32.lte 0ul j /\ U32.lt j n }): Stack unit
        (requires (fun h -> inv h (U32.v j)))
        (ensures (fun h0 () h1 -> inv h0 (U32.v j) /\ inv h1 (U32.v (U32.add j 1ul))))
    =
        let open B in
        if vis.(j) = false then begin
          vis.(j) <- true;
          arr.(i) <- j;
          generate (U32.add i 1ul);
          arr.(i) <- 0ul;
          vis.(j) <- false 
        end
    in
    C.Loops.for 0ul n inv body
  end

let main (): Stack C.exit_code
  (requires fun _ -> True)
  (ensures fun h _ h' -> M.modifies M.loc_none h h')
=
  push_frame ();

  generate 0ul;

  pop_frame ();
  C.EXIT_SUCCESS
