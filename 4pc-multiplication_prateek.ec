
prover quorum=2 ["Alt-Ergo" "Z3"].
timeout 1.  (* limit SMT solvers to two seconds *)
require import AllCore Distr List FSet.

require (*---*) DynMatrix.


clone DynMatrix as Mat_A with
type ZR.t <- int,
op ZR.zeror  <- 0,
op ZR.oner   <- 1,
op ZR.( + )  <- Top.Int.( + ),
op ZR.([-])  <- Top.Int.([-]),
op ZR.( * )  <- Top.Int.( * )

proof ZR.addrA by exact addrA,
ZR.addrC by exact addrC,
ZR.add0r by exact add0r,
ZR.addNr by exact addNr,
ZR.oner_neq0 by exact oner_neq0,
ZR.mulrA by exact mulrA,
ZR.mulrC by exact mulrC,
ZR.mul1r by exact mul1r,
ZR.mulrDl by exact mulrDl.

type party = int.

import Mat_A.Matrices.

op randint : int distr.

(* WARNING: matrices are zero indexed, so we need to have share 0, party 0 *)

(* matrix semantics are [party, share] *)

(* We have four parties. *)
op N : int.
axiom _4p : N = 4.

op err : int.
axiom _enz : err <> 0.

op open(m : matrix) =
    (* consistency check? or precondition? *)
    (* add up party 0 shares, then add P1's x0... make this nicer? *)
    m.[0, 1] + m.[0, 2] + m.[0, 3] + m.[1, 0].

(* Function to sum all elements of a matrix *)
op sum_matrix (m : matrix) =
   m.[0, 1] + m.[0, 2] + m.[0, 3] + m.[1, 0] + m.[1, 2] + m.[1, 3] + m.[2, 0] + m.[2, 1] + m.[2, 3] + m.[3, 0] + m.[3, 1] + m.[3, 2].
   

(* note: maybe use fset instead of list for party determination? *)

module F4 = {
  (* p has a value x and wants to share it with all other parties *)
  proc share(x p : int) : matrix = {
    var s0, s1, s2, s_, s3 : int;

    var shares : int list;

    (* generate random *)
    s0 <$ randint;
    s1 <$ randint;
    s2 <$ randint;
    s3 <$ randint;
    shares <- [s0; s1; s2; s3];

    (* zero out the p'th share *)
    shares <- put shares p 0;

    (* and set it such that the new sum equals x *)
    s_ <- x - sumz(shares);
    shares <- put shares p s_;

    (* TODO: think about if we should use vector here instead of list *)
    (* TODO: basically every `offunm` call is going to have the structure
        if p = s then 0 else ...
       maybe we can factor that out?
     *)
    return offunm ((fun p s =>
        if p = s then 0 else (nth err shares s)), N, N);
  }

  (* parties si and sj know x, and want to send it to party d.
     todo: cheating identification (vs just abort)
   *)
  proc jmp(x : int, si sj : party, d : party) : matrix = {
    (* TODO: party d gets x from si, and H(x) from sj *)
    (* abort if hashes don't check out *)
    var g : int;
    (* compute the excluded party g *)
    var p : party fset;
    p <- oflist [0;1;2;3];
(*
    (* remove current parties *)
    g <- pick ((rangeset 0 N) `\` oflist [si; sj; d]);
*)
    g <- pick (p `\` oflist [si; sj; d]);

    return offunm ((fun p s =>
        if p = s then 0 else
        if g = s then x else 0), N, N);
    
      (*FOR CHEATING IDENTIFICATION: Model H as a random oracle and have a map to save the value for x.
      When g checks the value for x if x is in the map then return the same value 
      otherwise return a new value*)

  }


  (* parties i and j know x, and want to share it with the two other
     parties.
   *)
  proc inp(x : int, i j : party) : matrix = {
    var r, xh : int;
    var g, h : party;
    var pgm : matrix;

    (* figure out excluded parties g, h *)
    var p : party fset;
    p <- (rangeset 0 N) `\` oflist [i; j];
    g <- nth err (elems p) 0;
    h <- nth err (elems p) 1;

    (* in the paper this is a PRF, but for now model as truly random
       and just don't give it to party g. *)
    r <$ randint;

    xh <- x - r;

    (* Pg learns xh *)
    pgm <@ jmp(xh, i, j, g);

    (* xi = xj = 0, xg = r, xh = x - r *)
    return pgm + offunm ((fun p s => 
      if s = p then 0 else
      if s = g then r else 0), N, N);
  }

  (* Hadamard product of mx and my to create mlocal 
      *)

  proc elem_mult(mx, my: matrix): matrix = {
    var mz: matrix;
    var r0, c0, elem: int;
    r0 <- 0;
    c0 <- 0;
    mz <- matrixc N N 0;
    while (r0 < rows mz) {
      while (c0 < cols mz) {
        elem <- mx.[r0, c0]*my.[r0, c0];
        mz <- updm mz r0 c0 elem;
        c0 <- c0 + 1;
      }
      r0 <- r0 + 1;
    }
    return mz;
  }


  proc mult(mx my : matrix) : matrix = {
    var m23, m13, m12, m03, m02, m01, mlocal : matrix;
(* perform inp on pairs of shares held by both parties.
      for example, both parties 2 and 3 hold x0, x1, y0, y1, so they
      can together compute the term x0y1 * x1y0.
      
      For symmetry we alternate which party we take the share from, but
      the validity check ensures this doesn't actually change the output.
     *)
    m23 <@ inp(mx.[0, 1] * my.[1, 0] + mx.[1, 0] * my.[0, 1], 2, 3);
    m13 <@ inp(mx.[0, 2] * my.[2, 0] + mx.[2, 0] * my.[0, 2], 1, 3);
    m12 <@ inp(mx.[0, 3] * my.[3, 0] + mx.[3, 0] * my.[0, 3], 1, 2);
    m03 <@ inp(mx.[1, 2] * my.[2, 1] + mx.[2, 1] * my.[1, 2], 0, 3);
    m02 <@ inp(mx.[1, 3] * my.[3, 1] + mx.[3, 1] * my.[1, 3], 0, 2);
    m01 <@ inp(mx.[2, 3] * my.[3, 2] + mx.[3, 2] * my.[2, 3], 0, 1);

    (* elementwise multiplication to create sharing of x_i * y_i
       this implements inp_local: no communication occurs *)
    
    mlocal <@ elem_mult(mx, my);

    (* elementwise addition *)
    return m01 + m02 + m03 + m12 + m13 + m23 + mlocal;   
  }

  proc mult_main(x y : int) : matrix = {
    var z : int;
    var mx, my, mz : matrix;

    (* assume P0 holds x and P1 holds y *)
    mx <@ share(x, 0);
    my <@ share(y, 1);

    mz <@ mult(mx, my);

    return mz;
  }

  proc add_main(x y : int) : int = {
    var mx, my, mz : matrix;
    var z : int;

    (* party 0 has x *)
    mx <@ share(x, 0);
    (* party 1 has y *)
    my <@ share(y, 1);

    (* addition is local *)
    mz <- mx + my;

    z <- open(mz);
    return z;
  }
}.


(* sum of four element list is the sum of the individual elements *)
lemma sum_four(s : int list) :
    size s = 4 => sumz s = 
    nth err s 0 + nth err s 1 + nth err s 2 + nth err s 3.
proof.
progress.
rewrite /sumz -{1}take_size H.
have T4 : take 4 s = rcons (take 3 s) (nth err s 3).
  rewrite -take_nth.
  rewrite H // take_nth.
  by simplify.
have T3 : take 3 s = rcons (take 2 s) (nth err s 2).
  rewrite -take_nth.
  rewrite H // take_nth.
  by simplify.
have T2 : take 2 s = rcons (take 1 s) (nth err s 1).
  rewrite -take_nth.
  rewrite H // take_nth.
  by simplify.
have T1 : take 1 s = rcons (take 0 s) (nth err s 0).
  rewrite -take_nth.
  rewrite H // take_nth.
  by simplify.
rewrite T4 T3 T2 T1 take0.
smt().
qed.

(* replacing zero value in list with `x` increases the sum by `x` *)
lemma sum_replacement(shares : int list, i x : int) :
    0 <= i < size shares /\ size shares = N /\ nth err shares i = 0  => sumz (put shares i x) = x + sumz shares.
proof.
progress.
rewrite _4p in H1.
rewrite (sum_four shares) //.
rewrite (sum_four (put shares i x)).
by rewrite size_put.
rewrite nth_put.
smt().
rewrite nth_put.
smt().
rewrite nth_put.
smt().
rewrite nth_put.
smt().
smt().
qed.

(* Prove correctness of the sharing scheme. *)
lemma share_correct(x_ p_ : int) :
    hoare[F4.share : x = x_ /\ p = p_ /\ 0 <= p < N ==> open res = x_].
proof.

proc.
seq 6 : (x = x_
  /\ 0 <= p < N
  /\ size shares = N
  /\ nth err shares p = 0).
auto; progress.
rewrite size_put; smt(_4p).
rewrite nth_put; smt(_4p).
seq 1 : (
  s_ = x - sumz shares
  /\ x = x_ 
  /\ size shares = N
  /\ 0 <= p < N
  /\ nth err shares p = 0).
auto; progress.
seq 1 : (sumz shares = x_
  /\ x = x_
  /\ size shares = N).
auto; progress.
(* sum = x *)
rewrite (sum_replacement shares{hr} p{hr} (x{hr} - sumz shares{hr})).
by rewrite H0 H2 H H1 /= // _enz.
smt().
rewrite size_put //.
(* matrix part *)
auto. progress.
rewrite /open get_offunm.
rewrite rows_offunm cols_offunm => /=; smt(_4p).
rewrite get_offunm.
rewrite rows_offunm cols_offunm => /=; smt(_4p).
rewrite get_offunm.
rewrite rows_offunm cols_offunm => /=; smt(_4p).
rewrite get_offunm.
rewrite rows_offunm cols_offunm => /=; smt(_4p).


simplify.

(* sum is correct *)
rewrite _4p in H.
rewrite (sum_four shares{hr}) // /#.
qed.

(* Prove the sharing scheme is secure. *)

(* need lemma valid shares *)

(* Prove addition is correct *)
lemma add_correct(x_ y_ : int) :
    hoare[F4.add_main : x = x_ /\ y = y_ ==> res = x_ + y_].
proof.
proc.
have n4 : N = 4 by rewrite _4p.
seq 1 : (open mx = x_ /\ y = y_).
auto.
call (share_correct x_ 0).
auto; smt().
seq 1 : (open my = y_ /\ open mx = x_).
call (share_correct y_ 1).
auto; progress.
smt().
auto.
progress.
by rewrite /open 4!get_addm /#.
qed.

lemma range4 :
    range 0 4 = [0; 1; 2; 3].
proof.
by rewrite range_ltn // range_ltn // range_ltn // rangeS.
qed.

lemma excluded_party (i j : int) :
    exists(a, b : int),  a < b /\ a <> i /\ b <> j /\ 0 <= i < j < N 
      => (rem i (rem j (range 0 N))) = [a; b].
proof.
rewrite _4p.
(* i = 0 *)
case (i = 0).
case (j = 1); progress.
exists 2 3.
by rewrite range4.
case (j = 2); progress.
exists 1 3.
by rewrite range4.
exists 1 2.
rewrite range4 /=.
progress.
have // : j = 3 by smt().
(* i = 1 *)
case (i = 1).
case (j = 2); progress.
exists 0 3.
by rewrite range4.
exists 0 2.
rewrite range4 /=.
progress.
have // : j = 3 by smt().
(* i = 2 *)
progress.
exists 0 1.
rewrite range4 /=.
progress.
have // : i = 2 /\ j = 3 by smt().
qed.

lemma pick_nonmem (s : party fset) :
    forall k, k \in s => pick (rangeset 0 N `\` s) <> k.
proof.
admit.
qed.
(*progress.
rewrite /pick.
rewrite /(`\`).
rewrite /rangeset.
have : uniq (range 0 n).
  by rewrite range_uniq.
progress.
rewrite oflist_uniq in H0.*)

lemma offunm_unwrap (i, j : int, f : int -> int -> int):
    0 <= i < N /\ 0 <= j < N => (offunm (fun(x y) => f x y, N, N)).[i, j] = f i j.
proof.
progress.
rewrite get_offunm.
rewrite rows_offunm cols_offunm H H1 /=.
move : H0 H2.
by rewrite _4p.
by simplify.
qed.


lemma nth_set (i : int, s : int list) :
  uniq s => nth err (elems (oflist s)) i = nth err s i.
proof.
admit.
qed.



(* Prove correctness of the jmp scheme. *)
lemma jmp_correct(x_ : int) :
    hoare[F4.jmp : x = x_ /\ si = 0 /\ sj = 1 /\ d = 2 ==> open res = x_].
proof.
proc.
auto => />.
rewrite _4p.

rewrite /open.
rewrite get_offunm.
rewrite rows_offunm cols_offunm => /=; smt(_4p).
rewrite get_offunm.
rewrite rows_offunm cols_offunm => /=; smt(_4p).
rewrite get_offunm.
rewrite rows_offunm cols_offunm => /=; smt(_4p).
rewrite get_offunm.
rewrite rows_offunm cols_offunm => /=; smt(_4p).
simplify.


(*
rewrite elemsK.
rewrite in_fsetD.

simplify.
rewrite -in_eq_fset0.


rewrite /offunm_unwrap.


simplify.
rewrite /pick.
rewrite -pick_nonmem.
*)





qed.

































(* Prove multiplication is correct *)
lemma mul_correct(x_ y_ : int) :
    hoare[F4.mult_main : x = x_ /\ y = y_ ==> open res = x_ * y_].
proof.
proc.
have n4 : N = 4 by rewrite _4p.

seq 1 : (open mx = x_ /\ y = y_).
auto.
call (share_correct x_ 0).
auto; smt().
seq 1 : (open mx = x_ /\ open my = y_).
call (share_correct y_ 1).
auto; smt().
inline F4.mult.

wp; sp.

seq 1 : (open m23 = mx.[0, 1] * my.[1, 0] + mx.[1, 0] * my.[0, 1]).
inline F4.inp.
auto.

seq 4 : (x1 = mx.[0,1]*my.[1,0] + mx.[1,0]*my.[0,1] /\ i = 2 /\ j = 3 /\ p = oflist [0; 1]).
auto.
progress.
rewrite n4.
rewrite /rangeset.
rewrite range4.
by rewrite (oflist_cat [0; 1] [2; 3] [0; 1; 2; 3]).

seq 2 : (x1 = mx.[0,1]*my.[1,0] + mx.[1,0]*my.[0,1] /\ i = 2 /\ j = 3 /\ g = 0 /\ h = 1).
auto.
progress.
by rewrite nth_set.
by rewrite nth_set.

seq 2 : (xh = x1 - r /\ i = 2 /\ j = 3 /\ g = 0 /\ h = 1); auto.
inline F4.jmp.
auto; progress.
rewrite /open n4 /rangeset range4.
rewrite (oflist_cat [1] [2; 3; 0] [0; 1; 2; 3])
rewrite get_offunm.
rewrite rows_offunm cols_offunm => /#.
simplify.

rewrite (offunm_unwrap 0 1 (fun (p1 s : int) =>
      if p1 = s then 0
      else
        if pick (rangeset 0 4 `\` oflist [2; 3; 0]) = s then
          (x1{hr} - r{hr})%Mat_A.ZR
        else 0)).
rewrite get_offunm.
rewrite rows_offunm cols_offunm => /#.
simplify.
rewrite get_offunm.
rewrite rows_offunm cols_offunm => /#.
simplify.
rewrite get_offunm.
rewrite rows_offunm cols_offunm => /#.
simplify.
rewrite get_offunm.
rewrite rows_offunm cols_offunm => /#.
simplify.
rewrite get_offunm.
rewrite rows_offunm cols_offunm => /#.
simplify.
rewrite get_offunm.
rewrite rows_offunm cols_offunm => /#.
simplify.
rewrite get_offunm.
rewrite rows_offunm cols_offunm => /#.
simplify.
rewrite get_offunm.
rewrite rows_offunm cols_offunm => /#.
simplify.
rewrite get_offunm.
rewrite rows_offunm cols_offunm => /#.
simplify.
rewrite get_offunm.
rewrite rows_offunm cols_offunm => /#.
simplify.
rewrite get_offunm.
rewrite rows_offunm cols_offunm => /#.
simplify.

rewrite pick_nonmem.
have no1 : 1 \notin oflist [2; 3; 0].
rewrite (mem_oflist).
smt().

rewrite rem23 /=.
smt().

qed.

