prover quorum=2 ["Alt-Ergo" "Z3"].
timeout 1.  (* limit SMT solvers to two seconds *)
require import AllCore Distr List.


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
op n : int.
axiom _4p : n = 4.

op err : int.
axiom _enz : err <> 0.

op open(m : matrix) =
    (* consistency check? or precondition? *)
    (* add up party 0 shares, then add P1's x0... make this nicer? *)
    m.[0, 1] + m.[0, 2] + m.[0, 3] + m.[1, 0].

(* note: maybe use fset instead of list for party determination? *)

module F4 = {
  var x : matrix

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
        if p = s then 0 else (nth err shares s)), n, n);
  }

  (* parties si and sj know x, and want to send it to party d.
     todo: cheating identification (vs just abort)
   *)
  proc jmp(x : int, si sj : party, d : party) : matrix = {
    (* TODO: party d gets x from si, and H(x) from sj *)
    (* abort if hashes don't check out *)
    var g : int;

    (* compute the excluded party g *)
    var p : int list;
    (* list 0..n *)
    p <- range 0 n;
    (* remove current parties *)
    p <- rem si (rem sj (rem d p));
    g <- head err p;

    return offunm ((fun p s =>
        if p = s then 0 else
        if g = s then x else 0), n, n);
  }

  (* parties i and j know x, and want to share it with the two other
     parties.
   *)
  proc inp(x : int, i j : party) : matrix = {
    var r, xh : int;
    var g, h : party;
    var pgm : matrix;

    (* figure out excluded parties g, h *)
    var p : int list;
    p <- rem i (rem j (range 0 n));
    g <- nth err p 0;
    h <- nth err p 1;

    (* in the paper this is a PRF, but for now model as truly random
       and just don't give it to party g. *)
    r <$ randint;

    xh <- x - r;

    (* Pg learns xh *)
    pgm <@ jmp(xh, i, j, g);

    (* xi = xj = 0, xg = r, xh = x - r *)
    return pgm + offunm ((fun p s => 
      if s = p then 0 else
      if s = g then r else 0), n, n);
  }

  proc mult(x y : matrix) : matrix = {
    var m23, m13, m12, m03, m02, m01, mlocal : matrix;

    (* perform inp on pairs of shares held by both parties.
      for example, both parties 2 and 3 hold x0, x1, y0, y1, so they
      can together compute the term x0y1 * x1y0.
      
      For symmetry we alternate which party we take the share from, but
      the validity check ensures this doesn't actually change the output.
     *)
    m23 <@ inp(x.[0, 1] * y.[1, 0] + x.[1, 0] * y.[0, 1], 2, 3);
    m13 <@ inp(x.[0, 2] * y.[2, 0] + x.[2, 0] * y.[0, 2], 1, 3);
    m12 <@ inp(x.[0, 3] * y.[3, 0] + x.[3, 0] * y.[0, 3], 1, 2);
    m03 <@ inp(x.[1, 2] * y.[2, 1] + x.[2, 1] * y.[1, 2], 0, 3);
    m02 <@ inp(x.[1, 3] * y.[3, 1] + x.[3, 1] * y.[1, 3], 0, 2);
    m01 <@ inp(x.[2, 3] * y.[3, 2] + x.[3, 2] * y.[2, 3], 0, 1);

    (* elementwise multiplication to create sharing of x_i * y_i
       this implements inp_local: no communication occurs *)
    mlocal <- x * y;

    (* elementwise addition *)
    return m01 + m02 + m03 + m12 + m13 + m23 + mlocal;   
  }

  proc mult_main(x y : int) : int = {
    var z : int;
    var mx, my, mz : matrix;

    (* assume P0 holds x and P1 holds y *)
    mx <@ share(x, 0);
    my <@ share(y, 1);

    mz <@ mult(mx, my);

    z <- open(mz);

    return z;
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
    0 <= i < size shares /\ size shares = n /\ nth err shares i = 0  => sumz (put shares i x) = x + sumz shares.
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
    hoare[F4.share : x = x_ /\ p = p_ /\ 0 <= p < n ==> open res = x_].
proof.
proc.
inline*.
sp.
seq 6 : (x = x_
  /\ 0 <= p < n
  /\ size shares = n
  /\ nth err shares p = 0).
auto; progress.
rewrite size_put; smt(_4p).
rewrite nth_put; smt(_4p).
seq 1 : (
  s_ = x - sumz shares
  /\ x = x_ 
  /\ size shares = n
  /\ 0 <= p < n
  /\ nth err shares p = 0).
auto; progress.
seq 1 : (sumz shares = x_
  /\ x = x_
  /\ size shares = n).
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
have n4 : n = 4 by rewrite _4p.
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

lemma excluded_party (i j : int) :
    exists(a, b : int),  a < b /\ a <> i /\ b <> j /\ 0 <= i < j < n 
      => (rem i (rem j (range 0 n))) = [a; b].
proof.
rewrite _4p.
(* i = 0 *)
case (i = 0).
case (j = 1); progress.
exists 2 3.
rewrite /= range_ltn // range_ltn // range_ltn // rangeS //.
case (j = 2); progress.
exists 1 3.
rewrite /= range_ltn // range_ltn // range_ltn // rangeS //.
exists 1 2.
rewrite /= range_ltn // range_ltn // range_ltn // rangeS.
progress.
have // : j = 3 by smt().
(* i = 1 *)
case (i = 1).
case (j = 2); progress.
exists 0 3.
rewrite /= range_ltn // range_ltn // range_ltn // rangeS //.
exists 0 2.
rewrite /= range_ltn // range_ltn // range_ltn // rangeS //.
progress.
have // : j = 3 by smt().
(* i = 2 *)
progress.
exists 0 1.
rewrite /= range_ltn // range_ltn // range_ltn // rangeS //.
progress.
have // : i = 2 /\ j = 3 by smt().
qed.

(* Prove multiplication is correct *)
lemma mul_correct(x_ y_ : int) :
    hoare[F4.mult_main : x = x_ /\ y = y_ ==> res = x_ * y_].
proof.
proc.
have n4 : n = 4 by rewrite _4p.
seq 1 : (open mx = x_ /\ y = y_).
auto.
call (share_correct x_ 0).
auto; smt().
seq 1 : (open mx = x_ /\ open my = y_).
auto.
call (share_correct y_ 1).
auto; smt().
inline F4.mult.
wp; sp.
seq 1 : (open m23 = mx.[0, 1] * my.[1, 0] + mx.[1, 0] * my.[0, 1]).
inline F4.inp.
seq 6 : (x1 = mx.[0, 1] * my.[1, 0] + mx.[1, 0] * my.[0, 1]
  /\ i = 2 /\ j = 3 /\ g = 0 /\ h = 1).
auto.
progress.
rewrite n4.
have : rem 2 (rem 3 (range 0 4)) = [0; 1].
rewrite (excluded_party 2 3).

qed.

