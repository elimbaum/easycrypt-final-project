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
import Mat_A.Vectors.

op randint : int distr.
axiom randint_ll : is_lossless randint.

(* bitwidth of int *)
op L : int.
axiom ge0_L : 0 <= L.

axiom randint1E (x : int) :
  mu1 randint x = 1%r / (2 ^ L)%r.

(* from SMC example in class *)
lemma rantint_full : is_full randint.
proof.
move => x.
rewrite /support randint1E.
by rewrite RField.div1r StdOrder.RealOrder.invr_gt0 lt_fromint StdOrder.IntOrder.expr_gt0.
qed.

(* WARNING: matrices are zero indexed, so we need to have share 0, party 0 *)

(* matrix semantics are [party, share] *)

(* We have four parties. *)
op N : int.
axiom _4p : N = 4.

(* An unspecified non-zero error value *)
op err : int.
axiom _enz : err <> 0.

op open(m : matrix) =
    (* consistency check? or precondition? *)
    (* add up party 0 shares, then add P1's x0... make this nicer? *)
    m.[0, 1] + m.[0, 2] + m.[0, 3] + m.[1, 0].

(* note: maybe use fset instead of list for party determination? *)

op view(m : matrix, p : party) =
  row m p.

module Sim = {
  (* simulator ignores x and p and just returns a random sharing
     we will argue that all rows of the matrix (parties' views)
     are indistinguishable. *)
  proc share(x : int, p : party) : matrix = {
    var s0, s1, s2, s3 : int;
    var shares : int list;

    (* generate random *)
    s0 <$ randint;
    s1 <$ randint;
    s2 <$ randint;
    s3 <$ randint;

    shares <- [s0; s1; s2; s3];

    return offunm ((fun p_ s =>
        if p_ = s then 0 else (nth err shares s)), N, N);
  }
}.

module F4 = {
  (* p has a value x and wants to share it with all other parties *)
  proc share(x : int, p : party) : matrix = {
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
        if p_ = s then 0 else ...
       maybe we can factor that out?
     *)
    return offunm ((fun p_ s =>
        if p_ = s then 0 else (nth err shares s)), N, N);
  }

  (* parties si and sj know x, and want to send it to party d.
     todo: cheating identification (vs just abort)
   *)
  proc jmp(x : int, si sj : party, d : party, g:party) : matrix = {
    (* TODO: party d gets x from si, and H(x) from sj *)
    (* abort if hashes don't check out *)
    (*var g : int;

    (* compute the excluded party g *)
    var p : party fset; *)
    (* remove current parties *)
    var a, b: party fset;
    var m: matrix;
    a <-  Top.FSet.oflist [si; sj; d];
    b <-  Top.FSet.oflist [g];
    g <- pick ( b `|` a `\` a);
    return offunm ((fun p s =>
        if p = s then 0 else
        if g = s && 0<=g && g<=3 then x else 0), N, N);

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
    p <- (rangeset 0 N) `\` Top.FSet.oflist [i; j];
    g <- nth err (elems p) 0;
    h <- nth err (elems p) 1;

    (* in the paper this is a PRF, but for now model as truly random
       and just don't give it to party g. *)
    r <$ randint;

    xh <- x - r;

    (* Pg learns xh *)
    pgm <@ jmp(xh, i, j, g, h);

    (* xi = xj = 0, xg = r, xh = x - r *)
    return pgm + offunm ((fun p s => 
      if s = p then 0 else
      if s = g then r else 0), N, N);
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
lemma share_correct(x_ : int, p_ : party) :
    hoare[F4.share: x = x_ /\ p = p_ /\ 0 <= p_ < N ==> open res = x_].
proof.
proc.
seq 6 : (x = x_ /\ p = p_ /\ 0 <= p_ < N
  /\ size shares = N
  /\ nth err shares p_ = 0).
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
lemma share_secure(p_ : party) :
    equiv[F4.share ~ Sim.share :
      ={p} /\ p{1} = p_ /\ 0 <= p_ < N
      ==>
      view res{1} p_ = view res{2} p_].
proof.
proc.
(* si are all random *)
seq 5 5 : (={p} /\ p{1} = p_ /\
  s0{1} \in randint /\ ={s0} /\
  s1{1} \in randint /\ ={s1} /\
  s2{1} \in randint /\ ={s2} /\
  s3{1} \in randint /\ ={s3} /\
  0 <= p_ < N /\
  size shares{2} = 4 /\ ={shares}
).
auto.
progress.
auto.
progress.
rewrite _4p in H4.
(* rewrite matrices *)
rewrite put_in.
by rewrite size_put H5.
(* convert view of matrix to vector *)
rewrite /view /row.
rewrite 2!cols_offunm _4p lez_maxr //.
rewrite eq_vectorP.
rewrite 2!size_offunv lez_maxr // /=.
move => i i_bounded.
rewrite get_offunv // get_offunv //.
(* evaluate function calls *)
simplify.
(* convert back to matrix *)
rewrite get_offunm.
rewrite rows_offunm lez_maxr // cols_offunm lez_maxr //.
rewrite get_offunm.
rewrite rows_offunm lez_maxr // cols_offunm lez_maxr //.
progress.
(* trivial when p = i => diagonal, so zero *)
case (p{2} = i) => [// | off_diag].
(* off diagonal: shares are indistinguishable *)
rewrite nth_cat.
rewrite size_take //.
rewrite size_put.
rewrite H5 H4 /=.
(* one side of diagonal *)
case (p{2} < i) => [plti | pgteqi].
have inltp : !(i < p{2}).
  smt().
rewrite inltp /=.
rewrite nth_drop.
smt().
smt().
have ip2n0 : i - p{2} <> 0.
  smt().
rewrite ip2n0 /=.
rewrite nth_put.
by rewrite H5 H3 H4.
have simp_mat_add : i = p{2} + 1 + (i - p{2} - 1)%Mat_A.ZR.
  smt(addrA addrC).
by rewrite -simp_mat_add off_diag /=.
(* other side of diagonal *)
have iltp : i < p{2}.
  smt().
rewrite iltp /=.
rewrite nth_take.
rewrite H3.
rewrite iltp.
rewrite nth_put.
rewrite H3 H5 H4 //.
rewrite off_diag //.
qed.

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

(* lemma pick_nonmem (s : party fset) :
    forall k, k \in s => pick (rangeset 0 N `\` s) <> k.
proof.
admit.
qed.
( *progress.
rewrite /pick.
rewrite /(`\`).
rewrite /rangeset.
have : uniq (range 0 n).
  by rewrite range_uniq.
progress.
rewrite oflist_uniq in H0.


lemma nth_set (i : int, s : int list) :
  uniq s => nth err (elems (oflist s)) i = nth err s i.
proof.
admit.
qed.

lemma oflist_cat (a b c : int list) :
    a ++ b = c => oflist c `\` oflist b = oflist a.
proof.
admit.
qed.

*)

lemma fsetUD (A B: party fset) : A `|` B `\` B = A.
proof.
apply/fsetP => x.
by rewrite fsetDv fsetUC fset0U.
qed.


lemma pick1(x: int): pick( Top.FSet.oflist [x]) = x.
proof. 
admit.
qed.


(* Prove correctness of the jmp. *)
lemma jmp_correct(x_ si_ sj_ d_ g_: party) :
    hoare[F4.jmp : x = x_ /\ si = si_ /\ sj = sj_ /\ d = d_ /\ g = g_ /\ 0<=g_ /\ g<=3 ==> open res = x_].
proof.
proc.
auto => />.
progress.
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
rewrite fsetUD.
rewrite pick1.
smt(sum_four).
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
auto.
call (share_correct y_ 1).
auto; smt().
wp.
inline F4.mult.
wp; sp.

seq 1 : (open m23 = mx.[0, 1] * my.[1, 0] + mx.[1, 0] * my.[0, 1]).
inline F4.inp.

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
rewrite get_offunm.
rewrite rows_offunm cols_offunm => /#.
simplify.


have no1 : 1 \notin oflist [2; 3; 0].
rewrite (mem_oflist).
smt().

rewrite rem23 /=.
smt().

qed.

