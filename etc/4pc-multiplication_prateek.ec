prover quorum=2 ["Alt-Ergo" "Z3"].
timeout 1.  (* limit SMT solvers to two seconds *)
require import AllCore FSet List Distr.
require import Bool IntDiv.
require import Number StdOrder.
(*---*) import RealOrder. 

require import ZModP. 
clone import ZModField as Zmod.
(*
import Zmod.Sub.
import Zmod.ZModule.
import Zmod.ComRing.*)

import Zmod.Sub.
import Zmod.ZModule.

type zmod = Zmod.zmod.

require (*---*) DynMatrix.
(*

clone DynMatrix as Mat_A with
type ZR.t <- Zmod.zmod,
pred ZR.unit   <- Zmod.unit,
op ZR.zeror  <- Zmod.zero,
op ZR.oner   <- Zmod.one,
op ZR.( + )  <- Zmod.( + ),
op ZR.([-])  <- Zmod.([-]),
op ZR.( * )  <- Zmod.( * ),
op ZR.invr   <- Zmod.inv,
op ZR.exp    <- Zmod.exp

proof ZR.addrA by exact Zmod.ZModpField.addrA,
ZR.addrC by exact Zmod.ZModpField.addrC,
ZR.add0r by exact Zmod.ZModpField.add0r,
ZR.addNr by exact Zmod.ZModpField.addNr,
ZR.oner_neq0 by exact Zmod.ZModpField.oner_neq0,
ZR.mulrA by exact Zmod.ZModpField.mulrA,
ZR.mulrC by exact Zmod.ZModpField.mulrC,
ZR.mul1r by exact Zmod.ZModpField.mul1r,
ZR.mulrDl by exact Zmod.ZModpField.mulrDl,
ZR.mulVr by exact Zmod.ZModpRing.mulVr,
ZR.mulrV by exact Zmod.ZModpRing.mulrV,
ZR.unitP by exact Zmod.ZModpRing.unitP,
ZR.unitout by exact Zmod.ZModpRing.unitout,
ZR.expr0 by exact Zmod.ZModpRing.expr0,
ZR.exprS by exact Zmod.ZModpRing.exprS,
ZR.exprN by exact Zmod.ZModpRing.exprN.
*)

clone DynMatrix as Mat_A with
type ZR.t <- Zmod.zmod,
op ZR.zeror  <- Zmod.zero,
op ZR.oner   <- Zmod.one,
op ZR.( + )  <- Zmod.( + ),
op ZR.([-])  <- Zmod.([-]),
op ZR.( * )  <- Zmod.( * )

proof ZR.addrA by exact Zmod.ZModpRing.addrA,
ZR.addrC by exact Zmod.ZModpRing.addrC,
ZR.add0r by exact Zmod.ZModpRing.add0r,
ZR.addNr by exact Zmod.ZModpRing.addNr,
ZR.oner_neq0 by exact Zmod.ZModpRing.oner_neq0,
ZR.mulrA by exact Zmod.ZModpRing.mulrA,
ZR.mulrC by exact Zmod.ZModpRing.mulrC,
ZR.mul1r by exact Zmod.ZModpRing.mul1r,
ZR.mulrDl by exact Zmod.ZModpRing.mulrDl.



type party = int.

import M.Matrices.
import M.Vectors.

op randint : int distr.
axiom randint_ll : is_lossless randint.

(* bitwidth of int *)
op L : int.
axiom ge0_L : 0 <= L.

axiom randint1E (x : int) :
  mu1 randint x = 1%r / (2 ^ L)%r.

(* from SMC example in class *)
lemma randint_full : is_full randint.
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


lemma open_linear(mx my : matrix):
    open (mx + my) = open mx + open my.
proof.
rewrite /open.
rewrite 4!get_addm.
rewrite !addrA.
smt(addrC addrA).
qed.




op valid(m : matrix) =
   (* matrix is NxN *)
   size m = (N, N)
   (* diagonal is zero *)
   /\ (forall (a : int), mrange m a a => m.[a, a] = 0)
   (* off diagonal, each column identical for all parties *)
   /\ (forall s, forall p, mrange m p s /\ p <> s /\ s = 0 => 
          (* for share 0, all shares equal to party 1's *)
           m.[p, s] = m.[1, s])
   /\ (forall s, forall p, mrange m p s /\ p <> s /\ s <> 0 => 
          (* for all other shares, equal to party 0's *)
           m.[p, s] = m.[0, s]).

op view(m : matrix, p : party) =
  row m p.

module Sim = {
  (* simulator ignores x and p and just returns a random sharing
     we will argue that all rows of the matrix (parties' views)
     are indistinguishable. *)
  proc share(x : int) : matrix = {
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

  proc add(x y : int, i j : party) : matrix = {
    var mx, my : matrix;
    var rx, ry : int;

    rx <$ randint;
    ry <$ randint;

    mx <@ share(rx);
    my <@ share(ry);
    return mx + my;
  }
}.

module F4 = {
  
  (* dealer has value x and wants to share it with all other parties *)
  proc share(x : int) : matrix = {
    var s0, s1, s2, s3, s_ : int;

    var shares : int list;

    (* generate random *)
    s0 <$ randint;
    s1 <$ randint;
    s2 <$ randint;
    s3 <$ randint;
    shares <- [s0; s1; s2; s3];

    (* set last share such that the new sum equals x *)
    s_ <- x - sumz(shares) + s3;
    shares <- put shares 3 s_;

    (* TODO: basically every `offunm` call is going to have the structure
        if p_ = s then 0 else ...
       maybe we can factor that out?
     *)
    return offunm ((fun p_ s =>
        if p_ = s then 0 else (nth err shares s)), N, N);
  }

  (* parties si and sj know x, and want to send it to party d.
     g is exlcuded.
     todo: cheating identification (vs just abort)

   *)
  proc jmp(x : int, si sj d g  :party) : matrix = {
    (* TODO: party d gets x from si, and H(x) from sj *)
    (* abort if hashes don't check out *)
    var mjmp : matrix;

    mjmp <- offunm ((fun p s =>
        if p = s then 0 else
        if g = s then x else 0), N, N);
    return mjmp;
  }

  (* parties i and j know x, and want to share it with the two other
     parties g and h.
   *)
  proc inp(x : int, i j g h : party) : matrix = {
    var r, xh : int;
    var pgm, minp : matrix;

    (* in the paper this is a PRF, but for now model as truly random
       and just don't give it to party g. *)
    r <$ randint;

    xh <- x - r;

    (* Pg learns xh *)
    pgm <@ jmp(xh, i, j, g, h);

    (* xi = xj = 0, xg = r, xh = x - r *)
    minp <- pgm + offunm ((fun p s => 
      if s = p then 0 else
      if s = h then r else 0), N, N);
    return minp;
  }

  proc mult(x y : matrix) : matrix = {
    var m23, m13, m12, m03, m02, m01, mlocal : matrix;

    (* perform inp on pairs of shares held by both parties.
      for example, both parties 2 and 3 hold x0, x1, y0, y1, so they
      can together compute the term x0y1 * x1y0.
      
      For symmetry we alternate which party we take the share from, but
      the validity check ensures this doesn't actually change the output.
     *)
    m23 <@ inp(x.[0, 1] * y.[1, 0] + x.[1, 0] * y.[0, 1], 2, 3, 0, 1);
    m13 <@ inp(x.[0, 2] * y.[1, 0] + x.[1, 0] * y.[0, 2], 1, 3, 0, 2);
    m12 <@ inp(x.[0, 3] * y.[1, 0] + x.[1, 0] * y.[0, 3], 1, 2, 0, 3);
    m03 <@ inp(x.[0, 2] * y.[0, 1] + x.[0, 1] * y.[0, 2], 0, 3, 1, 2);
    m02 <@ inp(x.[0, 3] * y.[0, 1] + x.[0, 1] * y.[0, 3], 0, 2, 1, 3);
    m01 <@ inp(x.[0, 3] * y.[0, 2] + x.[0, 2] * y.[0, 3], 0, 1, 2, 3);

    (* elementwise multiplication to create sharing of x_i * y_i
       this implements inp_local: no communication occurs *)
    mlocal <- offunm ((fun p s => 
      if s = p then 0 else x.[p, s] * y.[p, s]), N, N);

    (* elementwise addition *)
    return m01 + m02 + m03 + m12 + m13 + m23 + mlocal;   
  }

  proc mult_main(x y : int) : matrix = {
    var z : int;
    var mx, my, mz : matrix;

    mx <@ share(x);
    my <@ share(y);

    mz <@ mult(mx, my);

    return mz;
  }


  proc add_main(x y : int, i j : party) : matrix = {
    var mx, my, mz : matrix;
    var z : int;

    (* party i has x *)
    mx <@ share(x);
    (* party j has y *)
    my <@ share(y);

    (* addition is local *)
    mz <- mx + my;

    return mz;
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
lemma sum_replacement(shares : int list, i x y : int) :
    0 <= i < size shares /\ size shares = N /\ nth err shares i = y  => sumz (put shares i x) = x - y + sumz shares.
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
lemma share_correct(x_ : int) :
    hoare[F4.share: x = x_ ==> valid res /\ open res = x_].
proof.
proc.
seq 5 : (x = x_ /\ size shares = N /\ shares = [s0; s1; s2; s3]).
auto.
progress.
by rewrite _4p.
seq 2 : (x = x_ /\ size shares = N /\ sumz shares = x).
auto; progress.
rewrite _4p // size_put //.
rewrite sum_four.
rewrite size_put //.
rewrite nth_put // nth_put // nth_put // nth_put // /=.
rewrite sum_four // /=.
smt().
(* valid *)
auto.
rewrite _4p.
progress.
rewrite rows_offunm _4p lez_maxr //.
rewrite cols_offunm _4p lez_maxr //.
rewrite get_offunm.
rewrite rows_offunm cols_offunm //.
by simplify.
rewrite get_offunm.
rewrite rows_offunm cols_offunm // lez_maxr //.
rewrite get_offunm.
rewrite rows_offunm cols_offunm // lez_maxr //.
by rewrite /= H4 /=.
rewrite get_offunm.
rewrite rows_offunm cols_offunm // lez_maxr //.
rewrite get_offunm.
rewrite rows_offunm cols_offunm // lez_maxr //.
rewrite /= H4 /=.
have H5p : 0 <> s by smt().
by rewrite H5p /=.
(* correct *)
rewrite /open get_offunm.
rewrite rows_offunm cols_offunm => /=; smt(_4p).
rewrite get_offunm.
rewrite rows_offunm cols_offunm => /=; smt(_4p).
rewrite get_offunm.
rewrite rows_offunm cols_offunm => /=; smt(_4p).
rewrite get_offunm.
rewrite rows_offunm cols_offunm => /=; smt(_4p).
simplify.
(* sums match *)
rewrite (sum_four shares{hr}) // /#.
qed.

(* Prove the sharing scheme is secure.
   For all parties, view looks random.
 *)
lemma share_secure(p : party) :
    equiv[F4.share ~ Sim.share :
      0 <= p < N       
      ==>
      view res{1} p = view res{2} p].
proof.
proc.
wp.
seq 3 3 : (={s0, s1, s2} /\ 0 <= p < N).
auto.
simplify.
rnd (fun u => u).
auto.
rewrite _4p.
progress.
(*smt().
smt(randint1E).
smt().
smt().*)
(* views are equal *)
rewrite /view /row.
rewrite 2!cols_offunm lez_maxr //.
rewrite eq_vectorP.
rewrite 2!size_offunv lez_maxr // /=.
move => sh.
elim => shgt0 shlt4.
rewrite get_offunv // get_offunv //.
(* evaluate function calls *)
simplify.
(* convert back to matrix *)
rewrite get_offunm.
rewrite rows_offunm lez_maxr // cols_offunm lez_maxr //.
rewrite get_offunm.
rewrite rows_offunm lez_maxr // cols_offunm lez_maxr //.
progress.
have size4 : size [s0{2}; s1{2}; s2{2}; s3{2}] = 4 by trivial.
(* trivial when p = sh => view on diagonal, so zero *)
case (p = sh) => [// | off_diag].
(* off diagonal: shares are indistinguishable *)
rewrite nth_put.
rewrite size4 //.
(* bottom-left side of diagonal: p is looking at a truly random element *)
case (sh < p) => [shltp | shgteqp].
case (sh = 0) => [// | shn0].
case (sh = 1) => [// | shn1].
case (sh = 2) => [// | /#].
(* sh >= p *)
case (sh = 0) => [// | shn0].
case (sh = 1) => [// | shn1].
case (sh = 2) => [// | shn2].
have sh3 : sh = 3 by smt().
rewrite sh3 /=.
rewrite sum_four.
rewrite size4 //.
simplify.

rewrite addr.
have s3s3 : s3{1} = s3L.
admit.
rewrite s3s3.
smt().
qed.

(* Prove addition is correct *)
lemma add_correct(x_ y_ : int, pi pj : party) :
    hoare[F4.add_main : x = x_ /\ y = y_ /\ i = pi /\ j = pj /\ 0 <= pi < N /\ 0 <= pj < N
      ==> valid res /\ open res = x_ + y_].
proof.
proc.
have n4 : N = 4 by rewrite _4p.

seq 1 : (open mx = x_ /\ y = y_ /\ size mx = (N, N) /\ valid mx /\ j{hr} = pj /\ 0 <= pj < N).

auto.
call (share_correct x_ pi).
auto => />; progress; smt().

seq 1 : (open mx = x_ /\ size mx = (N, N) /\ valid mx /\
         open my = y_ /\ size my = (N, N) /\ valid my).
call (share_correct y_ pj).
(*Validity proof*)
auto => />; progress; smt().
wp.
auto.

(*Validity proof*)
auto => />.
move => &hr rows_mx cols_mx _ _ diag_mx not_diag_mx_left not_diag_mx_right rows_my cols_my _ _ diag_my not_diag_my_left not_diag_my_right.
progress.
rewrite rows_addm rows_mx rows_my /#.
rewrite cols_addm cols_mx cols_my /#.
rewrite get_addm; smt().
rewrite 2!get_addm.
have mxp0_eq_mx10: mrange mx{hr} p 0 /\ p <> 0 => mx{hr}.[p,0] = mx{hr}.[1, 0] by smt().
rewrite mxp0_eq_mx10.
rewrite H.
rewrite rows_addm in H0.
smt().
have myp0_eq_my10: mrange my{hr} p 0 /\ p <> 0 => my{hr}.[p,0] = my{hr}.[1, 0] by smt().
rewrite myp0_eq_my10.
rewrite H.
rewrite rows_addm in H0.
smt().
smt().
rewrite 2!get_addm.
have mxps_eq_mx0s: mrange mx{hr} p s /\ p <> s /\ s <> 0 => mx{hr}.[p,s] = mx{hr}.[0, s].
progress.
by smt().
rewrite mxps_eq_mx0s.
progress.
rewrite rows_addm in H0.
smt().
rewrite cols_addm in H2.
smt().
have myps_eq_my0s: mrange my{hr} p s /\ p <> s /\ s <> 0 => my{hr}.[p,s] = my{hr}.[0, s]. 
progress.
by smt().
rewrite  myps_eq_my0s.
progress.
rewrite rows_addm in H0.
smt().
rewrite cols_addm in H2.
smt().
smt().
(*Corretness proof*)
by rewrite open_linear.
qed.

lemma add_secure(pi pj : party) :
    equiv[F4.add_main ~ Sim.add :
      0 <= pi < N /\ 0 <= pj < N
      ==>
      view res{1} pi = view res{2} pi \/ view res{1} pj = view res{2} pj].
proof.
proc.
wp.
seq 0 2 : (0 <= pi < N /\ 0 <= pj < N).
auto.
progress.
rewrite randint_ll.
admit.
qed.

(* TODO: maybe do something like this to simplify all of the get/rows/cols proof steps below *)
lemma offunm_unwrap (i, j : party, f : party -> int -> int):
    0 <= i < N /\ 0 <= j < N => (offunm (fun(x y) => f x y, N, N)).[i, j] = f i j.
proof.
progress.
rewrite get_offunm.
rewrite rows_offunm cols_offunm H H1 /=.
move : H0 H2.
by rewrite _4p.
by simplify.
qed.

(* Prove correctness of the jmp. *)
lemma jmp_correct(x_ : int, si_ sj_ d_ g_: party) :
    hoare[F4.jmp : x = x_ /\ si = si_ /\ 
      sj = sj_ /\ d = d_ /\ g = g_ /\ 0 <= g_ < N
      ==>
      valid res /\ open res = x_].
proof.
proc.
(*Proof for open*)
auto.
rewrite _4p.
progress.
rewrite rows_offunm _4p lez_maxr // /=.
rewrite cols_offunm _4p lez_maxr //.
rewrite get_offunm.
rewrite rows_offunm cols_offunm /= lez_maxr //.
by simplify.
rewrite get_offunm.
rewrite rows_offunm cols_offunm /= lez_maxr //.
rewrite get_offunm.
rewrite rows_offunm cols_offunm /= lez_maxr //.
by rewrite /= H5 /=.

rewrite get_offunm.
rewrite rows_offunm cols_offunm /= lez_maxr //.
rewrite get_offunm.
rewrite rows_offunm cols_offunm /= lez_maxr //.
have H6p : 0 <> s by smt().
by rewrite /= H5 H6p /=.
rewrite /open.
rewrite get_offunm.
by rewrite rows_offunm cols_offunm => /=.
rewrite get_offunm.
by rewrite rows_offunm cols_offunm => /=.
rewrite get_offunm.
by rewrite rows_offunm cols_offunm => /=.
rewrite get_offunm.
by rewrite rows_offunm cols_offunm => /=.
simplify.
smt(_4p sum_four).
qed.

(* Prove correctness of inp. *)
lemma inp_correct(x_ : int, i_ j_ g_ h_: party) :
    hoare[F4.inp : x = x_ /\ i = i_ /\
      j = j_ /\ h = h_ /\ g = g_ /\ 0 <= h_ < N
      ==>
      valid res /\ open res = x_].
proof.
proc.
(*Proof for open*)
auto.
seq 2 : (x = x_ /\ i = i_ /\ j = j_ /\ h = h_ /\ g = g_ /\ 
  0 <= h_ < N /\ xh = x - r).
auto.
progress.
exists* r.
elim* => r_.
call (jmp_correct (x_ - r_) i_ j_ g_ h_).
auto => />.
rewrite _4p.
move => h0 hn result rowsn colsn diag0 valid_s0 valid_snot0 openr.
progress.
(* first, inp output is valid. *)
rewrite rows_addm rowsn rows_offunm /#.
rewrite cols_addm colsn cols_offunm /#.
have mrange_a : mrange result a a.
  rewrite rowsn colsn.
  move : H0.
  rewrite rows_addm rowsn rows_offunm /#.
rewrite get_addm.
rewrite get_offunm.
rewrite rows_offunm cols_offunm /#.
simplify.
by rewrite diag0.

(* columns are equal *)
rewrite 2!get_addm.
rewrite get_offunm.
rewrite rows_offunm cols_offunm.
rewrite /max.
simplify.
move: H0.
rewrite rows_addm rowsn rows_offunm /#.
rewrite get_offunm.
rewrite rows_offunm cols_offunm /#.
simplify.
have resultp0_eq_result10: mrange result p 0 /\ p <> 0 /\ 0 = 0 => result.[p, 0] = result.[1, 0] by smt().
rewrite resultp0_eq_result10.
progress.
move: H0.
rewrite rows_addm rowsn rows_offunm /#.
move: H1.
rewrite cols_addm colsn cols_offunm /#.
smt().
rewrite 2!get_addm.
rewrite get_offunm.
rewrite rows_offunm cols_offunm.
rewrite /max.
simplify.
progress.
move: H0.
rewrite rows_addm rowsn rows_offunm /#.
move: H2.
rewrite cols_offunm colsn cols_offunm /#.
rewrite get_offunm.
rewrite rows_offunm cols_offunm.
rewrite /max.
simplify.
progress.
move: H2.
rewrite cols_offunm colsn cols_offunm /#.
simplify.
have resultps_eq_result0s: mrange result p s /\ p <> s /\ s <> 0 => result.[p, s] = result.[0, s].
progress.
smt().
rewrite resultps_eq_result0s.
progress.
move: H0.
rewrite rows_addm rowsn rows_offunm /#.
move: H2.
rewrite cols_offunm colsn cols_offunm /#.
have s_noteq_p: s <> p by smt().
rewrite H4 s_noteq_p /#.
(* begin correctness proof *)
rewrite open_linear.
rewrite /open.
rewrite get_offunm.
rewrite cols_offunm rows_offunm /#.
rewrite get_offunm.
rewrite cols_offunm rows_offunm /#.
rewrite get_offunm.
rewrite cols_offunm rows_offunm /#.
rewrite get_offunm.
rewrite cols_offunm rows_offunm /#.
simplify.
smt(_4p).
qed.

(* annoying, but if we try to smt() this down below without the intermediate lemma,
   smt gets confused. (maybe too much in context) *)
lemma add_rearrange (t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 : int) :
   t1 +  t2 +  t3 +  t4 +  t5 +  t6 +  t7 +  t8 +
   t9 + t10 + t11 + t12 + t13 + t14 + t15 + t16 =
  t13 +  t5 +  t3 + t12 +  t6 + t14 +  t1 + t10 +
   t4 +  t2 + t15 +  t8 + t11 +  t9 +  t7 + t16.
proof.
smt().
qed.

lemma valid_size(m : matrix) :
    valid m => rows m = N /\ cols m = N.
proof.
rewrite /valid.
smt().
qed.

lemma valid_diag0(m : matrix) :
    valid m => forall a, m.[a, a] = 0.
proof.
rewrite /valid.
smt().
qed.

lemma valid_col0(m : matrix) :
    valid m => forall p, 0 < p < N => m.[p, 0] = m.[1, 0].
proof.
rewrite /valid.
progress.
rewrite H2.
smt().
trivial.
qed.

lemma valid_colp(m : matrix) :
    valid m => forall p s, mrange m p s /\ p <> s /\ s <> 0  => m.[p, s] = m.[0, s].
proof.
rewrite /valid.
progress.
rewrite H3.
smt().
trivial.
qed.

(* Prove multiplication is correct *)
lemma mul_correct(x_ y_ : int) :
    hoare[F4.mult_main : x = x_ /\ y = y_ ==> open res = x_ * y_ /\ valid res].
proof.
proc.
(* expand each sharing, one variable at a time *)
seq 1 : (open mx = x_ /\ y = y_ /\ size mx = (N, N) /\ valid mx).
auto.
call (share_correct x_ 0).
auto => />; progress; smt(_4p).

seq 1 : (open mx = x_ /\ size mx = (N, N) /\ valid mx /\
         open my = y_ /\ size my = (N, N) /\ valid my).
call (share_correct y_ 1).
auto => />; progress; smt(_4p).

(* prove multiplication is correct *)
inline F4.mult.
wp; sp.
exists* mx, my.
elim* => mx my.

(* expand each inp call using lemma above *)
call (inp_correct (mx.[0,3]*my.[0,2] + mx.[0,2]*my.[0,3]) 0 1 2 3).
call (inp_correct (mx.[0,3]*my.[0,1] + mx.[0,1]*my.[0,3]) 0 2 1 3).
call (inp_correct (mx.[0,2]*my.[0,1] + mx.[0,1]*my.[0,2]) 0 3 1 2).
call (inp_correct (mx.[0,3]*my.[1,0] + mx.[1,0]*my.[0,3]) 1 2 0 3).
call (inp_correct (mx.[0,2]*my.[1,0] + mx.[1,0]*my.[0,2]) 1 3 0 2).
call (inp_correct (mx.[0,1]*my.[1,0] + mx.[1,0]*my.[0,1]) 2 3 0 1).

auto.
progress.
by rewrite _4p.
by rewrite _4p.
by rewrite _4p.

(* prove two sides open to the same matrix *)

rewrite 6!open_linear.

(* results from INP *)
rewrite H7 H10 H13 H16 H19 H22.
(* local multiply result *)
rewrite /open _4p.
rewrite get_offunm.
by rewrite cols_offunm rows_offunm lez_maxr.
rewrite get_offunm.
by rewrite cols_offunm rows_offunm lez_maxr.
rewrite get_offunm.
by rewrite cols_offunm rows_offunm lez_maxr.
rewrite get_offunm.
by rewrite cols_offunm rows_offunm lez_maxr.
simplify.
(* algebra *)
rewrite 3!mulzDr 12!mulzDl.
rewrite 17!addrA.
rewrite add_rearrange. 
by simplify.
(* done correctness... now validity proof *)
(* 1. prove size correct (N x N) *)
rewrite 6!rows_addm.
rewrite valid_size // valid_size // valid_size //
        valid_size // valid_size // valid_size //.
rewrite _4p //.
rewrite 6!cols_addm.
rewrite valid_size // valid_size // valid_size //
        valid_size // valid_size // valid_size //.
rewrite _4p //.

(* 2. prove diag zero *)
rewrite 6!get_addm.
have alt4 : a < 4.
move : H24.
rewrite 6!rows_addm.
rewrite valid_size // valid_size // valid_size //
        valid_size // valid_size // valid_size //.
rewrite _4p //.

clear H24 H26.
rewrite valid_diag0 // valid_diag0 // valid_diag0 //
        valid_diag0 // valid_diag0 // valid_diag0 //.
rewrite get_offunm /= // _4p //.

(* 3a. prove columns consistent *)
(* don't actually need open anymore *)
clear H5 H8 H7 H10 H11 H13 H14 H16 H17 H19 H20 H22.

have plt4 : p < 4.
move : H24.
rewrite 6!rows_addm.
rewrite valid_size // valid_size // valid_size //
        valid_size // valid_size // valid_size //.
rewrite _4p rows_offunm lez_maxr // lez_maxr.

rewrite get_offunm.
rewrite rows_offunm cols_offunm.
rewrite 5!rows_addm 5!cols_addm.
rewrite valid_size // valid_size // valid_size //
        valid_size // valid_size // valid_size //.
rewrite _4p /= lez_maxr.
smt().

clear H24 H26.

rewrite valid_size // valid_size // valid_size //
        valid_size // valid_size // valid_size //.
rewrite _4p.
rewrite lez_maxr //.

rewrite 6!get_addm.
rewrite get_offunm.
rewrite cols_offunm rows_offunm.
rewrite _4p //.
simplify.
rewrite 5!get_addm.
rewrite get_offunm.
rewrite cols_offunm rows_offunm _4p lez_maxr //.
trivial.
simplify.
have zneqp : 0 <> p by smt().
rewrite zneqp /=.

rewrite (valid_col0 result) //.
rewrite _4p /#.
rewrite (valid_col0 result0) //.
rewrite _4p /#.
rewrite (valid_col0 result1) //.
rewrite _4p /#.
rewrite (valid_col0 result2) //.
rewrite _4p /#.
rewrite (valid_col0 result3) //.
rewrite _4p /#.
rewrite (valid_col0 result4) //.
rewrite _4p /#.
rewrite (valid_col0 mx{hr}) //.
rewrite _4p /#.
rewrite (valid_col0 my{hr}) //.
rewrite _4p /#.
trivial.

(* 3b. prove the other columns are consistent *)
clear H5 H8 H7 H10 H11 H13 H14 H16 H17 H19 H20 H22.

have plt4 : p < 4.
move : H24.
rewrite 6!rows_addm.
rewrite valid_size // valid_size // valid_size //
        valid_size // valid_size // valid_size //.
rewrite _4p rows_offunm lez_maxr // lez_maxr.

have slt4 : s < 4.
move : H26.
rewrite 6!cols_addm.
rewrite valid_size // valid_size // valid_size //
        valid_size // valid_size // valid_size //.
rewrite _4p cols_offunm lez_maxr // lez_maxr.

clear H24 H26.

rewrite get_offunm.
rewrite rows_offunm cols_offunm _4p.
rewrite 5!rows_addm 5!cols_addm.
rewrite valid_size // valid_size // valid_size //
        valid_size // valid_size // valid_size //.
rewrite _4p.
rewrite rows_offunm cols_offunm.
rewrite valid_size // valid_size // valid_size //
        valid_size // valid_size // valid_size //.
rewrite _4p.
smt().

simplify.
rewrite 11!get_addm.
rewrite get_offunm.
rewrite cols_offunm rows_offunm.
smt(_4p).
simplify.
rewrite get_offunm.
rewrite cols_offunm rows_offunm.
smt(_4p).
simplify.
rewrite H28.
simplify.
have sneqp : s <> p by smt().
rewrite sneqp /=.

rewrite (valid_colp result) //.
rewrite valid_size // valid_size // _4p /#.
rewrite (valid_colp result0) //.
rewrite valid_size // valid_size // _4p /#.
rewrite (valid_colp result1) //.
rewrite valid_size // valid_size // _4p /#.
rewrite (valid_colp result2) //.
rewrite valid_size // valid_size // _4p /#.
rewrite (valid_colp result3) //.
rewrite valid_size // valid_size // _4p /#.
rewrite (valid_colp result4) //.
rewrite valid_size // valid_size // _4p /#.
rewrite (valid_colp mx{hr}) //.
rewrite valid_size // valid_size // _4p /#.
rewrite (valid_colp my{hr}) //.
rewrite valid_size // valid_size // _4p /#.
qed.




