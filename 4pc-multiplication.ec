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
import Mat_A.Vectors.

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
progress.
rewrite /open.
rewrite 4!get_addm /#.
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

    (* assume P0 holds x and P1 holds y *)
    mx <@ share(x, 0);
    my <@ share(y, 1);

    mz <@ mult(mx, my);

    return mz;
  }


  proc add_main(x y : int) : matrix = {
    var mx, my, mz : matrix;
    var z : int;

    (* party 0 has x *)
    mx <@ share(x, 0);
    (* party 1 has y *)
    my <@ share(y, 1);

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
    hoare[F4.share: x = x_ /\ p = p_ /\ 0 <= p_ < N ==> valid res /\ open res = x_].
proof.
proc.
seq 6 : (x = x_ /\ p = p_ /\ 0 <= p_ < N
  /\ size shares = N
  /\ nth err shares p_ = 0).
auto.
progress.
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
auto.
progress.
(* sum = x *)
rewrite (sum_replacement shares{hr} p{hr} (x{hr} - sumz shares{hr})).
by rewrite H0 H2 H H1 /= // _enz.
smt().
rewrite size_put //.
(* matrix part *)
auto.
rewrite _4p.
progress.
(* valid *)
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

(* Prove the sharing scheme is secure. *)
(* for any party, view of real and simulated matrices look the same *)
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
(* TODO: don't open inside proc. use valid. *)
lemma add_correct(x_ y_ : int) :
    hoare[F4.add_main : x = x_ /\ y = y_ ==> valid res /\ open res = x_ + y_].
proof.
proc.
have n4 : N = 4 by rewrite _4p.
seq 1 : (open mx = x_ /\ y = y_ /\ rows mx = Top.N /\ cols mx = Top.N /\
        (forall (a : int), mrange mx a a => mx.[a, a] = 0) /\
         (forall s, forall p, mrange mx p s /\ p <> s /\ s = 0 => 
          (if s = 0 then mx.[p, s] = mx.[1, s]
           else mx.[p, s] = mx.[0, s])) /\ 
      (forall s, forall p, mrange mx p s /\ p <> s /\ s <> 0=> 
         (if s = 0 then mx.[p, s] = mx.[1, s]
          else mx.[p, s] = mx.[0, s]))).
auto.
call (share_correct x_ 0).
auto => />; progress; smt().
seq 1 : (open mx = x_ /\ rows mx = Top.N /\ cols mx = Top.N /\ 
        (forall (a : int), mrange mx a a => mx.[a, a] = 0) /\
         (forall s, forall p, mrange mx p s /\ p <> s /\ s = 0=> 
         (if s = 0 then mx.[p, s] = mx.[1, s]
          else mx.[p, s] = mx.[0, s])) /\
        (forall s, forall p, mrange mx p s /\ p <> s /\ s <> 0=> 
         (if s = 0 then mx.[p, s] = mx.[1, s]
          else mx.[p, s] = mx.[0, s])) /\
         open my = y_ /\ rows my = Top.N /\ cols my = Top.N /\ 
        (forall (a : int), mrange my a a => my.[a, a] = 0) /\
        (forall s, forall p, mrange my p s /\ p <> s /\ s = 0 => 
          (if s = 0 then my.[p, s] = my.[1, s]
           else my.[p, s] = my.[0, s])) /\
        (forall s, forall p, mrange my p s /\ p <> s /\ s <> 0=> 
         (if s = 0 then my.[p, s] = my.[1, s]
          else my.[p, s] = my.[0, s]))).
call (share_correct y_ 1).
(*Validity proof*)
auto => />; progress; smt().
wp.
auto => />.
move => &hr rows_mx cols_mx diag_mx not_diag_mx_left not_diag_mx_right rows_my cols_my diag_my not_diag_my_left not_diag_my_right.
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

(* TODO: maybe do something like this to simplify all of the get/rows/cols proof steps below *)
lemma offunm_unwrap (i, j : party, f : party -> party -> int):
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

(*There must be an existing lemma but I am just proving it for now*)
lemma not_eq(x, y : int): x <> y => y <> x.
proof.
smt().
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
have s_noteq_p: s <> p by smt(not_eq).
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



(* TODO: validity *)
(* Prove multiplication is correct *)
lemma mul_correct(x_ y_ : int) :
    hoare[F4.mult_main : x = x_ /\ y = y_ ==> open res = x_ * y_ /\ valid res].
proof.
proc.
have n4 : N = 4 by rewrite _4p.
(* expand sharing *)
seq 1 : (open mx = x_ /\ y = y_ /\ rows mx = Top.N /\ cols mx = Top.N /\
        (forall (a : int), mrange mx a a => mx.[a, a] = 0) /\
         (forall s, forall p, mrange mx p s /\ p <> s /\ s = 0 => 
          mx.[p, s] = mx.[1, s]) /\ 
         forall s, forall p, mrange mx p s /\ p <> s /\ s <> 0 => 
           mx.[p, s] = mx.[0, s]).
auto.
call (share_correct x_ 0).
auto => />; progress; smt().
seq 1 : (open mx = x_ /\ rows mx = Top.N /\ cols mx = Top.N /\ 
        (forall (a : int), mrange mx a a => mx.[a, a] = 0) /\
         (forall s, forall p, mrange mx p s /\ p <> s /\ s = 0 => 
        mx.[p, s] = mx.[1, s]) /\  
       (forall s, forall p, mrange mx p s /\ p <> s /\ s <> 0 => 
           mx.[p, s] = mx.[0, s]) /\
         open my = y_ /\ rows my = Top.N /\ cols my = Top.N /\ 
        (forall (a : int), mrange my a a => my.[a, a] = 0) /\
        (forall s, forall p, mrange my p s /\ p <> s/\ s = 0 => 
         my.[p, s] = my.[1, s]) /\
        forall s, forall p, mrange my p s /\ p <> s /\ s <> 0 => 
           my.[p, s] = my.[0, s]).

call (share_correct y_ 1).
(*Validity proof*)
auto => />; progress; smt().
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

auto => />.
progress.

by rewrite n4.
by rewrite n4.
by rewrite n4.
(* prove two sides open to the same matrix *)

rewrite 6!open_linear.

rewrite H15 H22 H29 H35 H41 H47.
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
(*Mult correct validity proof*)
rewrite 6!rows_addm.

rewrite H10 H17 H24 H30 H36 H42.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

rewrite 6!cols_addm.

rewrite H11 H18 H25 H31 H37 H43.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.
rewrite 6!get_addm.
rewrite get_offunm.
rewrite cols_offunm rows_offunm.
rewrite n4.
rewrite /max.
simplify.
progress.


move: H49.
rewrite 6!rows_addm.
rewrite H10 H17 H24 H30 H36 H42.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.
move: H49.
rewrite 6!rows_addm.
rewrite H10 H17 H24 H30 H36 H42.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

(*Proof Diagonal zero*)
(*result.[a, a] = 0*)
rewrite H12.
progress.
rewrite H10 n4.

move: H49.
rewrite 6!rows_addm.
rewrite H10 H17 H24 H30 H36 H42.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

move: H50.
rewrite 6!cols_addm.
rewrite H11 H18 H25 H31 H37 H43.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

(*result0.[a, a] = 0*)
rewrite H19.
progress.
rewrite H17 n4.

move: H49.
rewrite 6!rows_addm.
rewrite H10 H17 H24 H30 H36 H42.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

move: H50.
rewrite 6!cols_addm.
rewrite H11 H18 H25 H31 H37 H43.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.


(*result1.[a, a] = 0*)
rewrite H26.
progress.
rewrite H24 n4.

move: H49.
rewrite 6!rows_addm.
rewrite H10 H17 H24 H30 H36 H42.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

move: H50.
rewrite 6!cols_addm.
rewrite H11 H18 H25 H31 H37 H43.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.


(*result2.[a, a] = 0*)
rewrite H32.
progress.
rewrite H30 n4.

move: H49.
rewrite 6!rows_addm.
rewrite H10 H17 H24 H30 H36 H42.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

move: H50.
rewrite 6!cols_addm.
rewrite H11 H18 H25 H31 H37 H43.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.



(*result3.[a, a] = 0*)
rewrite H38.
progress.
rewrite H36 n4.

move: H49.
rewrite 6!rows_addm.
rewrite H10 H17 H24 H30 H36 H42.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

move: H50.
rewrite 6!cols_addm.
rewrite H11 H18 H25 H31 H37 H43.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.




(*result4.[a, a] = 0*)
rewrite H44.
progress.
rewrite H42 n4.

move: H49.
rewrite 6!rows_addm.
rewrite H10 H17 H24 H30 H36 H42.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

move: H50.
rewrite 6!cols_addm.
rewrite H11 H18 H25 H31 H37 H43.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.
simplify.
trivial.

(*Proof that columns are equal when s = 0*)
rewrite 12!get_addm.
rewrite get_offunm.
rewrite rows_offunm lez_maxr // n4 //.
rewrite cols_offunm lez_maxr //. 
progress.

move: H49.
rewrite 6!rows_addm.
rewrite H10 H17 H24 H30 H36 H42.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

rewrite get_offunm.
rewrite rows_offunm lez_maxr // n4 //.
simplify.
have zero_noteq_p: 0 <> p. 
rewrite (not_eq p 0).
by rewrite H51.
trivial.
rewrite zero_noteq_p.
simplify.


(*result.[p, 0] = result.[1, 0]*)
have resultp0_eq_result10:  mrange result p 0 /\ p <> 0 => result.[p,0] = result.[1, 0].
progress.
rewrite (H13 0 p).
progress.
trivial.

(*result0.[p, 0] = result0.[1, 0]*)
have result0p0_eq_result010:  mrange result0 p 0 /\ p <> 0 => result0.[p,0] = result0.[1, 0].
progress.
rewrite (H20 0 p).
progress.
trivial.


(*result1.[p, 0] = result1.[1, 0]*)
have result1p0_eq_result110:  mrange result1 p 0 /\ p <> 0 => result1.[p,0] = result1.[1, 0].
progress.
rewrite (H27 0 p).
progress.
trivial.


(*result2.[p, 0] = result2.[1, 0]*)
have result2p0_eq_result210:  mrange result2 p 0 /\ p <> 0 => result2.[p,0] = result2.[1, 0].
progress.
rewrite (H33 0 p).
progress.
trivial.


(*result3.[p, 0] = result3.[1, 0]*)
have result3p0_eq_result310:  mrange result3 p 0 /\ p <> 0 => result3.[p,0] = result3.[1, 0].
progress.
rewrite (H39 0 p).
progress.
trivial.


(*result4.[p, 0] = result4.[1, 0]*)
have result4p0_eq_result410:  mrange result4 p 0 /\ p <> 0 => result4.[p,0] = result4.[1, 0].
progress.
rewrite (H45 0 p).
progress.
trivial.


(*mx.[p, 0] = mx.[1, 0]*)
have mxp0_eq_mx10:  mrange mx p 0 /\ p <> 0 => mx.[p,0] = mx.[1, 0].
progress.
rewrite (H2 0 p).
progress.
trivial.


(*my.[p, 0] = my.[1, 0]*)
have myp0_eq_my10:  mrange my p 0 /\ p <> 0 => my.[p,0] = my.[1, 0].
progress.
rewrite (H7 0 p).
progress.
trivial.

rewrite resultp0_eq_result10.
progress.
rewrite H10 n4.
move: H49.
rewrite 6!rows_addm.
rewrite H10 H17 H24 H30 H36 H42.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

rewrite H11 n4 //.

rewrite result0p0_eq_result010.
progress.
rewrite H17 n4.
move: H49.
rewrite 6!rows_addm.
rewrite H10 H17 H24 H30 H36 H42.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

rewrite H18 n4 //.

rewrite result1p0_eq_result110.
progress.
rewrite H24 n4.
move: H49.
rewrite 6!rows_addm.
rewrite H10 H17 H24 H30 H36 H42.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

rewrite H25 n4 //.


rewrite result2p0_eq_result210.
progress.
rewrite H30 n4.
move: H49.
rewrite 6!rows_addm.
rewrite H10 H17 H24 H30 H36 H42.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

rewrite H31 n4 //.


rewrite result3p0_eq_result310.
progress.
rewrite H36 n4.
move: H49.
rewrite 6!rows_addm.
rewrite H10 H17 H24 H30 H36 H42.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

rewrite H37 n4 //.

rewrite result4p0_eq_result410.
progress.
rewrite H42 n4.
move: H49.
rewrite 6!rows_addm.
rewrite H10 H17 H24 H30 H36 H42.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

rewrite H43 n4 //.


rewrite mxp0_eq_mx10.
progress.
rewrite H n4.
move: H49.
rewrite 6!rows_addm.
rewrite H10 H17 H24 H30 H36 H42.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

rewrite H0 n4 //.

rewrite myp0_eq_my10.
progress.
rewrite H4 n4.
move: H49.
rewrite 6!rows_addm.
rewrite H10 H17 H24 H30 H36 H42.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

rewrite H5 n4 //.
trivial.



(*Proof that columns are Equal when s<>0*)

rewrite 12!get_addm.
rewrite get_offunm.
rewrite rows_offunm lez_maxr // n4 //.
rewrite cols_offunm lez_maxr //. 
progress.

move: H49.
rewrite 6!rows_addm.
rewrite H10 H17 H24 H30 H36 H42.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

move: H51.
rewrite 6!cols_addm.
rewrite H11 H18 H25 H31 H37 H43.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.


rewrite get_offunm.
rewrite rows_offunm lez_maxr // n4 //.
rewrite cols_offunm lez_maxr //. 
simplify.
rewrite H50.

move: H51.
rewrite 6!cols_addm.
rewrite H11 H18 H25 H31 H37 H43.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

simplify.

(*result.[p, s] = result.[0, s]*)
have resultps_eq_result0s: result.[p,s] = result.[0, s].
rewrite H14.
progress.
move: H49.
rewrite 6!rows_addm.
rewrite H10 H17 H24 H30 H36 H42.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

move: H51.
rewrite 6!cols_addm.
rewrite H11 H18 H25 H31 H37 H43.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

trivial.


(*result0.[p, s] = result0.[0, s]*)
have result0ps_eq_result00s: result0.[p,s] = result0.[0, s].
rewrite H21.
progress.
move: H49.
rewrite 6!rows_addm.
rewrite H10 H17 H24 H30 H36 H42.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

move: H51.
rewrite 6!cols_addm.
rewrite H11 H18 H25 H31 H37 H43.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

trivial.


(*result1.[p, s] = result1.[0, s]*)
have result1ps_eq_result10s: result1.[p,s] = result1.[0, s].
rewrite H28.
progress.

move: H49.
rewrite 6!rows_addm.
rewrite H10 H17 H24 H30 H36 H42.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

move: H51.
rewrite 6!cols_addm.
rewrite H11 H18 H25 H31 H37 H43.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

trivial.

(*result2.[p, s] = result2.[0, s]*)
have result2ps_eq_result20s: result2.[p,s] = result2.[0, s].
rewrite H34.
progress.

move: H49.
rewrite 6!rows_addm.
rewrite H10 H17 H24 H30 H36 H42.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

move: H51.
rewrite 6!cols_addm.
rewrite H11 H18 H25 H31 H37 H43.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

trivial.


(*result3.[p, s] = result3.[0, s]*)
have result3ps_eq_result30s: result3.[p,s] = result3.[0, s].
rewrite H40.
progress.

move: H49.
rewrite 6!rows_addm.
rewrite H10 H17 H24 H30 H36 H42.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

move: H51.
rewrite 6!cols_addm.
rewrite H11 H18 H25 H31 H37 H43.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

trivial.



(*result4.[p, s] = result4.[0, s]*)
have result4ps_eq_result40s: result4.[p,s] = result4.[0, s].
rewrite H46.
progress.

move: H49.
rewrite 6!rows_addm.
rewrite H10 H17 H24 H30 H36 H42.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

move: H51.
rewrite 6!cols_addm.
rewrite H11 H18 H25 H31 H37 H43.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

trivial.


(*mx.[p, s] = mx.[0, s]*)
have mxps_eq_mx10s: mx.[p,s] = mx.[0, s].
rewrite H3.
progress.

move: H49.
rewrite 6!rows_addm.
rewrite H10 H17 H24 H30 H36 H42.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

rewrite H n4.
trivial.

move: H51.
rewrite 6!cols_addm.
rewrite H11 H18 H25 H31 H37 H43.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

rewrite H0 n4.
trivial.

trivial.


(*my.[p, s] = my.[0, s]*)
have myps_eq_my10s: my.[p,s] = my.[0, s].
rewrite H8.
progress.

move: H49.
rewrite 6!rows_addm.
rewrite H10 H17 H24 H30 H36 H42.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

rewrite H4 n4.
trivial.

move: H51.
rewrite 6!cols_addm.
rewrite H11 H18 H25 H31 H37 H43.
rewrite n4 /max.
simplify.
rewrite /max.
simplify.
trivial.

rewrite H5 n4.
trivial.

trivial.

rewrite resultps_eq_result0s result0ps_eq_result00s.
rewrite result1ps_eq_result10s result2ps_eq_result20s result3ps_eq_result30s result4ps_eq_result40s mxps_eq_mx10s myps_eq_my10s.

have s_noteq_p: s <> p.
rewrite eq_sym.
trivial.

rewrite s_noteq_p H53.
simplify.
trivial.


qed.

