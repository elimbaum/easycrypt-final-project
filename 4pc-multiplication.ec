prover quorum=1 ["Alt-Ergo" "Z3"].
timeout 2.  (* limit SMT solvers to two seconds *)
require import AllCore FSet List Distr.
require import Bool IntDiv.
require import Number StdOrder.
(*---*) import RealOrder. 

require import ZModP. 
clone import ZModField as Zmod.

import Zmod.Sub.
import Zmod.ZModule.

require (*---*) DynMatrix.

type elem = Zmod.zmod.

clone DynMatrix as Mat_A with
type ZR.t <- elem,
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

(* We have four parties. *)
op N : int.
axiom _4p : N = 4.

type party = int.
axiom pbounds : forall (p : party), 0 <= p < 4.

type share = int.
axiom sbounds : forall (s : share), 0 <= s < 4.

import Mat_A.Matrices.
import Mat_A.Vectors.

(* DISTRIBUTION *)
import Zmod.DZmodP.

op randelem : zmod distr = dunifin.

lemma randelem_full: is_full randelem by exact dunifin_fu.

lemma randelem1E (s : zmod) : mu1 randelem s = (1%r / p%r)%Real
  by rewrite dunifin1E cardE.

lemma randelem_ll: is_lossless randelem by exact dunifin_ll.

lemma randelem_funi: is_funiform randelem.
proof.
by move=> ??; rewrite !randelem1E.
qed.

(* WARNING: matrices are zero indexed, so we need to have share 0, party 0 *)
(* matrix semantics are [party, share] *)

(* An unspecified non-zero error value *)
op err : elem.
axiom _enz : err <> zero.

(* Calculate sum of elems in list of elems *)
op sumz_elem (sz : elem list) = foldr Zmod.(+) zero sz.

op open(m : matrix) =
    (* consistency check? or precondition? *)
    (* add up party 0 shares, then add P1's x0... make this nicer? *)
    m.[0, 1] + m.[0, 2] + m.[0, 3] + m.[1, 0].

lemma open_linear(mx my : matrix):
    open (mx + my) = open mx + open my.
proof.
rewrite /open.
rewrite 4!get_addm.
algebra.
qed.

op valid(m : matrix) =
   (* matrix is NxN *)
   size m = (N, N)
   (* diagonal is zero *)
   /\ (forall (a : int), mrange m a a => m.[a, a] = zero)
   (* off diagonal, each column identical for all parties *)
   /\ (forall s, forall p, mrange m p s /\ p <> s /\ s = 0 => 
          (* for share 0, all shares equal to party 1's *)
           m.[p, s] = m.[1, s])
   /\ (forall s, forall p, mrange m p s /\ p <> s /\ s <> 0 => 
          (* for all other shares, equal to party 0's *)
           m.[p, s] = m.[0, s]).

(* oops. this might be backwards from what we need. *)
lemma valid_linear (x y : matrix) :
    valid x /\ valid y => valid (x + y).
proof.
rewrite /valid _4p.
progress.
rewrite rows_addm /#.
rewrite cols_addm /#.
have alt4 : a < 4.
move : H10.
rewrite rows_addm /#.
rewrite get_addm.
rewrite H1; first by smt().
rewrite H6; first by smt().
by rewrite add0r.
have plt4 : p < 4.
rewrite rows_addm in H10; smt().
rewrite !get_addm.
rewrite H2; first by smt().
rewrite H7; first by smt().
trivial.
have pslt4 : p < 4 /\ s < 4.
move : H10 H12. rewrite rows_addm cols_addm; smt().
rewrite !get_addm.
rewrite H3; first by smt().
rewrite H8; first by smt().
trivial.
qed.

op view(m : matrix, p : party) =
  row m p.


module Sim = {
  (* simulator ignores x and just returns a random sharing
     we will argue that all rows of the matrix (parties' views)
     are indistinguishable. *)
  proc share(x : elem) : matrix = {
    var s0, s1, s2, s3 : elem;
    var shares : elem list;

    (* generate random *)
    s0 <$ randelem;
    s1 <$ randelem;
    s2 <$ randelem;
    s3 <$ randelem;

    shares <- [s0; s1; s2; s3];

    return offunm ((fun p_ s =>
        if p_ = s then zero else (nth err shares s)), N, N);
  }

  proc jmp(x : elem, si sj g h : party) : matrix = {
    (* QUESTION: what, if anything, should the simulator do here? *)
    var mjmp : matrix;

    mjmp <- offunm ((fun p s =>
        if s = p then zero else
        if s = h then x else zero), N, N);
    return mjmp;
  }

  proc inp(x : elem, i j g h : party) : matrix = {
    var r, xh, xfake: elem;
    var pgm, minp : matrix;

    r <$ randelem;
    
    (* for Pi Pj : sim can't fool them, since them already have 
       Security for INP is only against g and h
     *)
    xh <- x - r;
    (* for Pg : sim can fool them. *)
    xfake <$ randelem;

    (* NOTE: this is NOT a valid matrix, because share h disagrees. *)
    minp <- offunm ((fun p s => 
      if s = p then zero else (* diag *)
      if s = g then r else    (* share g is always r *)
      if s = h then (if p = g then xfake else xh) (* lie to Pg, give Pi Pj real *)
      else zero (* all other shares 0 *)
      ), N, N);
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
      if s = p then zero else x.[p, s] * y.[p, s]), N, N);

    (* elementwise addition *)
    return m01 + m02 + m03 + m12 + m13 + m23 + mlocal;
  }

  proc mult_main(x y : elem) : matrix = {
    var mx, my, mz : matrix;

    mx <@ share(x);
    my <@ share(y);

    mz <@ mult(mx, my);

    return mz;
  }

  proc add(x y : elem) : matrix = {
    var mx, my : matrix;

    (* these will be simulated random matrices *)
    mx <@ share(x);
    my <@ share(y);
    return mx + my;
  }
}.


module F4 = {
  
  (* dealer has value x and wants to share it with all other parties *)
  proc share(x : elem) : matrix = {
    var s0, s1, s2, s_ : elem;

    var shares : elem list;

    (* generate random *)
    s0 <$ randelem;
    s1 <$ randelem;
    s2 <$ randelem;

    (* set last share such that the new sum equals x *)
    shares <- [s0; s1; s2; x - (s0 + s1 + s2)];

    (* TODO: basically every `offunm` call is going to have the structure
        if p_ = s then 0 else ...
       maybe we can factor that out?
     *)
    return offunm ((fun p_ s =>
        if p_ = s then zero else (nth err shares s)), N, N);
  }

  (* parties si and sj know x, and want to send it to party d.
     g is exlcuded.
     todo: cheating identification (vs just abort)
     NOTE: this is NOT a secure functionality. just message passing.


     matrix representation:
      |. 0 0 x|     |. 0 0 x|    party i
      |0 . 0 x| --> |0 . 0 x|    party h
      |0 0 . ?|     |0 0 . x|    party g
      |0 0 0 .|     |0 0 0 .|  ( party h)
   *)
  proc jmp(x : elem, si sj g h : party) : matrix = {
    (* TODO: party g gets x from si, and H(x) from sj *)
    (* abort if hashes don't check out *)
    (* mayank points out: don't do hash. just both send, compare *)
    var mjmp : matrix;

    (* zero matrix, except share h, which is x *)
    mjmp <- offunm ((fun p s =>
        if s = p then zero else
        if s = h then x else zero), N, N);
    return mjmp;
  }

  (* parties i and j know x, and want to share it with the two other
     parties g and h.
   *)
  proc inp(x : elem, i j g h : party) : matrix = {
    var r, xh : elem;
    var pgm, minp : matrix;

    (* in the paper this is a PRF, but for now model as truly random
       and just don't give it to party g.
       parties i, j, h generate r. *)
    r <$ randelem;

    (* only parties i and j know BOTH x and r, so only parties i and j know xh *)
    xh <- x - r;

    (* Use jmp to send xh from Pi, Pj to Pg *)
    pgm <@ jmp(xh, i, j, g, h);

    (* xi = xj = 0, xg = r, xh = x - r (within pgm) *)
    minp <- pgm + offunm ((fun p s => 
      if s = p then zero else
      if s = g then r else zero), N, N);
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
      if s = p then zero else x.[p, s] * y.[p, s]), N, N);

    (* elementwise addition *)
    return m01 + m02 + m03 + m12 + m13 + m23 + mlocal;   
  }

  proc mult_main(x y : elem) : matrix = {
    var mx, my, mz : matrix;

    mx <@ share(x);
    my <@ share(y);

    mz <@ mult(mx, my);

    return mz;
  }


  proc add_main(x y : elem) : matrix = {
    var mx, my, mz : matrix;

    mx <@ share(x);
    my <@ share(y);

    (* addition is local *)
    mz <- mx + my;

    return mz;
  }
}.


(* sum of four element list is the sum of the individual elements *)
lemma sum_four(s : elem list) :
    size s = 4 => sumz_elem s = 
    nth err s 0 + nth err s 1 + nth err s 2 + nth err s 3.
proof.
progress.
rewrite /sumz_elem -take_size H.
rewrite (take_nth err 3); first by rewrite H.
rewrite (take_nth err 2); first by rewrite H.
rewrite (take_nth err 1); first by rewrite H.
rewrite (take_nth err 0); first by rewrite H.
rewrite take0.
smt(addrA addrC add0r).
qed.

(************************)
(* SHARE ****************)
(************************)

(* Prove correctness of the sharing scheme. *)
lemma share_correct(x_ : elem) :
    hoare[F4.share: x = x_ ==> valid res /\ open res = x_].
proof.
proc.
seq 4 : (x = x_ /\ size shares = N /\ sumz_elem shares = x).
auto.
progress.
by rewrite _4p.
rewrite sum_four //=; algebra.
(* valid *)
auto.
rewrite _4p.
progress.
rewrite rows_offunm _4p lez_maxr //.
rewrite cols_offunm _4p lez_maxr //.
rewrite get_offunm.
rewrite rows_offunm cols_offunm //.
by simplify.
rewrite get_offunm; first by rewrite rows_offunm cols_offunm // lez_maxr //.
rewrite get_offunm; first by rewrite rows_offunm cols_offunm // lez_maxr //.
by rewrite /= H4 /=.
rewrite get_offunm; first by rewrite rows_offunm cols_offunm // lez_maxr //.
rewrite get_offunm; first by rewrite rows_offunm cols_offunm // lez_maxr //.
rewrite /= H4 /=.
have H5p : 0 <> s by smt().
by rewrite H5p /=.
(* correct *)
rewrite /open.
rewrite get_offunm; first by rewrite rows_offunm cols_offunm //=.
rewrite get_offunm; first by rewrite rows_offunm cols_offunm //=.
rewrite get_offunm; first by rewrite rows_offunm cols_offunm //=.
rewrite get_offunm; first by rewrite rows_offunm cols_offunm //=.
simplify.
(* sums match *)
rewrite (sum_four shares{hr}) //.
algebra.
qed.

(* Prove the sharing scheme is secure.
   For all parties, view looks random.
 *)
lemma share_secure (p : party):
    equiv[F4.share ~ Sim.share :
      ={x}
      ==>
      size res{1} = (N, N) /\ size res{2} = (N, N) /\
      view res{1} p = view res{2} p].
proof.
proc.
wp.
(*** party 3 ***) 
case (p = 3).
(* easy: all random in both cases *)
seq 3 3 : (={s0, s1, s2} /\ p = 3); auto. 
rewrite _4p.
progress.
rewrite /view /row 2!cols_offunm lez_maxr // eq_vectorP 2!size_offunv //=.
move => sh [shgt0 shlt4].
(* extract matrix *)
rewrite !get_offunv //=.
rewrite !get_offunm; first rewrite rows_offunm cols_offunm //.
rewrite shgt0 shlt4 //=.
simplify.
case (sh = 0) => [// | shn0].
case (sh = 1) => [// | shn1].
case (sh = 2) => //.
smt().

(* other parties. last share is technically non-random but still looks it. *)
(*** party 2 ***)
case (p = 2).
seq 2 2 : (={x, s0, s1} /\ p = 2).
auto.
seq 0 1 : (={x, s0, s1} /\ p = 2).
auto.
rnd (fun u => x{1} - (s0{1} + s1{1} + u)).
auto.
rewrite _4p.
progress; first 2 by algebra.
(* non-trivial views are equal *)
rewrite /view /row 2!cols_offunm lez_maxr // eq_vectorP 2!size_offunv //=.
move => sh [shgt0 shlt4].
(* extract matrix *)
rewrite !get_offunv //=.
rewrite !get_offunm; first 2 rewrite rows_offunm cols_offunm /#.
simplify.
case (sh = 0) => [// | shn0].
case (sh = 1) => [// | shn1].
case (sh = 2) => [-> //= | shn2].
have -> //= : sh = 3 by smt().

(*** party 1 ***)
case (p = 1).
seq 1 1 : (={x, s0} /\ p = 1).
auto.
(* THIS IS THE TICKET! *)
swap{1} 1.
seq 0 1 : (={x, s0} /\ p = 1).
auto.
seq 1 1 : (={x, s0, s2} /\ p = 1).
auto.
rnd (fun u => x{1} - s0{1} - s2{1} - u).
auto.
rewrite _4p.
progress; first 2 by algebra.
(* non-trivial views are equal *)
rewrite /view /row 2!cols_offunm lez_maxr // eq_vectorP 2!size_offunv //=.
move => sh [shgt0 shlt4].
(* extract matrix *)
rewrite !get_offunv //=.
rewrite !get_offunm; first 2 rewrite rows_offunm cols_offunm //.
simplify.
case (sh = 0) => [// | shn0].
case (sh = 1) => [// | shn1].
case (sh = 2) => [// | shn2].
have -> //= : sh = 3 by smt().
algebra.

(*** party 0 ***)
swap 1 2.
seq 2 2 : (={x, s1, s2} /\ p = 0).
auto.
smt(pbounds).
seq 0 1 : (={x, s1, s2} /\ p = 0).
auto.
rnd (fun u => x{1} - s1{1} - s2{1} - u).
auto.
rewrite _4p.
progress; first 2 by algebra.
rewrite /view /row 2!cols_offunm lez_maxr // eq_vectorP 2!size_offunv //=.
move => sh [shgt0 shlt4].

rewrite !get_offunv //=.
rewrite !get_offunm; first 2 rewrite rows_offunm cols_offunm //.
case (sh = 0) => [// | shn0].
case (sh = 1) => [// | shn1].
case (sh = 2) => [// | shn2].
have -> //= : sh = 3 by smt().
algebra.
qed.

(************************)
(* JMP ******************)
(************************)

(* Prove correctness of the jmp: joint message passing *)
lemma jmp_correct(x_ : elem, si_ sj_ g_ h_ : party) :
    hoare[F4.jmp : x = x_ /\ si = si_ /\ 
      sj = sj_ /\ g = g_ /\ h = h_ /\ 0 <= g_ < N /\ 0 <= h_ < N
      ==>
      valid res /\ open res = x_].
proof.
proc.
(*Proof for open*)
auto.
rewrite _4p.
progress.
rewrite rows_offunm _4p lez_maxr //=.
rewrite cols_offunm _4p lez_maxr //=.
rewrite get_offunm.
rewrite rows_offunm cols_offunm /= lez_maxr //.
by simplify.
rewrite get_offunm; first rewrite rows_offunm cols_offunm /= lez_maxr //=.
rewrite get_offunm; first rewrite rows_offunm cols_offunm /= lez_maxr //=.
rewrite eq_sym in H7.
by rewrite //= H7.
rewrite get_offunm; first rewrite rows_offunm cols_offunm /= lez_maxr //.
rewrite get_offunm; first rewrite rows_offunm cols_offunm /= lez_maxr //.
rewrite eq_sym in H7.
by rewrite /= H7 H8 /=.
rewrite /open.
rewrite !get_offunm; first 4 by rewrite rows_offunm cols_offunm //=.
simplify.
case (h{hr} = 3) => [-> //= | hn3]; first by algebra.
case (h{hr} = 2) => [-> //= | hn2]; first by algebra.
case (h{hr} = 1) => [-> //= | hn1]; first by algebra.
have -> : h{hr} = 0 by smt().
simplify.
algebra.
qed.

(************************)
(* INP ******************)
(************************)

(* Prove correctness of inp: shared input *)
lemma inp_correct(x_ : elem, i_ j_ g_ h_: party) :
    hoare[F4.inp : x = x_ /\ i = i_ /\
      j = j_ /\ h = h_ /\ g = g_ /\ 0 <= g_ < N /\ 0 <= h_ < N
      ==>
      valid res /\ open res = x_].
proof.
proc.
(*Proof for open*)
auto.
seq 2 : (x = x_ /\ i = i_ /\ j = j_ /\ h = h_ /\ g = g_ /\ xh = x - r /\ 0 <= g_ < N /\ 0 <= h_ < N).
auto.
progress.
exists* r.
elim* => r_.
call (jmp_correct (x_ - r_) i_ j_ g_ h_).
auto => />.
rewrite _4p.
move => g0 g4 h0 h4 result rowsn colsn diag0 valid_s0 valid_snot0 openr.
progress.
(* first, inp output is valid. *)
rewrite rows_addm rowsn rows_offunm /#.
rewrite cols_addm colsn cols_offunm /#.
have mrange_a : mrange result a a.
  move : H0.
  rewrite rowsn colsn rows_addm rowsn rows_offunm /#.
rewrite get_addm get_offunm; first rewrite rows_offunm cols_offunm.
smt().
simplify.
rewrite diag0.
rewrite mrange_a.
algebra.

(* columns are equal *)
rewrite 2!get_addm get_offunm.
rewrite rows_offunm cols_offunm /max //=.
move: H0.
rewrite rows_addm rowsn rows_offunm; first smt().
rewrite get_offunm.
rewrite rows_offunm cols_offunm //=.
simplify.
have resultp0_eq_result10: mrange result p 0 /\ p <> 0 /\ 0 = 0 => result.[p, 0] = result.[1, 0] by smt().
rewrite resultp0_eq_result10.
progress.
move: H0.
rewrite rows_addm rowsn rows_offunm /#.
move: H1.
rewrite cols_addm colsn cols_offunm /#.
smt().

rewrite 2!get_addm get_offunm.
rewrite rows_offunm cols_offunm /max //=.
move : H0 H2.
rewrite rows_addm rowsn rows_offunm.
rewrite cols_offunm colsn cols_offunm.
smt().
rewrite get_offunm.
rewrite rows_offunm cols_offunm /max //=.
move: H2.
rewrite cols_offunm colsn cols_offunm; first smt().
simplify.
have resultps_eq_result0s: mrange result p s /\ p <> s /\ s <> 0 => result.[p, s] = result.[0, s].
progress.
smt().

rewrite resultps_eq_result0s.
move: H0 H2.
rewrite rows_addm rowsn rows_offunm
        cols_addm colsn cols_offunm. 
smt().
have s_noteq_p: s <> p by smt().
by rewrite H4 s_noteq_p.

(* begin correctness proof *)
rewrite open_linear /open.
rewrite !get_offunm; first 4 rewrite cols_offunm rows_offunm; smt().
simplify.
case (3 = g_) => [<- //= | ?]; first smt(addrC addrA addNr add0r).
case (2 = g_) => [<- //= | ?]; first smt(addrC addrA addNr add0r).
case (1 = g_) => [<- //= | ?]; smt(addrC addrA addNr add0r).
qed.

(* prove inp security:
 * for the two receiving parties (g & h), the protocol and simulator
 * are indistinguishable. we cannot include parties i and j in this
 * security proof, since they already know the value of x. therefore,
 * no simulator could generate a share matrix which would fool them.
 *
 * precondition is ugly, maybe could be cleaned up with FSet.
 *)
lemma inp_secure(i_ j_ g_ h_ : party, p : party) :
    equiv[F4.inp ~ Sim.inp :
      ={x, i, j, g, h} /\
      i{1} = i_ /\ j{1} = j_ /\ g{1} = g_ /\ h{1} = h_ /\ 
      uniq [i_; j_; g_; h_] /\ 
      0 <= p < N /\ 0 <= i_ < N /\ 0 <= j_ < N /\ 0 <= h_ < N /\ 0 <= g_ < N
      ==>
      size res{1} = (N, N) /\ size res{2} = (N, N) /\
      view res{1} p = view res{2} p].
proof.
proc.
simplify.
(* first case: Pi or Pj. INP simulator behaves. *)
case (p \in [i_; j_]).
seq 2 3 : (={x,h,i,j,g,r,xh} /\
  p \in [i_; j_] /\ uniq [i_; j_; g_; h_] /\
  i_ = i{2} /\ j_ = j{2} /\ h_ = h{2} /\ g_ = g{2} /\ 0 <= p < N).
rnd{2}.
auto.
wp.
inline F4.jmp.
auto.
rewrite _4p.
progress.
rewrite /view /row !cols_offunm eq_vectorP !size_offunv //=. 
rewrite !lez_maxr //=.
move => share [share_gt0 share_lt4].
rewrite !get_offunv //=.
rewrite !get_offunm; first 2 rewrite rows_offunm cols_offunm //=.
simplify.
rewrite !get_offunm; first 2 rewrite rows_offunm cols_offunm //=.
simplify.
move : H0 H1.
rewrite !negb_or.
elim => inj.
elim => ing inh.
elim => jng jnh.
case (share = p) => [//= | off_diag].
by rewrite add0r.
have -> //= : p <> g{2} by smt().
case (share = i{2}) => [-> //= | share_not_i].
by rewrite inh ing add0r.
case (share = j{2}) => [-> //= | share_not_j].
by rewrite jnh jng //= add0r.
case (share = g{2}) => [-> //= | share_not_g].
by rewrite H2 //= add0r.
have all_uniq : uniq [i{2}; j{2}; g{2}; h{2}].
smt().
case (share = h{2}) => [//= | share_not_h]; by rewrite addrC add0r.

(* end of first case: Pi Pj identical.
 * next, viewing party is ph: share (0, 0, r) *)
case (p = h{2}).
(* r are the same *)
seq 1 1 : (={x,h,i,j,g,r} /\ p = h_ /\ h{1} = h_ /\ h_ <> g_ /\ g_ = g{2} /\ 0 <= g_ < N /\ 0 <= p < N).
auto.
progress; by rewrite eq_sym.
(* party h cannot see xh, so eat it. also eat fake xh. *)
seq 1 2 : (={x,h,i,j,g,r} /\ p = h_ /\ h{1} = h_ /\ h_ <> g_ /\ g_ = g{2} /\ 0 <= g_ < N /\ 0 <= p < N).
rnd{2}.
auto.
(* handle calls to jmp - same, but we can ignore xh, so value is unimportant *)
auto.
inline.
auto.
rewrite _4p.
progress.

rewrite /view /row !cols_offunm lez_maxr // eq_vectorP !size_offunv //=.
rewrite !lez_maxr //.
move => sh [shgt0 shlt4].
rewrite !get_offunv //=.
rewrite !get_offunm; first 2 rewrite rows_offunm cols_offunm //=.
simplify.
rewrite !get_offunm; first 2 rewrite rows_offunm cols_offunm lez_maxr //.
simplify.
case (sh = g{2}) => [-> //= | sh_not_g].
rewrite eq_sym in H.
by rewrite H //= add0r.
case (sh = h{2}) => [//= | sh_not_h]; by rewrite add0r.

(* end of second case: secure against Ph.
   next, viewing party is pg. share (0, 0, g)
   we can't set p = g yet but will later *)
seq 0 2 : (={x,h,i,j,g} /\
  0 <= p < N /\ 0 <= i_ < N /\ 0 <= j_ < N /\ 0 <= g_ < N /\ 0 <= h_ < N /\
  p = g_ /\ p <> h{2} /\ g_ = g{2} /\ h_ = h{2} /\ i_ = i{2} /\ j_ = j{2} /\
  uniq [i_; j_; g_; h_]).
(* eat r on the right. *)
auto.
rewrite _4p.
progress.
smt().
seq 1 1 : (={x,h,i,j,g} /\ xfake{2} = x{2} - r{1} /\
  0 <= p < N /\ 0 <= i_ < N /\ 0 <= j_ < N /\ 0 <= g_ < N /\ 0 <= h_ < N /\
  p = g_ /\ g_ = g{2} /\ h_ = h{2} /\ i_ = i{2} /\ j_ = j{2} /\ uniq [i_; j_; g_; h_]).
rnd (fun u => x{2} - u).
auto.
progress; first 2 by algebra.
sp.
(* jmp call *)
inline; auto.
rewrite _4p.
progress.
rewrite /view /row !cols_offunm lez_maxr // eq_vectorP !size_offunv //=.
move => sh [shgt0 shlt4].
rewrite !get_offunv //= !get_offunm; first 2 rewrite rows_offunm cols_offunm //=.
simplify.
rewrite !get_offunm; first 2 rewrite rows_offunm cols_offunm lez_maxr //=.
simplify.
move : H9 H10.
rewrite !negb_or => /> inj ing inh jng jnh.
case (sh = g{2}) => [//= | sh_not_g].
by rewrite add0r.
case (sh = i{2}) => [-> //= | sh_not_i].
by rewrite inh //= add0r.
case (sh = j{2}) => [-> //= | sh_not_j].
by rewrite jnh //= add0r.
smt(addrC add0r).
qed.

(************************)
(* ADD ******************)
(************************)


(* Prove addition is correct *)
lemma add_correct(x_ y_ : elem) :
    hoare[F4.add_main : x = x_ /\ y = y_
      ==> valid res /\ open res = x_ + y_].
proof.
proc.
seq 1 : (open mx = x_ /\ y = y_ /\ size mx = (N, N) /\ valid mx).
auto.
call (share_correct x_).
auto => />; progress; smt().
seq 1 : (open mx = x_ /\ size mx = (N, N) /\ valid mx /\
         open my = y_ /\ size my = (N, N) /\ valid my).
call (share_correct y_).
(*Validity proof*)
auto.
rewrite _4p.
progress; smt().
wp.
auto => />.
(*Validity proof*)
rewrite _4p.
move => &hr rows_mx cols_mx _ _ diag_mx not_diag_mx_left not_diag_mx_right rows_my cols_my _ _ diag_my not_diag_my_left not_diag_my_right.
progress.
rewrite rows_addm rows_mx rows_my /#.
rewrite cols_addm cols_mx cols_my /#.
rewrite get_addm.
rewrite diag_mx.

have alt4 : a < 4.
move : H0.
by rewrite rows_addm rows_mx rows_my.

progress.
smt().
smt().
smt(add0r).

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

lemma view_linear(x y : matrix, p : party) :
    size x = size y => view (x + y) p = view x p + view y p.
proof.
progress.
rewrite /view /row cols_offunm lez_maxr.
rewrite /max.
case (cols x < cols y); by rewrite cols_ge0.
rewrite eq_vectorP //.
progress.
rewrite size_addv !size_offunv //=.
smt().
rewrite get_addv !get_offunv //=.
smt().
smt().
smt().
by rewrite get_addm.
qed.

lemma add_secure(p : party) :
    equiv[F4.add_main ~ Sim.add :
      ={x, y} /\ 0 <= p < N
      ==>
      view res{1} p = view res{2} p].
proof.
proc.
wp.
call (share_secure p).
call (share_secure p).
auto; progress.
rewrite !view_linear //=; smt().
qed.


(************************)
(* MULT *****************)
(************************)


lemma mult_secure(p: party) :
    equiv[F4.mult ~ Sim.mult :
      ={x, y} /\ 0 <= p < N
      ==>
      view res{1} p = view res{2} p].
proof.
proc.
auto.
call (inp_secure 0 1 2 3 p) => //=.
call (inp_secure 0 2 1 3 p) => //=.
call (inp_secure 0 3 1 2 p) => //=.
call (inp_secure 1 2 0 3 p) => //=.
call (inp_secure 1 3 0 2 p) => //=.
call (inp_secure 2 3 0 1 p).
simplify.
skip.
rewrite _4p /=.
move => &1 &2.
elim.
elim => x12 y12 pbounds.
split; first by smt().

elim => view5eq [p5c1 p5c2 rL5 rR5 [rL5size [rR5size rLR5view]]].
split; first by smt().

elim => view4eq [p4c1 p4c2 rL4 rR4 [rL4size [rR4size rLR4view]]].
split; first by smt().

elim => view3eq [p3c1 p3c2 rL3 rR3 [rL3size [rR3size rLR3view]]].
split; first by smt().

elim => view2eq [p2c1 p2c2 rL2 rR2 [rL2size [rR2size rLR2view]]].
split; first by smt().

elim => view1eq [p1c1 p1c2 rL1 rR1 [rL1size [rR1size rLR1view]]].
split; first by smt().

elim => view0eq [p0c1 p0c2 rL0 rR0 [rL0size [rR0size rLR0view]]].

rewrite !view_linear.
rewrite !cols_addm !rows_addm; smt().
rewrite !cols_addm !rows_addm; smt().
rewrite !cols_addm !rows_addm; smt().
rewrite !cols_addm !rows_addm; smt().
rewrite !cols_addm !rows_addm; smt().
by rewrite !rL0size !rL1size.

rewrite !cols_addm !rows_addm; smt().
rewrite !cols_addm !rows_addm; smt().
rewrite !cols_addm !rows_addm; smt().
rewrite !cols_addm !rows_addm; smt().
rewrite !cols_addm !rows_addm; smt().
by rewrite !rR0size !rR1size.

rewrite x12 y12 rLR0view rLR1view rLR2view rLR3view rLR4view rLR5view.
smt().
qed.

(* possibly use for mult_main_secure, should we ever get that working. *)
lemma view12_equiv (x1 x2 : matrix, i : party, j : int) :
    (size x1 = (N, N) /\ size x2 = (N, N) /\
    0 <= i < N /\ 0 <= j < N /\
    forall (q : party), view x1 q = view x2 q)
    =>
    x1.[i, j] = x2.[i, j].
proof.
rewrite _4p.
progress.
have : view x1 i = view x2 i.
by rewrite H7.
rewrite /view /row !eq_vectorP size_offunv H0 H2 lez_maxr // => vx1.
have : (offunv (fun (i0 : int) => x1.[i, i0], 4)).[j] = 
       (offunv (fun (i0 : int) => x2.[i, i0], 4)).[j] by smt().
by rewrite !get_offunv.
qed.

lemma size_view (m : matrix, p : party) :
    size (view m p) = cols m.
proof.
by rewrite /view size_row.
qed.

(* full share-multiply protocol secure *)
(* does not appear to be provable right now, because mult_secure requires the input
   matrix to be equal, which, after a simulator run of share, is not true.
 *)
lemma mult_main_secure :
    equiv[F4.mult_main ~ Sim.mult_main :
      ={x, y}
      ==>
      view res{1} p = view res{2} p].
proof.
proc.
seq 2 2 : (view mx{1} p = view mx{2} p /\ view my{1} p = view my{2} p
           /\ size mx{1} = (N, N) /\ size my{1} = (N, N)
           /\ size mx{2} = (N, N) /\ size my{2} = (N, N)).
call (share_secure p).
call (share_secure p).
auto.
call (mult_secure p).
auto.
rewrite _4p pbounds //=.
progress.
admit.
admit.
qed.

lemma valid_size(m : matrix) :
    valid m => rows m = N /\ cols m = N.
proof.
rewrite /valid.
smt().
qed.

lemma valid_diag0(m : matrix) :
    valid m => forall a, m.[a, a] = zero.
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

(* Prove pre-shared multiplication is correct *)
lemma mult_correct(x_ y_ : elem) :
    hoare[F4.mult_main : x = x_ /\ y = y_ ==> open res = x_ * y_ /\ valid res].
proof.
proc.
(* expand each sharing, one variable at a time *)
seq 1 : (open mx = x_ /\ y = y_ /\ size mx = (N, N) /\ valid mx).
auto.
call (share_correct x_).
auto => />; progress; smt(_4p).

seq 1 : (open mx = x_ /\ size mx = (N, N) /\ valid mx /\
         open my = y_ /\ size my = (N, N) /\ valid my).
call (share_correct y_).
auto => />; progress; smt(_4p).

(* prove share + multiply is correct *)
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

auto; rewrite _4p. progress.

(* prove two sides open to the same matrix *)
rewrite 6!open_linear.
(* results from INP *)
rewrite H6 H8 H10 H12 H14 H16.
(* local multiply result *)
rewrite /open.
rewrite get_offunm; first by rewrite cols_offunm rows_offunm lez_maxr.
rewrite get_offunm; first by rewrite cols_offunm rows_offunm lez_maxr.
rewrite get_offunm; first by rewrite cols_offunm rows_offunm lez_maxr.
rewrite get_offunm; first by rewrite cols_offunm rows_offunm lez_maxr.
simplify.
algebra.

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
move : H18.
rewrite 6!rows_addm.
rewrite valid_size // valid_size // valid_size //
        valid_size // valid_size // valid_size //.
rewrite _4p //.

clear H18 H20.
rewrite valid_diag0 // valid_diag0 // valid_diag0 //
        valid_diag0 // valid_diag0 // valid_diag0 //.
rewrite get_offunm /= //.
smt(zeroE).

(* 3a. prove columns consistent *)
have plt4 : p < 4.
move : H18.
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

rewrite valid_size // valid_size // valid_size //
        valid_size // valid_size // valid_size //.
rewrite _4p lez_maxr //.

rewrite 6!get_addm.
rewrite get_offunm.
rewrite cols_offunm rows_offunm.
trivial.
simplify.
rewrite 5!get_addm.
rewrite get_offunm.
rewrite cols_offunm rows_offunm lez_maxr //.
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
have plt4 : p < 4.
move : H18.
rewrite 6!rows_addm.
rewrite valid_size // valid_size // valid_size //
        valid_size // valid_size // valid_size //.
rewrite _4p rows_offunm lez_maxr // lez_maxr.

have slt4 : s < 4.
move : H20.
rewrite 6!cols_addm.
rewrite valid_size // valid_size // valid_size //
        valid_size // valid_size // valid_size //.
rewrite _4p cols_offunm lez_maxr // lez_maxr.

rewrite get_offunm.
rewrite rows_offunm cols_offunm.
rewrite 5!rows_addm 5!cols_addm.
rewrite valid_size // valid_size // valid_size //
        valid_size // valid_size // valid_size //.
rewrite _4p.
rewrite rows_offunm cols_offunm.
rewrite valid_size // valid_size // valid_size //
        valid_size // valid_size // valid_size //.
rewrite _4p.
rewrite /max.
simplify.
smt().

simplify.
rewrite 11!get_addm.
rewrite get_offunm.
rewrite cols_offunm rows_offunm.
trivial.
simplify.
rewrite get_offunm.
rewrite cols_offunm rows_offunm.
trivial.
simplify.
simplify.
rewrite H22.
rewrite eq_sym in H21.
rewrite H21.
simplify.
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
