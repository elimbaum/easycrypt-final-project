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

(* note: maybe use fset instead of list for party determination? *)

module F4 = {
  var x : matrix
  var err : int

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
    (* TODO oops need to factor in p. right now, fixing data owner. *)
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

  proc open(m : matrix) : int = {
    (* consistency check? or precondition? *)
    (* add up party 0 shares, then add P1's x0... make this nicer? *)
    return m.[0, 1] + m.[0, 2] + m.[0, 3] + m.[1, 0];
  }

  proc main(x y : int) : int = {
    var z : int;
    var mx, my, mz : matrix;

    (* assume P1 holds x and P2 holds y *)
    mx <@ share(x, 1);
    my <@ share(y, 2);

    mz <@ mult(mx, my);

    z <@ open(mz);

    return z;
    
  }

  proc share_main(x p : int) : int = {
    var m : matrix;
    var z : int;
    
    m <@ share(x, p);
    z <@ open(m);
    return z;
  }
}.

(* Prove correctness of the sharing scheme. *)
lemma share_correct(x_ p_ int) :
    hoare[F4.share_main : x = x_ /\ p = p_ /\ 0 <= p < n ==> res = x_].
proof.
proc.
inline*.
sp.
seq 6 : (x0 = x_ /\ 0 <= p0 < n /\ size shares = n /\ nth F4.err shares p = 0).
auto; progress.
rewrite size_put; smt(_4p).
rewrite nth_put; smt(_4p).
seq 2 : (sumz shares = x_ /\ x0 = x_ /\ size shares = n).
auto; progress.
(* sum = x *)
rewrite /put.
rewrite H H1 H0 => /=.
admit.
rewrite size_put => //.
(* matrix part *)
auto. progress.
rewrite get_offunm.
rewrite rows_offunm cols_offunm => /=; smt(_4p).
rewrite get_offunm.
rewrite rows_offunm cols_offunm => /=; smt(_4p).
rewrite get_offunm.
rewrite rows_offunm cols_offunm => /=; smt(_4p).
rewrite get_offunm.
rewrite rows_offunm cols_offunm => /=; smt(_4p).
simplify.
(* sum is correct *)
rewrite /sumz.
rewrite _4p in H.
(* something like this *)
rewrite foldr_rcons.
qed.

(* Prove the sharing scheme is secure. *)

(* need lemma valid shares *)

lemma mul_correct(x_ y_ : int) :
    hoare[F4.main : x = x_ /\ y = y_ ==> res = x_ * y_].
proof.
proc.
(* call - how to use invariants?
   or is inline ok?
   need to reason about uniform randomness: argue indist. from rand submatrix *)
inline F4.open.
wp.
seq 1 : (mx).
inline F4.mult.
wp.
inline (6) F4.inp.

inline (1) F4.share.
sp.
seq 1 : (true).
rnd.
rewrite /randint.

auto.
call (_: true).

sp.

qed.

