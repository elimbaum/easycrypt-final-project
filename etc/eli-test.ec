prover quorum=1 ["Alt-Ergo" "Z3"].
timeout 1.  (* limit SMT solvers to two seconds *)
require import AllCore Distr.


require (*---*) DynMatrix Matrix.


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

import Mat_A.Matrices.

(* p - party
 * s - share
 *
 * semantics: party i does NOT have share i
 *)
op f_share (p s : int) : int =
  if p = s then 0 else s.


(* matrix indexing: (r, c) *)
module T = {
  var m : matrix
 
  proc f(n : int) : unit = {
    m <- offunm (f_share, n, n);
  }
}.

lemma valid_sharing(p_ s_ : int) :
    hoare[T.f : 0 <= s_ < n /\ 0 <= p_ < n ==>
      (s_ = p_ => T.m.[p_, s_] = 0) /\
      (s_ <> p_ => T.m.[p_, s_] = s_)].
proof.
proc.
auto => />.
progress.
smt(get_offunm).
rewrite /f_share.
rewrite get_offunm.
smt().
smt().
qed.
