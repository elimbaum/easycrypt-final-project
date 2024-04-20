prover quorum=2 ["Alt-Ergo" "Z3"].
timeout 1.  (* limit SMT solvers to two seconds *)
require import AllCore FSet List Distr.
require import Bool IntDiv.
require import Number StdOrder.
(*---*) import RealOrder. 

const order : { int | 2 <= order } as ge2_order.

require import ZModP. 
clone import ZModField as Zmod with op p <- order.

import Zmod.Sub.
import Zmod.ZModule.

require (*---*) DynMatrix.


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

import Zmod.DZmodP.

op randint : zmod distr = dunifin.

module M = {
  proc f() : zmod = {
    var a, b : zmod;
    a <$ randint;
    b <$ randint;
    return a + b;
  }

  proc g() : zmod = {
    var r : zmod;
    r <$ randint;
    return r;
  }
}.

lemma randint_full: is_full randint by exact dunifin_fu.

lemma randint1E (s : zmod) : mu1 randint s = (1%r / order%r)%Real
  by rewrite dunifin1E cardE.

lemma randint_ll: is_lossless randint by exact dunifin_ll.

lemma randint_funi: is_funiform randint.
proof.
by move=> ??; rewrite !randint1E.
qed.

op rnd_f : zmod -> zmod.
op rnd_g : zmod -> zmod.

axiom f_inv : forall x, rnd_f (rnd_f x) = x.
axiom fg_inv : forall x, rnd_f (rnd_g x) = x.
axiom gf_inv : forall x, rnd_g (rnd_f x) = x.

lemma addS (a b c : zmod) :
    a - b = c <=> a = b + c.
proof.
smt(addrA addrC addNr add0r).
qed.

lemma subrr (x : zmod) :
    x - x = zero.
proof.
smt(addNr add0r).
qed.

lemma subK (a b : zmod) :
  a - (a - b) = b.
proof.
by rewrite addS -addrA addNr addrC add0r.
qed.

lemma indist :
    equiv[M.f ~ M.g : true ==> ={res}].
proof.
proc.
(* consume the first random assignment *)
seq 1 0 : true.
rnd{1}.
auto.
rnd (fun u => a{1} + u) (fun u => u - a{1}).
auto.
progress.
by rewrite -addS.
smt(addrC addrA subrr).
qed.

(* without seq, it doesn't work *)
lemma indist_stuck :
    equiv[M.f ~ M.g : true ==> ={res}].
proof.
proc.
rnd{1}.
rnd (fun u => b{1} + u) (fun u => u - b{1}).
auto; progress.
by rewrite -addS.
smt(addrC addrA subrr).
(* stuck: aL + b0 = a{1} + aL *)
admit.
qed.

op randint2 : int distr.

module M2 = {
  proc f() : int = {
    var a, b : int;
    a <$ randint2;
    b <$ randint2;
    return a + b;
  }

  proc g() : int = {
    var r : int;
    r <$ randint2;
    return r;
  }
}.

lemma indist2 :
    equiv[M2.f ~ M2.g : true ==> ={res}].
proof.
proc.
(* consume the first random assignment *)
seq 1 0 : true.
rnd{1}.
auto.
(* not true: is_lossless randint2 *)
admit.
rnd (fun u => a{1} + u) (fun u => u - a{1}).
auto.
progress.
smt().
(* not true mu1 r = mu1 r - a *)
admit.
(* maybe true: randint full *)
admit.
smt().
qed.
