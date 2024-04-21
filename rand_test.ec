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

  proc h() : zmod = {
    var a, b, c : zmod;
    a <$ randint;
    b <$ randint;
    c <$ randint;
    return a + b + c;
  }

  proc j(x : zmod) : zmod = {
    var a, b, c, d : zmod;
    a <$ randint;
    b <$ randint;
    c <$ randint;
    return x - (a + b + c);
  }

  proc g() : zmod = {
    var r : zmod;
    r <$ randint;
    return r;
  }

  proc real(x : zmod) : zmod list = {
    var r1 : zmod;
    r1 <$ randint;
    return [r1; x - r1];
  }

  proc simu() : zmod list = {
    var r1, r2 : zmod;
    r1 <$ randint;
    r2 <$ randint;

    return [r1; r2];
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

lemma subD (a b c : zmod) :
    a - (b + c) = a - b - c.
proof.
rewrite addS.
rewrite !addrA.
smt(addrA addrC add0r addNr).
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

lemma ababK (a b x : zmod) :
    a + b + x - a - b = x.
proof.
smt(addrA addrC add0r addNr).
qed.

lemma negnegK (a b : zmod) :
    a - (-b) = a + b.
proof.
rewrite -{1}add0r.
smt(addrA addrC addNr add0r).
qed.

lemma negposK (a b : zmod) :
    a - b = -b + a.
proof.
smt(addrA addrC addNr add0r).
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

lemma indist_h :
    equiv[M.h ~ M.g : true ==> ={res}].
proof.
proc.
seq 2 0 : true.
auto.
rnd (fun u=> a{1} + b{1} + u) (fun u => u - a{1} - b{1}).
auto; progress.
rewrite -addS.
by rewrite subD.
by rewrite ababK.
qed.

lemma addjk (x a b r: zmod) :
    x - a - b + r + a + b - x = r.
proof.
rewrite (addrC (x - a - b)).
rewrite !addrA.
have rk : forall (y : zmod), r + y = r => y = zero.
move => y.
rewrite eq_sym.
rewrite -addS.
smt(addNr addrC).
admit.
qed.

lemma indist_j (x_ : zmod) :
    equiv[M.j ~ M.g : x_ = x{1} ==> ={res}].
proof.
proc.
seq 2 0 : (x_ = x{1}).
auto.
rnd (fun u => (x_ - (a{1} + b{1} + u)))
    (fun (u : zmod) => (-u - a{1} - b{1} + x_)).
auto.
progress.
rewrite !subD.
rewrite !negnegK.
by rewrite addjk.
rewrite !subD.
admit.
qed.

op errL : zmod.
op errR : zmod.

lemma indist_exec_0 (x_ : zmod) :
    equiv[M.real ~ M.simu : x_ = x{1} ==> nth errL res{1} 0 = nth errR res{2} 0].
proof.
proc.
seq 1 1 : (={r1}).
rnd.
auto.
rnd{2}.
auto.
qed.

lemma indist_exec_1 (x_ : zmod) :
    equiv[M.real ~ M.simu : x_ = x{1} ==> nth errL res{1} 1 = nth errR res{2} 1].
proof.
proc.
seq 0 1 : (x_ = x{1}).
rnd{2}.
auto.
rnd (fun u => x_ - u).
auto.
progress.
by rewrite subK.
qed.

lemma indist_exec (x_ : zmod, p : int) :
    equiv[M.real ~ M.simu :
      x_ = x{1} /\ 0 <= p <= 1 ==>
      nth errL res{1} p = nth errR res{2} p].
proof.
proc.
case (p = 0).
seq 1 1 : (={r1} /\ p = 0); auto.
(* p = 1 *)
seq 0 1 : (x_ = x{1} /\ p = 1).
auto. (* by default, runs rnd{2} *)
smt().
rnd (fun u => x_ - u).
auto.
progress.
by rewrite subK.
qed.

(* ---- *)

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
