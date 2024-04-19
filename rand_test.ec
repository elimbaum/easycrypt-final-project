prover quorum=2 ["Alt-Ergo" "Z3"].
timeout 2.  (* limit SMT solvers to two seconds *)
require import AllCore Distr.

op randint : int distr.
axiom randint_ll : is_lossless randint.

(* bitwidth of int *)
op L : int.
axiom ge0_L : 0 <= L.

axiom randint1E (x : int) :
  mu1 randint x = 1%r / (2 ^ L)%r.

axiom uniform_randint : is_uniform randint.

lemma randint_full : is_full randint.
proof.
move => x.
rewrite /support randint1E.
by rewrite RField.div1r StdOrder.RealOrder.invr_gt0 lt_fromint StdOrder.IntOrder.expr_gt0.
qed.

module M = {
  proc f() : int = {
    var a, b : int;
    a <$ randint;
    b <$ randint;
    return a + b;
  }

  proc g() : int = {
    var r : int;
    r <$ randint;
    return r;
  }
}.

op rnd_f : int -> int.
op rnd_g : int -> int.

axiom f_inv : forall x, rnd_f (rnd_f x) = x.
axiom fg_inv : forall x, rnd_f (rnd_g x) = x.
axiom gf_inv : forall x, rnd_g (rnd_f x) = x.

lemma indist :
    equiv[M.f ~ M.g : true ==> ={res}].
proof.
proc.
(* consume the first random assignment *)
rnd{1}.
rnd rnd_f rnd_g.
auto.
progress.
by rewrite fg_inv.
smt(randint1E).
rewrite randint_full.
by rewrite gf_inv.
rewrite randint_ll.
(* ???? *)
admit.
qed.
