
prover quorum=2 ["Alt-Ergo" "Z3"].
timeout 2.  (* limit SMT solvers to two seconds *)
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

module T = {
  var m: matrix
  proc f(n : int):unit = {
    m <- offunm (f_share, n, n);
  }
}.

lemma diagonal_equal_zero_check(mat: matrix, n_ : int):
  hoare[T.f: n = n_ /\ 0 <= n_ ==> forall a, mrange mat n_ n_ =>  T.m.[a, a] = 0].
proof.
proc.
auto => />.
progress.
smt(get_offunm).
qed.


(* CODE FOR  i x j matrix 

op f_diag_1 (m n : int) : int = 
  if m = n then 1 else 0.

(*op createMatrix(x y : int): matrix = offunm (f_poly, x, y).*)

module T = {
  var mat_x: matrix
  var mat_y: matrix
  var mat_z: matrix
  var mat_w: matrix
(*
  proc f_diag (i j : int) : int = {
    var b: int;
    if (i = j) {
      b <- 1; 
    } else { 
      b <- 0;
    }
    return b;
  }
*)

(* offunm: function, pass in coordinates range i, j *)
  proc f(i j : int):unit = {
    mat_x <- offunm ( f_diag_1, i, j);
    mat_y <- offunm ( f_diag_1, i, j);
    mat_z <- mat_x + mat_y;
    mat_w <- mat_x - mat_y;
  }
}.

lemma matrix_rows_cols_check(i_ j_ : int):
  (* `rows` returns number of rows. `cols` returns number of cols *)
  hoare[T.f: 0 < i_ /\ 0 < j_ /\ i = i_ /\ j = j_  ==> rows T.mat_x = i_ /\ cols T.mat_x = j_].
proof.
proc.
auto => />.
progress.
smt().
smt().
qed.


lemma sum_matrix_rows_check(i_ j_ : int):
  hoare[T.f: i = i_ /\ 0 < i_ /\  rows T.mat_x =i_ /\ rows T.mat_x = rows T.mat_y ==> rows T.mat_z = i_].
proof.
proc.
auto => />.
progress.
rewrite rows_offunm.
rewrite rows_offunm.
smt().
qed.

lemma sum_matrix_cols_check(j_ : int):
  hoare[T.f: j = j_ /\ 0 < j_ /\ cols T.mat_x =j_ /\ cols T.mat_x = cols T.mat_y ==> cols T.mat_z = j_].
proof.
proc.
auto => />.
progress.
rewrite cols_offunm.
rewrite cols_offunm.
smt().
qed.

lemma difference_matrix_rows_check(i_ j_ : int):
  hoare[T.f: i = i_ /\ 0 < i_ /\  rows T.mat_x =i_ /\ rows T.mat_x = rows T.mat_y ==> rows T.mat_w = i_].
proof.
proc.
auto => />.
progress.
rewrite rows_offunm.
rewrite rows_offunm.
smt().
qed.

lemma difference_matrix_cols_check(j_ : int):
  hoare[T.f: j = j_ /\ 0 < j_ /\ cols T.mat_x =j_ /\ cols T.mat_x = cols T.mat_y ==> cols T.mat_w = j_].
proof.
proc.
auto => />.
progress.
rewrite cols_offunm.
rewrite cols_offunm.
smt().
qed.

(* Matrix with the values of v on the diagonal and zeror off the diagonal *)


(* check bottom corner *)
lemma diagonal_elements_are_one(i_ j_ : int):
  hoare[T.f: 0 <= i_ /\ 0 <= j_ /\ j = j_ /\ i = i_ /\ j_ <> i_ ==>  T.mat_x.[i_, j_] = 0].
proof.
proc.
auto => />.
progress.
rewrite offunm0E.
smt().
trivial.
qed.

lemma diagonal_elements_are_one(i_ j_ : int):
  hoare[T.f: i <> j /\ 0 <= i_ <= i /\ 0 <= j_ <= j /\ j_ <> i_ ==>  T.mat_x.[i_, j_] = 0].
proof.
proc.
auto => />.
progress.
rewrite offunm0E.
apply negbT.
split.
trivial.
qed.
*)


