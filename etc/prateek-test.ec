
prover quorum=2 ["Alt-Ergo" "Z3"].
timeout 2.  (* limit SMT solvers to two seconds *)
require import AllCore Distr.


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

import Mat_A.Matrices.

(* INP is of type prematrix -> int -> int -> premarix*)
(* This can be an option to create the input matrix for INP *)
op f_inp_in (i j : int):int =
  if j = 3 && (i = 0 || i = 1) then j else -1.

(* Important functions in DynMatrix.eca 

1) Constant valued matrix with r rows and c columns 
op matrixc (rows cols: int) (c : R) = offunm ((fun _ _ => c), rows, cols).

2) Matrix with the values of v on the diagonal and zeror off the diagonal 
op diagmx (v : vector) =
  offunm ((fun i j => if i = j then v.[i] else zeror), size v, size v).

3) Matrix with constant values on the diagonal 
abbrev diagc n (c : R) = diagmx (vectc n c).

4) n by n identity matrix 
abbrev onem n = diagc n oner.

5) r by c zero matrix
abbrev zerom r c  = matrixc r c zeror.

6) 0 by 0 matrix also used as error state when there is a size mismatch 
op emptym = zerom 0 0.

7) lifting functions to matrices 
op mapm (f : R -> R) (m : matrix) : matrix = 
  offunm (fun i j => f m.[i, j], rows m, cols m).

8) Gets the n-th row of m as a vector 
op row m n = offunv (fun i => m.[n, i], cols m).

9) Gets the n-th column of m as a vector 
op col m n = offunv (fun i => m.[i, n], rows m).

10) Turns row vector into matrix 
op rowmx (v: vector) = offunm ((fun _ i => v.[i]), 1, size v).

11) turns column vector into matrix 
op colmx (v: vector) = offunm ((fun i _ => v.[i]), size v, 1).

12) Sideways matrix concatenation - aka row block matrices
op catmr (m1 m2: matrix) = 
  offunm ((fun i j => m1.[i, j] + m2.[i, j-cols m1]), 
          max (rows m1) (rows m2), cols m1 + cols m2).

13) Downwards matrix concatenation - aka column block matrices
op catmc (m1 m2: matrix) =
  offunm ((fun i j => m1.[i, j] + m2.[i-rows m1, j]), 
          rows m1 + rows m2, max (cols m1) (cols m2)).

14) Taking a submatrix from row r1 (inclusive) to r2 (exclusive) and
   column c1 (inclusive) to c2 (exclusive). 
   That is m = subm 0 (rows m) 0 (cols m) 
op subm (m: matrix) (r1 r2 c1 c2: int) = 
  offunm ((fun i j => m.[i+r1,j+c1]), r2-r1, c2-c1).

15) Updating one entry of a matrix
op updm (m: matrix) (r c: int) (p: t) = offunm 
  (fun (i j: int) => if i = r /\ j = c then p else m.[i,j], rows m, cols m).

16) dmatrix helper function: construct matrix from list of (column) vectors 
op ofcols r c (vs : vector list) =
  offunm (fun (i j : int) => (nth witness vs j).[i], r, c).

*)


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


lemma diagonal_equal_zero_check(n_ : int):
  hoare[T.f: n = n_ /\ 0 <= n_ ==> forall a, mrange T.m n_ n_ =>  T.m.[a, a] = 0].
proof.
proc.
auto => />.
progress.
smt(get_offunm).
qed.

lemma valid_sharing(n_ : int) :
  hoare [T.f : n = n_ /\  0 < n ==> forall i j, mrange T.m i j /\ i <> j =>  T.m.[i, j] = j].
proof.
proc.
auto => />.
progress. 
rewrite (get_offunm).
smt (get_offunm) .
rewrite /f_share. 
smt ().
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


