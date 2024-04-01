(*********************************************************************
 The main results are:
 * Correctness with respect to the input that the adversary is commited to.
   correctness
   this use pi1_spec
 
 * output_simulation
 which builds on pi1_spec, which follows from:
   input_spec
   comp_spec

 * Input independence: 
   input_independence
 which is a consequence of:
   privacy_input_phase
   privacy_computation_phase


 We have used a number of axioms to specify the behavior of the
 adversary.
 They are clearly marked as: axiom.


 We roughly have two types of lemmas, ones connected to privacy (equiv) and
 ones connected to correctness (hoare).

 We abuse witnesses to avoid having to deal with None in the option type.

 We always enfore witness on the diagonal for secret sharings. 
 This is an example of integrity (_integr), which may be seen as
 extra typing information.                                         
*********************************************************************)

require import AllCore Bool List.
require import IntDiv.
require import Distr.
require import ZModFin.
require import StdRing. import RField.
require import StdOrder. import IntOrder.
require import StdBigop Bigalg. import Bigreal Bigreal.BRM.
require import DList DInterval.

import Zp Zp.ZModule Zp.ZModpRing ZModFinType MZModFinite ZModule Zp.ComRing.

require import Util.
require import Vote.

pragma -oldip.

(* -------------------------------------------------------------------- *)
abbrev "_.[_]" ['a] (s : 'a list) (i : int) = nth witness s i.

abbrev vec ['a] (n : int)  (f : int -> 'a) = mkseq f n.

(* We will use arrays based on lists to avoid translating back and forth *)
op "_.[_<-_]" (arr : 'a list) (i : int) (x : 'a) =
  mkseq (fun k => if i = k then x else arr.[k]) (size arr).

lemma get_set_if (arr : 'a list) (x : 'a) (i j : int):
  arr.[i <- x].[j] = if 0 <= i < size arr /\ j = i then x else arr.[j].
rewrite nth_mkseq_if (eq_sym j).
case: (0 <= j < size arr)=> [|^j_out /(nth_out witness) ->].
+ by case: (i = j)=> //= -> // -> //.
+ by case: (i = j)=> [->|//=]; rewrite j_out.
qed. 

lemma size_set (arr : 'a list) (x : 'a) (i : int):
  size arr.[i <- x] = size arr by smt(size_mkseq  size_ge0).

(* -------------------------------------------------------------------- *)
type 'a matrix = 'a list list.
type 'a matrix3 = 'a matrix list.
type 'a matrix4 = 'a matrix3 list.
type 'a matrix5 = 'a matrix4 list.
type 'a matrix6 = 'a matrix5 list.

op square (l : int) (m : 'a matrix) =
  size m = l /\ forall i, 0 <= i < l => size m.[i] = l.

op cube (l : int) (m : 'a matrix3) =
  size m = l /\ forall i, 0 <= i < l => square l m.[i].

op cube4 (l : int) (m : 'a matrix4) =
  size m = l /\ forall i, 0 <= i < l => cube l m.[i].

op cube5 (l : int) (m : 'a matrix5) =
  size m = l /\ forall i, 0 <= i < l => cube4 l m.[i].

op cube6 (l : int) (m : 'a matrix6) =
  size m = l /\ forall i, 0 <= i < l => cube5 l m.[i].

(* -------------------------------------------------------------------- *)
clone import BigComRing as ZmodComRing with
  type t <- zmod,
  op CR.zeror <- Zp.zero,
  op CR.oner  <- Zp.one,
  op CR.( + ) <- Zp.(+),
  op CR.([-]) <- Zp.([-]),
  op CR.( * ) <- Zp.( * ),
  op CR.invr  <- Zp.inv,
  pred CR.unit  <- Zp.unit
  proof * by smt.

import ZmodComRing.BAdd.

(* -------------------------------------------------------------------- *)
abbrev sum = ZmodComRing.BAdd.big predT idfun.
abbrev asum (alpha : zmod list) (l : zmod list) =
  sum (map2 (Zp.( * )) l alpha).

lemma sum_bigi n (l : zmod list) :
  size l = n => sum l = bigi predT (fun i => l.[i]) 0 n.
proof. move=> Hsize; by rewrite (big_nth witness) Hsize. qed.

lemma sum_mkseq F n : sum (mkseq F n) = bigi predT F 0 n.
proof. by rewrite big_map. qed.

lemma sum_plus n (l1 l2 : zmod list) :
  0 <= n => size l1 = n => size l2 = n =>
  sum l1 + sum l2 = sum (mkseq (fun i => l1.[i] + l2.[i]) n).
proof.
move=> ???.
rewrite (sum_bigi n) //.
rewrite (sum_bigi n) //.
rewrite sum_mkseq.
rewrite -big_split.
by apply/eq_big_int=> i hi /=; smt(nth_mkseq).
qed.

lemma sum2E M (m : zmod matrix) : square M m =>
    sum (map sum m)
  = bigi predT (fun i => bigi predT (fun j => m.[i].[j]) 0 M) 0 M.
proof.
case=> [<- sz_m]; rewrite (big_nth witness) size_map.
have ->: predT \o nth witness (map sum m) = predT by done.
rewrite !big_seq; apply/eq_bigr => i /= /mem_range [ge0_i lt_im].
by rewrite (nth_map witness) // (big_nth witness predT idfun) sz_m.
qed.

(* -------------------------------------------------------------------- *)

(* The ideal functionality, which defines the function that we want to securely compute.
   Makes it easier to update the protocol with having to update the lemmas. 
   We want to compute the multiplication of party 0 and party 1's inputs. *)
op idealfct (xs : zmod list) = xs.[0] * xs.[1].

(* -------------------------------------------------------------------- *)
abbrev dzmod = MZModFinite.dunifin.

(* -------------------------------------------------------------------- *)
op N : { int | 3 < N } as gt3_N.

lemma gt0_N : 0 < N by smt(gt3_N).
lemma gt1_N : 1 < N by smt(gt3_N).
lemma ge0_N : 0 <= N by smt(gt3_N).

hint exact : gt0_N ge0_N gt1_N gt3_N size_nseq size_mkseq.
hint rewrite vecdb: nth_mkseq size_mkseq nth_nseq size_nseq.

(* -------------------------------------------------------------------- *)
(* returns the i-th column of the matrix *)
abbrev col M i (m : 'a matrix) : 'a list =
  mkseq (fun j => m.[j].[i]) M.
lemma col3 (m: 'a matrix3) (i j k:int) : 0<=i<N =>(col N k m).[i].[j]=(m.[i]).[k].[j] by smt(nth_mkseq).

(* -------------------------------------------------------------------- *)
(* Auxiliary lemma: sum is invariant by transposition *)
lemma matrix_sum_commutativity (M : int) (m : zmod matrix) :
     0 <= M => square M m
  => sum (map sum m) = sum (mkseq (fun j => sum (mkseq (fun i => m.[i].[j]) M)) M).
proof.
move=> ge0_M sq_M; rewrite (sum2E M _ sq_M) exchange_big sum_mkseq.
by apply/eq_bigr=> i _ /=; rewrite sum_mkseq.
qed.

lemma matrix_asum_commutativity (M : int) (alpha : zmod list) (m : zmod matrix) :
  0 <= M =>
  square M m =>
  size alpha = M =>
  asum alpha (map sum m) = sum (mkseq (fun j => asum alpha (col M j m)) M).
proof.
move => Hm Hsq Halpha.
rewrite (map2_mkseq witness witness _ _ _ M) //; 1:rewrite size_map /#.
pose mx := mkseq (fun i => (mkseq (fun j => alpha.[i] * m.[i].[j]) M)) M.
have eq : map sum mx = mkseq (fun (i : int) => (map sum m).[i] * alpha.[i]) M.
* rewrite map_mkseq // /(\o).
  apply eq_in_mkseq=> i hi /=.
  rewrite (nth_map witness witness) 1:/#.
  rewrite mulr_suml.
  rewrite big_map /(\o) /idfun.
  have hmi : size m.[i] = M by smt().
  rewrite -{3}(mkseq_nth witness m.[i]) hmi.
  rewrite big_map /(\o) /idfun.
  by apply eq_big; smt().
rewrite -eq (matrix_sum_commutativity M mx) //; 1:smt(size_mkseq nth_mkseq).
congr.
apply eq_in_mkseq => i hi //=.
congr.
rewrite (map2_mkseq witness witness _ _ _ M) //; 1:smt(size_mkseq nth_mkseq).
by apply eq_in_mkseq => j hj //=; smt(nth_mkseq).
qed.

(* -------------------------------------------------------------------- *)
op fresh (i,j : int) : int=
  if i=0 then
    (if j=1 then 2 else 1)
  else
    (if j=0 then (if i=1 then 2 else 1) else 0).

lemma fresh_is_fresh : 2 < N =>
  forall i j, 
    0 <= fresh i j < N /\ fresh i j <> i /\ fresh i j <> j by smt().

op fresh3 (i,j,k : int) : int=
  if i=0 then
    (if j=1 then (if k=2 then 3 else 2) 
            else (if k=1 then (if j=2 then 3 else 2) else 1))
  else (* i>0 *)
    (if j=0 then (if i=1 then (if k=2 then 3 else 2) else (if k=1 then (if i=2 then 3 else 2) else 1))
            else (* j>0 *)
    (if k=0 then (if i=1 then (if j=2 then 3 else 2) else (if j=1 then (if i=2 then 3 else 2) else 1))
  else 0)).

lemma fresh3_is_fresh : 3 < N =>
  forall i j k, 
    0 <= fresh3 i j k < N /\ fresh3 i j k <> i /\ fresh3 i j k <> j /\ fresh3 i j k <> k by smt().

(* -------------------------------------------------------------------- *)
(* Auxiliary lemma *)
lemma sum_drop_elem_plus n (l : zmod list) a :
  0 <= n < size l =>
  sum (drop_elem n l) + a =
  sum (mkseq (fun i => if i <> n then l.[i] else a) (size l)).
proof.
move=> hn.
rewrite big_cat -addrA (addrC _ a) addrA.
have : a = idfun a by trivial. move=> ->.
rewrite -big_seq1 -big_cat -big_cat.
congr.
apply (eq_from_nth witness);
first by smt(size_take size_drop size_cat size_mkseq).
rewrite size_cat size_cat /= size_take 1:/# size_drop 1:/# max_ler 1:/#.
move=> i hi.
rewrite nth_mkseq /= 1:/# big_seq1 /idfun.
smt(nth_cat size_cat nth_take size_take nth_drop size_mkseq).
qed.

(* -------------------------------------------------------------------- *)
(* Take a list of additive shares and make replicated shares.
   Add witness in the diagonal.
   In row i, column j we add the jth additive share*)
op mkrepshares (addshares : zmod list) : zmod matrix =
  mkseq (fun i => addshares.[i<-witness]) N.

lemma mkrepshares_type (addshares : zmod list):
    size addshares =N => square N (mkrepshares addshares).
move => sz. split;smt(size_mkseq nth_mkseq size_nseq ge0_N size_set).
qed.

op transpose (m : 'a matrix) : 'a matrix =
  vec N (fun (id : int) => col N id m).
lemma transpose_invol (m : 'a matrix): square N m => transpose (transpose m) =m.
move => sq. 
rewrite  /transpose.
rewrite -(mkseq_nth witness m).
rewrite -(mkseq_nth witness m).
have ->:(size m)=N by smt().
rewrite size_mkseq.
have ->: (max 0 N)=N by smt(ge0_N).
apply eq_in_mkseq => i ibd //=.
rewrite nth_mkseq //=.
rewrite -(mkseq_nth witness m.[i]).
have ->:(size m.[i])=N by smt().
apply eq_in_mkseq => j jbd //=.
smt(nth_mkseq ge0_N).
qed.

lemma transpose_sq (m : 'a matrix): square N m => square N (transpose m) by smt(size_mkseq nth_mkseq ge0_N).

(* Perhaps not needed *)
lemma transpose_unfold (m : 'a matrix): square N m => 
forall i j, 0<=i<N => 0<=j<N => (transpose m).[i].[j] =m.[j].[i] by smt(nth_mkseq).

(* Slightly easier to apply *)
lemma eq_in_mkseq' ['a]:
   forall (f1 f2 : int -> 'a) (n m : int), n=m =>
     (forall (i : int), 0 <= i < n => f1 i = f2 i) => vec n f1 = vec m f2 by smt(eq_in_mkseq).

lemma matrix_unfold (m : 'a matrix): square N m => 
   m = vec N (fun i => vec N (fun j => m.[i].[j])).
progress [-delta].
(* ssr rewriting: https://coq.inria.fr/refman/ssreflect.html#sec563 *)
rewrite -{1}(mkseq_nth witness m).
apply eq_in_mkseq'; first smt().  move => i ibd //=.
rewrite -{1}(mkseq_nth witness m.[i]). smt(eq_in_mkseq').
qed.
pred (\eqm) ['a] (m1 m2 : 'a matrix) =   square N m1 /\   square N m2 /\   
    forall (i j : int),     0 <= i < N => 0 <= j < N =>  m1.[i].[j] = m2.[i].[j]. 
lemma eqmeq (m1 m2 : 'a matrix) : square N m1 => square N m2 => (m1 \eqm m2)= (m1=m2) by smt( matrix_unfold eq_in_mkseq').
lemma meq_eq (m1 m2 : 'a matrix) : square N m1 => square N m2 => (m1 \eqm m2)=> (m1=m2) by smt( matrix_unfold eq_in_mkseq').

abbrev distribute_shares: zmod matrix3 -> zmod matrix3 = transpose.

lemma distribute_shares_type (shares : zmod matrix3): 
      cube N shares => cube N (distribute_shares shares)
by smt(size_mkseq nth_mkseq ge0_N).
hint exact: distribute_shares_type.

(* -------------------------------------------------------------------- *)
(* Ops specific for the multiplication protocol: *)

(* This is used in steps 9--11. *)
op mkrepshares_mult (id : int) (share : zmod) : zmod list =
  mkseq (fun j =>
  if id = j then witness else (if j = 0 then share else Zp.zero)) N.
(* = (nseq N Zp.zero).[0<-share].[id<-witness] *)
lemma mkrepshares_mult_type (id : int) (share : zmod) : size (mkrepshares_mult id share)=N
by smt(size_mkseq nth_mkseq ge0_N).

op distribute_shared_terms : zmod matrix5 ->  zmod matrix5 = map (map distribute_shares).

op rearrange_sharedterms (sharedterms : zmod matrix4) : zmod matrix3 =
   vec N (fun id => 
   vec ((N-1)*N) (fun term =>   
     (* i = term div(%/) N, j = term mod(%%) N *) 
     (* compute indexes i and j, and rearrange sharedterms *)
     sharedterms.[term %/ N].[term %% N].[id])).

(* -------------------------------------------------------------------- *)
(* The local computation of sum. *)
op mklocalsums_M (M : int) (shares : zmod matrix3) : zmod matrix =
  mkseq (fun id =>
  mkseq (fun c  =>
    (* For party c, col c only contains witness*)
    if id = c then witness else
      sum ( col M c shares.[id])) N) N.
  (* Recomputes the underlying additive share *)
op mkaddshares (m : zmod matrix) : zmod list = vec N (fun i => m.[fresh i i ].[i]).

(* Local differences. Used in step 3. *)
op localdiff (i j : int) (shares : zmod matrix3) : zmod matrix3 =
  transpose (vec N (fun sen => if sen=i\/sen=j then nseq N (nseq N witness) else
        (mkrepshares (map2 (fun x y:zmod => x-y) (mkaddshares (transpose shares).[sen]) 
                                                            (mkaddshares (transpose shares).[fresh i j]))))).
(* Pointwise definition
  mkseq (fun rec =>
  mkseq (fun sen =>
  mkseq (fun c (* column*)  => 
    (* For party c, col c only contains witness*)
    if rec = c then witness else
    if sen = i \/ sen = j then witness else
      shares.[rec].[sen].[c] - shares.[rec].[fresh i j].[c]) N) N) N. *)

(* -------------------------------------------------------------------- *)
(* All parties send their share of the result to all other parties.
   The adversary can send possible different shares to the honest parties.
   advc: row i contains the share that the adversary sends to party i. 
   psums: row i contains party i's share of the result (note that the 
   row index by advid contains only witness. *)
op distribute_resshares advid (advc : zmod matrix) (psums : zmod matrix) : zmod matrix3 =
  mkseq (fun id =>
  mkseq (fun i  => if i = advid then advc.[id] else psums.[i]) N) N.

(* -------------------------------------------------------------------- *)
(* Verifiable reconstruction of the result. *)
op reconstruct_vss_one (resshares : zmod matrix) : zmod =
  sum (mkseq (fun j =>
    oget (majority (drop_elem j (col N j resshares)))) N).

op reconstruct_vss (advid : int) (advres : zmod)
                   (resshares : zmod matrix3) : zmod list =
  mkseq (fun id =>
    if id = advid then advres else reconstruct_vss_one resshares.[id]) N.
(* (reconstruct_vss_one resshares.[id]).[advid<-advres] *)

(* -------------------------------------------------------------------- *)
(*  Update the shares as by the protocol:
    - all the honest parties accept the updated values
    - the honest parties delete additive shares that they are not supposed to know 
      (not really, the rest of the protocol should ensure that they never learn those values in the first place )
    - (AND the adversary obtains maximal information )
*)

type reqs = bool list.
type bcast = zmod option list.

op fix (advid : int) (pshares : zmod matrix3) (bx : bcast list) =
  mkseq (fun id =>
  mkseq (fun i  =>
  mkseq (fun j  =>
      if id=j then witness (* set diagonal to witness (should have been witness already before) *)
      else (
      if id <> advid && id = j then
        pshares.[id].[i].[j] (* ignore the broadcasted value *)
      else odflt pshares.[id].[i].[j] bx.[i].[j] )
    ) N) N) N.

op VSS_fix (advid : int) (shares : zmod matrix) (bx : bcast) =
   mkseq (fun id =>
   mkseq (fun j  =>
       if id <> advid && id = j then
         shares.[id].[j] (* ignore the broadcasted value *)
       else odflt shares.[id].[j] bx.[j]
     ) N) N.

(* -------------------------------------------------------------------- *)
module Misc = {
  proc abort() = {
    var x : unit; x <$ dnull;
  }
}.

lemma abort_false_1 : hoare [ Misc.abort : true ==> false ].
proof. by proc; auto; smt(supp_dnull). qed.

lemma abort_false_2 : equiv [ Misc.abort ~ Misc.abort : true ==> false ].
proof. by proc; auto; smt(supp_dnull). qed.

(* -------------------------------------------------------------------- *)
module type QueryProtocol = {
  proc complains(id : int, j : int, parties : int * int) : bool
  proc complains_vss(id : int, j : int, parties : int * int) : bool
}.

(* -------------------------------------------------------------------- *)
module Protocol (Q : QueryProtocol) = {
  proc share_additive(id : int, s : zmod) : zmod list = {
    var mxrd;
    mxrd <$ dlist dzmod (N-1);
    return (s - sum mxrd) :: mxrd;
  }

  proc share_replicated(id : int, s : zmod) : zmod matrix = {
    var addshares : zmod list;
    addshares <@ share_additive(id, s);
    return mkrepshares addshares;
  }

  (* Collect complaints *)
  proc verify(id : int) : reqs = {
    var b, j, k, l;
    var rx = nseq N false;

    j <- 0; while (j < N) {
      k <- 0; while (k < N) {
        l <- 0; while (l < N) {
          if (k <> j /\ l <> j /\ k <> l) {
            b <@ Q.complains(id, j, (k, l));
            if (b) {
              rx <- rx.[j <- true];
            }
          }
          l <- l + 1;
        }
        k <- k + 1;
      }
      j <- j + 1;
    }

    return rx;
  }

  (* verify procedure used in vss_share *)
  proc verify_vss (id : int) : reqs = {
    var b, j, k, l;
    var rx = nseq N false;

    j <- 0; while (j < N) {
      k <- 0; while (k < N) {
        l <- 0; while (l < N) {
          if (k <> j /\ l <> j /\ k <> l) {
            b <@ Q.complains_vss(id, j, (k, l));
            if (b) {
              rx <- rx.[j <- true];
            }
          }
          l <- l + 1;
        }
        k <- k + 1;
      }
      j <- j + 1;
    }

    return rx;
  }

  (* broadcast procedure used in vss_share *)
  proc broadcast_vss(id : int, v : zmod list, bx : reqs) = {
    return mkseq (fun j => bx.[j] ? Some v.[j] : None) N;
  }
}.

(* -------------------------------------------------------------------- *)
module type Adv = {
  proc sharing      (s : zmod) : zmod matrix
  proc complains    (m : zmod matrix, s: zmod, i j pa :int) : bool
  proc complains_vss    (_ : zmod list * zmod * int * int * int) : bool
  proc broadcast    (rq : reqs) : bcast
  proc broadcast_vss    (_ : reqs) : bcast
  proc localsum     (_ : unit) : unit
  proc localdiff    (_ : unit) : unit
  proc localmultsum (_ : unit) : unit
  proc localopening (_ : unit) : unit
  proc local_check_openings (_ : unit) : unit
  proc bxshareofres (_ : zmod matrix) : zmod matrix
  proc getres       (_ : unit) : zmod
 
  (* To model information sent *to* the Adv. *)
  proc recv_shares  (_ : zmod matrix) : unit
  proc recv_rx      (_ : reqs list  ) : unit
  proc recv_bx      (_ : bcast list ) : unit
  proc recv_fixed_shares (_ : zmod matrix) : unit

  proc recv_VSS_share (_ : zmod list) : unit
  proc recv_VSS_rx    (_ : reqs ) : unit
  proc recv_VSS_bx    (_ : bcast ) : unit

  (* mult step 4 *)
  proc sen_shared_diff_distr (_ : int) : zmod matrix
  proc rec_shared_diff_distr (_ : zmod matrix * int) : unit
  proc sen_shared_diff_distr' (_ : unit) : zmod matrix5
  proc rec_shared_diff_distr' (_ : zmod matrix5) : unit

  (* mult step 7 - new *)
  proc sen_open_diff_distr  (_ : unit) : zmod matrix4
  proc rec_open_diff_distr  (_ : zmod matrix4) : unit

  (* 9 *)
  (* proc sen_bx_shares_rep (_ : int) : zmod * zmod
  proc rec_bx_shares_rep (_ : (zmod * zmod) * int) : unit*)
  proc sen_bx_shares_rep (_ : unit) : (zmod * zmod) list
  proc rec_bx_shares_rep (_ : (zmod * zmod) matrix3) : unit
}.

(* -------------------------------------------------------------------- *)
op extract (advid : int) (pshares : zmod matrix3) = col N advid pshares.

(* The adv does not change during the protocol, 
   and the honest parties are not using its id.
op advid:int.
axiom advidbd: 0<= advid <N. *)

module Environment(A : Adv) = {
  var advid   : int
  var pshares : zmod matrix3
  var pshares_vss : zmod matrix

  (* View variables *)
  var initadvshares    : zmod matrix
  var psharesbeforefix : zmod matrix3
  var rx : reqs list
  var bx : bcast list

  var inp : zmod matrix3
  var comp : zmod matrix
  (* Variable to store the adv input share *)
  var advinpsx : zmod list
  var secrets : zmod list
  
  module QP : QueryProtocol = {
    proc complains(id : int, j : int, p : int * int) = {
      var aout = false; var vj, pa;

      if (   (p.`1 <> p.`2)
          /\ (0 <= p.`1 < N /\ j <> p.`1)
          /\ (0 <= p.`2 < N /\ j <> p.`2))
      {
        if (p.`1 = advid || p.`2 = advid) {
          pa   <- (p.`1 = advid) ? p.`2 : p.`1;
          vj   <- pshares.[pa].[id].[j];
          (* This is an optimization - since Adv can decide on the outcome *)
          aout <@ A.complains(pshares.[advid], vj, id, j, pa);
        } else {
          (* We here inline the complaining of 2 honest parties *)
          aout <- pshares.[p.`1].[id].[j] <> pshares.[p.`2].[id].[j];
        }
      }

      return aout;
    }

    (* complains procedure used in vss_share
       Here we use another global variable than in complains, and the type of the variable is a 
       zmod list (instead of a zmod matrix) *)
    proc complains_vss (id : int, j : int, p : int * int) = {
      var aout = false; var vj, pa;

      if (   (p.`1 <> p.`2)
          /\ (0 <= p.`1 < N /\ j <> p.`1)
          /\ (0 <= p.`2 < N /\ j <> p.`2))
      {
        if (p.`1 = advid || p.`2 = advid) {
          pa   <- (p.`1 = advid) ? p.`2 : p.`1;
          vj   <- pshares_vss.[pa].[j];
          (* This is an optimization *)
          aout <@ A.complains_vss(pshares_vss.[advid], vj, id, j, pa);
        } else {
          (* We here inline the complaining of 2 honest parties *)
          aout <- pshares_vss.[p.`1].[j] <> pshares_vss.[p.`2].[j];
        }
      }

      return aout;
    }
  }

  (* Replicated SS for the secret s of party i. *)
  proc do_one_sharing (i : int, s : zmod) : zmod matrix = {
    var shares;
    
    if (i = advid) {
      shares <@ A.sharing(s);
    } else {
      shares <@ Protocol(QP).share_replicated(i, s);
    }

    return shares;
  }
 
  (* Replicated SS for the secrets in list s. *)
  proc do_sharing(s : zmod list) : (zmod matrix) list = {
    var i, shares, repshares;

    (shares, i) <- (nseq N (nseq N (nseq N witness)), 0); while (i < N)
    {
      (* replicated secret sharing for s.[i] *)
      repshares <@ do_one_sharing(i, s.[i]);
      shares <- shares.[i<-repshares];
      i <- i + 1;
    }

    return shares;
  }

  proc verify_shares() : reqs list = {
    var i, rx, rx1;

    (rx1, rx, i) <- (witness, (nseq N witness), 0); while (i < N) {
      rx1 <@ Protocol(QP).verify(i);
      rx  <- rx.[i<-rx1];
      i   <- i + 1;
    }

(* Perhaps:
    (rx1, rx) <- (witness, []); while (size rx < N) {
      rx1 <@ Protocol(QP).verify(size rx);
      rx  <- rcons rx rx1;
    }
*)

    return rx;
  }

  proc broadcast_shares(rx : reqs list) : bcast list = {
    var i, j, bx, bx1;

    (bx1, bx, i) <- ((nseq N witness), (nseq N (nseq N witness)), 0); while (i < N) {
      if (i = advid) {
        bx1 <@ A.broadcast(rx.[i]);
      } else {
        bx1 = mkseq (fun j => rx.[i].[j] ? Some pshares.[i].[i].[j] : None) N;
      }

      (* Verify that all the requests are served, abort the protocol otherwise *)
      j <- 0; while (j < N) {
        if (rx.[i].[j] && bx1.[j] = None)
          Misc.abort();
      }

      bx <- bx.[i<-bx1];
      i  <- i + 1;
    }

    return bx;
  }

  
  proc broadcast_VSS_share(i:int, rx : reqs, shares:zmod matrix) 
    : bcast = {
    var j, bx;

     if (i = advid) {
        bx <@ A.broadcast_vss(rx);
      } else {
        bx <@ Protocol(QP).broadcast_vss(i, shares.[i], rx);
      }

      (* Verify that all the requests are served, abort the protocol otherwise *)
      j <- 0; while (j < N) {
        if (rx.[j] && bx.[j] = None)
          Misc.abort();
      }

    return bx;
  }

  proc vss_share(dlr : int, s : zmod) : zmod matrix = {
    var vss_rx, vss_bx;

    (* Do replicated secret sharing and get a list of sharings
     * shares.[id].[j], where shares.[id] is the share of the replicated 
     * secret sharing that party id receives. *)
    pshares_vss <@ do_one_sharing (dlr, s);

    (* Instrumentation: save adversary's initial shares 
    initadvshares <- shares.[advid];*)

    (* Adversary receives its share *)
    A.recv_VSS_share(pshares_vss.[advid]);

    (* Consistency check: *)

    (* Get all the requests after the complaining phase.
     * The value rx.[id].[j] is the optional complaining
     * request of party `id` for value `v_j`. *)
    vss_rx <@ Protocol(QP).verify_vss(dlr);

    (* Adversary logs the requests since they are public *)
    A.recv_VSS_rx(vss_rx);

    (* Reply the complaints *)
    vss_bx <@ broadcast_VSS_share(dlr,vss_rx,pshares_vss);

    (* Adversary logs the broadcasts *)
    A.recv_VSS_bx(vss_bx);

    (* Fix the parties' views from the bcast'ed values *)
    pshares_vss <- VSS_fix advid pshares_vss vss_bx;

    (* Return the global view *)
    return pshares_vss;
  }
  
  (* The input phase shares the inputs and does consistency check.
     s is a list of secrets. *)
  proc input(s : zmod list) : zmod matrix3 = {
    var shares;

    (* Do replicated secret sharing and get a list of sharings
     * shares.[id].[i].[j], where shares.[id] is the replicated 
     * secret sharing of party id's secret. *)
    shares <@ do_sharing(s);

    (* Instrumentation: save adversary's initial shares *)
    initadvshares <- shares.[advid];

    pshares <- distribute_shares shares;

    (* Instrumentation: save the global view of sent shares *)
    psharesbeforefix <- pshares;

    (* Adversary receives its shares *)
    A.recv_shares(pshares.[advid]);

    (* Consistency check: *)

    (* Get all the requests after the complaining phase.
     * The value rx.[id].[j] is the optional complaining
     * request of party `id` for value `v_j`. *)
    rx <@ verify_shares ();

    (* Adversary logs the requests since they are public *)
    A.recv_rx(rx);

    (* Reply the complaints *)
    bx <@ broadcast_shares(rx);

    (* Adversary logs the broadcasts *)
    A.recv_bx(bx);

    (* Fix the parties' views from the bcast'ed values *)
    pshares <- fix advid pshares bx;

    (* Extract adversary's sharing of its input - important to it do here! *)
    advinpsx <- mkaddshares (extract advid pshares);
    secrets <- s.[advid<-sum advinpsx];
    (* Return the global view *)
    return pshares;
  }

  (* Step 1: Compute and share terms *)
  (* Communication between the parties are hidden inside vss_share *)
  proc mult_term_sharing (a, b : zmod matrix) : zmod matrix5 = {
    var shared_terms_rep : zmod matrix5;
    (* Indexes: *)
    var i, j, sen; (* term a_i*b_j, sender *)
    var valshare <- nseq N (nseq N witness);
    
    (* We build the complete matrix before updating it
       To get ride of side conditions in the proof *)
    shared_terms_rep = nseq N (nseq N (nseq N (nseq N (nseq N witness))));

    (* TODO: we cannot use a procedure call (i.e. vss_share) inside a mkseq.
       Thus, we need to update the matrix afterwards. *)
    i<-0; while (i < N) {
      j<-0; while (j < N) {
        sen<-0; while (sen < N) {
          if (sen <> i /\ sen <> j) { 
            valshare <@ vss_share (sen, a.[sen].[i] * b.[sen].[j]);
            (* Possibly more clever data structures would help here. *)
            shared_terms_rep = 
                (shared_terms_rep.[i<-
                        (shared_terms_rep.[i].[j<-
                            shared_terms_rep.[i].[j].[sen <- valshare]])]);
          } 
          sen <- sen+1;
        }
        j <- j+1;
      }
      i <- i+1;
    }
    return shared_terms_rep;
  }

  proc mult_check_term_sharing (sharedterms_rep_distr : zmod matrix5) : zmod option matrix4 = {
   (* Step 3: Compute the difference *)
    var valj:zmod matrix3; 
    var shared_diff : zmod matrix5;

    (* Step 4: Open differences - part 1: send/distribute shares *)
    var shared_diff_distr : zmod matrix6;
    var valsen : zmod matrix5;

    (* Step 5: Open differences - part 2: transform representation *)
    var shared_diff_trans: zmod matrix6;

    (* Step 6: Open differences - part 3: local opening *)
    var opened_diff_rep;

    (* Step 7: Open differences - part 4: publish the result *)
    var opened_diff_rep_distr<-[]; 
    var valopendiff;

    (* Step 8: Open differences - part 5: determine the value of the openings *)
    var opened_diff;

    (* Step 3: Compute the difference *)
    (* Local computation of the differences between the different sharing of the same term *)
    shared_diff =
      vec N (fun i =>
      vec N (fun j =>
        localdiff i j sharedterms_rep_distr.[i].[j]));
    A.localdiff(); (* Inform the adversary that we perform local computation *)

  (* Step 4: Open differences - part 1: send/distribute shares *)
  (* Communication: the parties communicate and send shares of the values that we need to open *)
    shared_diff_distr = 
      vec N (fun rec => 
      vec N (fun i => 
      vec N (fun j => 
      vec N (fun sen =>
        if (sen = advid) then nseq N (nseq N witness)
        else shared_diff.[i].[j].[sen] ))));

    A.rec_shared_diff_distr'(shared_diff_distr.[advid]);

    valsen <@ A.sen_shared_diff_distr'();

    (* Updating adversary values. *)
    shared_diff_distr = 
      vec N (fun rec => 
      vec N (fun i => 
      vec N (fun j =>
          (shared_diff_distr.[rec].[i].[j]).[advid <- valsen.[rec].[i].[j]])));

  (* Step 5: Open differences - part 2: transform representation *)
  (* Environment changes the representation of the honest parties data *)
     shared_diff_trans <-  
      mkseq (fun rec => 
      mkseq (fun i => 
      mkseq (fun j => transpose (shared_diff_distr.[rec].[i].[j]))
      N)N)N;
 
  (* Step 6: Open differences - part 3: local opening *)
  (* Local computation *)
    opened_diff_rep <-
      mkseq (fun id => 
      mkseq (fun i => 
      mkseq (fun j => 
      mkseq (fun k => 
        reconstruct_vss_one shared_diff_trans.[id].[i].[j].[k])
      N)N)N)N;
    A.localopening(); (* inform the adversary that we perform local openings *)

  (* Step 7: Open differences - part 4: publish the result *)
  (* Compute the values for the honest parties *)
    opened_diff_rep_distr = 
       (mkseq (fun rec => 
       (* The inner loop is !?: opened_diff_rep.[advid<-witness] *)
       (mkseq (fun sen => 
        if (sen=advid) then witness (* dummy value, will be updated below *)
        else opened_diff_rep.[sen]) 
      N)) N);

   (* send values to the adversary *)
     A.rec_open_diff_distr(opened_diff_rep);

   (* receive values from the adversary *)
     valopendiff <@ A.sen_open_diff_distr();
     opened_diff_rep_distr=
        (mkseq (fun rec => (opened_diff_rep_distr.[rec]).[advid<-valopendiff.[rec]]) N);

  (* Step 8: Open differences - part 5: determine the value of the openings *)
  (* Local computation *)
  (* This is not optimal *) 
    opened_diff =
      mkseq (fun rec => 
      mkseq (fun i => 
      mkseq (fun j => 
      mkseq (fun k => 
        majority ( mkseq (fun sen => 
          opened_diff_rep_distr.[rec].[sen].[i].[j].[k]) N))     
      N)N)N)N;
    A.local_check_openings(); (* inform the adversary that we are checking the opened values*)
   return opened_diff;
  }

  proc mult_determine_term_sharing (a,b : zmod matrix, sharedterms_rep_distr : zmod matrix5, opened_diff : zmod option matrix4) 
       : zmod matrix4 = {
  (* Step 9,10,11: Choose sharing of terms *)   
    var bx_shares_rep; var valbx;
  (* Step 9,10,11: Choose sharing of terms *)   
  (* Communication *)
  (* Honest parties. We initiate bx_shares_rep to have the right shape for the loop invariant *)
    bx_shares_rep = 
       (mkseq (fun rec =>
       (mkseq (fun i =>
       (mkseq (fun j => if (forall id, 0<=id<N => forall k, 0<=k<N =>
                    odflt (Zp.one) opened_diff.[id].[i].[j].[k]=Zp.zero%Zp)
            then nseq N witness
            else (mkseq (fun sen => 
                 if (sen=advid) then witness (* dummy value, will be updated below *)
                                else (if sen=i\/i=advid then witness else a.[sen].[i], 
                                      if sen=j\/j=advid then witness else b.[sen].[j])) N))
         N)))N)N);
    A.rec_bx_shares_rep(bx_shares_rep.[advid]); 
    (* rushing adversary receives first and only then sends *)
    valbx <@ A.sen_bx_shares_rep();
    bx_shares_rep = (mkseq (fun rec =>
       (mkseq (fun i =>
       (mkseq (fun j => (bx_shares_rep.[rec].[i].[j]).[advid <-valbx.[rec]]) N))N))N);
    return (*sharedterms: *) (mkseq (fun i =>
       (mkseq (fun j => if (forall id, 0<=id<N => 
            forall k, 0<=k<N => (odflt (Zp.one) opened_diff.[id].[i].[j].[k]=Zp.zero)%Zp)
            then mkseq (fun id => sharedterms_rep_distr.[i].[j].[id].[fresh i j]) N
            else let bx_shares= mkseq (fun rec => 
            (oget (majority (drop_elem i (map fst bx_shares_rep.[rec].[i].[j]))), 
             oget (majority (drop_elem j (map snd bx_shares_rep.[rec].[i].[j]))))) N in
             vec N (fun id => mkrepshares_mult id (map (uncurry ( * )%Zp) bx_shares).[id]))
        N))N);
  }

  proc multiplication (a, b : zmod matrix) : zmod matrix = {
    var known_shared_terms;
    var shared_terms_rep;
    var sharedterms_rep_distr; 
    var opened_diff;
    var sharedterms;

    shared_terms_rep <@ mult_term_sharing(a,b);

    sharedterms_rep_distr <- distribute_shared_terms shared_terms_rep;

    opened_diff <@ mult_check_term_sharing (sharedterms_rep_distr);

    sharedterms <@ mult_determine_term_sharing (a,b,sharedterms_rep_distr, opened_diff);

    known_shared_terms <- rearrange_sharedterms sharedterms;
    A.localmultsum(); (* inform the adversary that we perform local computation*)

    return mklocalsums_M ((N-1)*N) known_shared_terms;
  }

  (* Wrapper around multiplication procedure that extracts two inputs a and b.
     For simplicity we choose a to be party 0's input and b to be party 1's input. *)
  proc computation_mult (pshares : zmod matrix3) : zmod matrix = {
    var comp_mult : zmod matrix;
    (* extract shares of party 0's secret a *)
    (* extract shares of party 1's secret b *)
    comp_mult <@ multiplication(col N 0 pshares,
                                col N 1 pshares);
    return comp_mult;
  }
    
  proc pi1 (s : zmod list) : zmod matrix * zmod matrix3 = {
    var rinp, comp;

    rinp <@ input (s);
    comp <@ computation_mult (rinp);

    return (comp,rinp);
  }
  
  proc output (psums : zmod matrix) : zmod list = {
    var advc, advres, resshares;

    (* Opening of the result:
     * Every party send their share of the result to all other parties.
     * We give the adversary the shares of the honest parties (psums),
     * and ask him to send to each other party his share
     * (i.e. he can send different values to different parties, 
     * thus we get a matrix) *)
    advc <@ A.bxshareofres(psums);

    resshares <- distribute_resshares advid advc psums;

    (* The adversary outputs an (possible arbitrary) value *)
    advres <@ A.getres();

    (* Verifiable reconstruction:
     * Take the result of the computation, and the shares sent by the adversary.
     * Do majority vote, and reconstruction.
     * The output vector (y,...,y) has advres on the position of the adversary. *)
    return reconstruct_vss advid advres resshares;
  }

  (* The addition protocol *)
  proc protocol(s : zmod list) : zmod list = {
    var out;

    (* run the input and computation phase *)
    (comp, inp) <@ pi1 (s);

    (* run the output phase *)   
    out <@ output (comp);
    (* y   <- oget (majority out);*)
     
    return out;
  }
}.

(* -------------------------------------------------------------------- *)
pred addss_private (dlr: int) (j : int) (shares1 shares2 : zmod list) =
     (size shares1 = N /\ size shares2 = N)
  /\ (forall i, 0 <= i < N => (i <> j \/ j = dlr) => shares1.[i] = shares2.[i]).

pred repss_private_honest (advid : int) (rshares1 rshares2 : zmod matrix) =
     square N rshares1 /\ square N rshares2
  /\ forall i j,
       0 <= i < N => 0 <= j < N => j <> advid =>
       rshares1.[i].[j] = rshares2.[i].[j].

(* Used in do_one_sharing_private *)
pred repss_private0 (advid : int) id (m1 m2 : zmod matrix) =
     square N m1 /\ square N m2
  /\ (id = advid => m1 = m2)
  /\ (id <> advid => m1.[advid] = m2.[advid]).

(* repss_list_private_aux *)
pred repss_private_aux (advid : int) l (mx1 mx2 : zmod matrix3) =
   forall id, 0 <= id < l => repss_private0 advid id mx1.[id] mx2.[id].

(* Used in fix_advid, privacy_input_phase *)
(* repss_list_private *)
pred repss_private (advid : int) (mx1 mx2 : zmod matrix) =
   square N mx1 /\ square N mx2 /\ mx1.[advid] = mx2.[advid].
pred repss_list_private (advid : int) (mx1 mx2 : zmod matrix3) =
      mx1.[advid] = mx2.[advid] /\
      forall dlr, 0 <= dlr < N => mx1.[dlr].[advid] = mx2.[dlr].[advid].
      (* i.e. col N advid mx1  = col N advid mx2 *)

(* The structure/invariant of a valid replicated secret sharing *)
pred repss_integr (m : zmod matrix) =
     (square N m) 
  /\ (forall id, 0<=id<N => m.[id].[id]=witness)
  /\ (forall rec1, 0<=rec1<N => 
      forall rec2, 0<=rec2<N => 
      forall c, (0<=c<N /\ c<>rec1 /\ c<>rec2) => 
        m.[rec1].[c]=m.[rec2].[c]). (* each column has the same value in all entries (except the diagonal) *)

lemma mkrepshares_integr l: size l=N => repss_integr (mkrepshares l) by
smt(nth_mkseq size_mkseq ge0_N size_nseq nth_nseq).

lemma repss_integr_transpose (m : zmod matrix3): 
      (forall i, 0<=i<N => repss_integr m.[i]) => forall i, 0<=i<N => repss_integr (col N i (transpose m)).
move=> hyp i ibd.
split; split ; smt(nth_mkseq size_mkseq).
qed.

lemma size_mkaddshares (m:zmod matrix): square N m => size (mkaddshares m)=N by
smt(size_mkseq ge0_N size_nseq nth_nseq).

lemma mkaddshares_mkrepshares l: size l= N => (mkaddshares (mkrepshares l))=l.
move => sz. rewrite /mkaddshares /mkrepshares.
have efn := (eq_from_nth<:zmod> witness).
apply efn. smt(size_mkseq gt0_N).
rewrite size_mkseq. have -> :max 0 N=N by smt(gt0_N).
smt(gt1_N nth_mkseq get_set_if fresh_is_fresh).
qed.

lemma mkrepshares_mkaddshares (m: zmod matrix) :
    repss_integr m  => (mkrepshares (mkaddshares m))=m.
move => intg. rewrite /mkaddshares /mkrepshares.
apply meq_eq => //=. 
smt( nth_mkseq size_mkseq ge0_N size_set size_set).
smt( nth_mkseq size_mkseq ge0_N size_set size_set).
split. smt( nth_mkseq size_mkseq ge0_N size_set size_nseq nth_nseq size_set).
split. smt( nth_mkseq size_mkseq ge0_N size_set size_nseq nth_nseq size_set).
move => i j ibd jbd. rewrite nth_mkseq //=.
smt( nth_mkseq size_mkseq ge0_N size_set size_nseq nth_nseq size_set fresh_is_fresh). 
qed.

lemma mkadd_recon: forall m, repss_integr m => sum (mkaddshares m) = reconstruct_vss_one m.
move => m repi. rewrite /reconstruct_vss_one /mkaddshares.
congr. apply eq_in_mkseq => j jbd /=. 
rewrite (majority_all _ (m.[fresh j j].[j])) //=.  smt(size_mkseq nth_mkseq size_drop_elem gt3_N).
rewrite all_cat //=. split. apply (all_take witness); smt(nth_mkseq). apply (all_drop witness); smt(all_drop size_mkseq nth_mkseq).
qed.

lemma recon_mkadd: forall l, size l = N => sum l = reconstruct_vss_one (mkrepshares l).
move => l sz. rewrite -mkadd_recon //. by apply mkrepshares_integr. by rewrite mkaddshares_mkrepshares.
qed.

(* -------------------------------------------------------------------- *)
pred repss_correct (advid : int) (sx : zmod list) (mx : zmod matrix3) =
  forall id, 0 <= id < N => id <> advid => sum (mkaddshares mx.[id]) = sx.[id]. 
pred repss_correct1 (s : zmod) (mx : zmod matrix) =
  repss_integr mx => sum (mkaddshares mx) = s.

lemma nth_map2 ['c, 'b, 'a]:
  forall (f : 'a -> 'b -> 'c) (n : int) (s : 'a list) (t : 'b list),
     forall m, m=size s => m=size t => 
     0 <= n < m => (map2 f s t).[n] = f (s.[n]) (t.[n]).
admitted. (* Straight forward *)

lemma sum_diff (n:int) ( l k: zmod list):  size l = n => size k = n =>
     sum (map2 (fun (x y : zmod) => (x - y)%CR) l k) = (sum l - sum k)%CR.
admitted. (* Straight forward *)

lemma  col_transpose (m: 'a matrix): square N m => forall i, 0<=i<N =>  col N i (transpose m)=m.[i].
move => sq i ibd. rewrite matrix_unfold //=. 
smt(eq_in_mkseq nth_mkseq size_mkseq).
qed.

lemma eqcol_eq: forall (m1 m2 : (zmod list) matrix), square N m1 => square N m2 => 
     (forall c, 0<=c<N => (col N c m1) = (col N c m2)) => m1 = m2.
  move => m1 m2 sq1 sq2 hyp. rewrite -eqmeq //= /(\eqm). split; first trivial. split; first trivial.
  move => k l kbd lbd. have ->: m1.[k].[l]=(col N l m1).[k]; smt(nth_mkseq).
qed.

(* properties of localdiff *)
lemma localdiff_integr i j shares:
  forall sen, 0 <= sen < N => sen <> i => sen <> j =>
  repss_integr (col N sen         shares) =>  
  repss_integr (col N (fresh i j) shares) =>
  repss_integr (col N sen (localdiff i j shares)).
progress [-delta].
rewrite /localdiff. 
split. split. rewrite col_transpose //=. split; smt(size_mkseq nth_mkseq size_nseq transpose_sq nth_nseq). 
smt(size_mkseq nth_mkseq size_nseq transpose_sq nth_nseq). 
move => i0 i0bd.
do 4!rewrite nth_mkseq //=. rewrite H1 H2 //=. pose l:=(map2 _ _ _). have sz:(size l=N) by smt(size_map2 size_mkseq).
  have tmp:=(mkrepshares_integr l sz); smt().
split. rewrite col_transpose //=.  split; smt(size_mkseq nth_mkseq size_nseq transpose_sq nth_nseq).  
rewrite nth_mkseq //=. 
rewrite H1 H2 //=. move => id idbd. do 2!rewrite nth_mkseq //=. pose l:=(map2 _ _ _). 
have sz:(size l=N) by smt(size_map2 size_mkseq).
have tmp:=(mkrepshares_integr l sz); smt().
move => rec1 rec1bd rec2 rec2bd c [cbd cond].
rewrite col_transpose //=. split; smt(size_mkseq nth_mkseq size_nseq transpose_sq nth_nseq). 
rewrite nth_mkseq //=. rewrite H1 H2 //=.
rewrite !nth_mkseq //=. smt( fresh_is_fresh).
rewrite  !get_set_if. rewrite size_map2 size_mkaddshares //=. 
smt( mkrepshares_type size_mkseq nth_mkseq size_nseq transpose_sq nth_nseq size_map2). 
smt( mkrepshares_type size_mkseq nth_mkseq size_nseq transpose_sq nth_nseq size_map2). 
smt( mkrepshares_type size_mkseq nth_mkseq size_nseq transpose_sq nth_nseq size_map2). 
rewrite rec1bd rec2bd.
have -> :(c<>rec1) by smt(). simplify.
by have -> :(c<>rec2) by smt(). 
qed.

lemma localdiff_correct i j shares s1 s2:    
  forall sen, 0 <= sen < N => sen <> i => sen <> j =>
  repss_integr (col N sen         shares) =>  
  repss_integr (col N (fresh i j) shares) =>  
  repss_correct1 s1 (col N sen         shares) =>
  repss_correct1 s2 (col N (fresh i j) shares) =>
  repss_integr (col N sen (localdiff i j shares)) /\
  repss_correct1 (s1 - s2) (col N sen (localdiff i j shares)).
move => sen senbd neqi neqj repsen repfr cors1 cors2. 
split. apply localdiff_integr => //=.
move => repdi. rewrite -cors1 // -cors2 //.
rewrite /localdiff.  
rewrite col_transpose //=. split; smt(size_mkseq nth_mkseq size_nseq transpose_sq nth_nseq).
rewrite !nth_mkseq //=.  smt( fresh_is_fresh).
rewrite !nth_mkseq //=. rewrite neqi neqj //=.
rewrite mkaddshares_mkrepshares //=. smt(size_map2 size_mkaddshares).
pose l:=(mkaddshares _). pose k:=(mkaddshares _).
apply (sum_diff N); smt(size_mkaddshares).
qed.

lemma localdiff_correct_zero i j shares:
  forall sen, 0 <= sen < N => sen <> i => sen <> j =>
  repss_integr (col N sen         shares) =>  
  repss_integr (col N (fresh i j) shares) => 
  sum (mkaddshares (col N sen shares)) = sum (mkaddshares (col N (fresh i j) shares)) =>
  repss_integr (col N sen (localdiff i j shares)) /\
  repss_correct1 Zp.zero (col N sen (localdiff i j shares)).
move => sen senbd neqi neqj repsen repfr eq. 
split. apply localdiff_integr => //=.
move => repdi. rewrite /localdiff.
rewrite col_transpose //=. split; smt(size_mkseq nth_mkseq size_nseq transpose_sq nth_nseq).
rewrite !nth_mkseq //=.  smt( fresh_is_fresh).
rewrite !nth_mkseq //=. rewrite neqi neqj //=.
rewrite mkaddshares_mkrepshares //=. smt(size_map2 size_mkaddshares).
move: eq.
pose l:=(mkaddshares _). pose k:=(mkaddshares _).
move => eq. have <-:sum l-sum k =Zp.zero. smt.
apply (sum_diff N); smt(size_mkaddshares).
qed.

(* -------------------------------------------------------------------- *)
section S.

declare module A : Adv { Environment }.
local module E = Environment(A).

(* We assume that the adversaries shares are well-formed *)
axiom Awf : hoare [ A.sharing : true ==> square N res /\ (forall k, 0 <= k < N => res.[k].[k] = witness) ].

(* The distribution of what Adv sends on equal inputs is the same for two runs of the program.
   This is necessary for the privacy statement to hold. 
   Moreover, Adv outputs a square matrix with witness on diagonal *)
axiom A_sharing_consistent :
   equiv [ A.sharing~A.sharing :
       ={glob A,s}
   ==>
       ={glob A, res}
    /\ square N res{1}
    /\ square N res{2}
    /\ (forall i, 0 <= i < N => res{1}.[i].[i] = witness)
    /\ (forall i, 0 <= i < N => res{2}.[i].[i] = witness)  ].

(* If the adv does not complain about an additive share, then that share is consistent with its own knowledge of it. *)
axiom Acomplains: forall i0 j0 pa0, 
   hoare [A.complains: i=i0 /\ j=j0 /\ pa=pa0 ==> !res =>
     ( 0 <= i0 < N
    /\ 0 <= j0 < N => 
    Environment.pshares.[Environment.advid].[i0].[j0] = Environment.pshares.[pa0].[i0].[j0])].

axiom Acomplains2: forall i0 i1 j0 j1 pa0 pa1, 
   equiv [A.complains~A.complains: i{1}=i0 /\ j{1}=j0 /\ pa{1}=pa0 /\
                                   i{2}=i1 /\ j{2}=j1 /\ pa{2}=pa1 /\ ={glob A}
         ==> ={glob A,res} /\
      (   0 <= i0 < N /\ 0 <= i1 < N
       /\ 0 <= j0 < N /\ 0 <= j1 < N 
       /\ 0 <= pa0 < N /\ 0 <= pa1 < N  => 
   (!res{1} => Environment.pshares{1}.[Environment.advid{1}].[i0].[j0] = Environment.pshares{1}.[pa0].[i0].[j0])
            /\ Environment.pshares{1}.[Environment.advid{2}].[i0].[j0] = Environment.pshares{2}.[pa0].[i0].[j0])].
    
(* If there is no complaint about the j-th share of the adversary, then that share is consistent within pshares.
   If there is a complaint about the j-th share of the adversary, then the adversary broadcasts the share that it has stored in pshares.[advid].[advid].[j]. Note that this is an assumption that restricts the adversary's power: It means that the adversary cannot choose that share to broadcast adaptively. However, this issue can be fixed by calling the adversary before making the broadcasts and update pshares.[advid].[advid].[j] according to the output.  *)
axiom Abroadcast rq0 : hoare [A.broadcast: rq=rq0 ==> size res=N /\ (forall j k l, 
    0 <= j < N => 
    ( 0 <= k < N
    /\ 0 <= l < N /\
   !rq0.[j] => Environment.pshares.[k].[Environment.advid].[j] = Environment.pshares.[l].[Environment.advid].[j])
    /\ (res.[j] = None <=> ! rq0.[j])
(*    /\ (rq0.[j] => res.[j] = Some Environment.pshares.[Environment.advid].[Environment.advid].[j])not true if Adv tries to cheat, that is the whole point of calling A.broadcast  *)) ].

axiom Abroadcast2 rq1 rq2 : equiv [A.broadcast~A.broadcast: rq1 = rq2 /\ rq{1}=rq1 /\ ={glob A}==> 
    ={res, glob A}/\ size res{1}=N /\ (forall j k l, 
    0 <= j < N => 
    ( 0 <= k < N
    /\ 0 <= l < N /\
   !rq1.[j] => Environment.pshares{1}.[k].[Environment.advid{1}].[j] = Environment.pshares{1}.[l].[Environment.advid{1}].[j])
    /\ (res{1}.[j] = None <=> ! rq1.[j])
(*    /\ (rq1.[j] => res{1}.[j] = Some Environment.pshares{1}.[Environment.advid{1}].[Environment.advid{1}].[j]) *) )].

(* -------------------------------------------------------------------- *)
(* --- Lemmas for Additive Secret Sharing --- *)

(* Secrecy of additive secret sharing agains N-1 colluding parties. *)
local lemma share_additive_private dlr j :
  0 <= j < N =>
  equiv [ Protocol(E.QP).share_additive ~ Protocol(E.QP).share_additive :
          ={id}/\ id{1} = dlr /\ (j=dlr =>={s})  ==> addss_private dlr j res{1} res{2} ].
proof. 
move=> lt_jN; proc; exists* s{1}, s{2}; elim*=> s1 s2 /=.
have hsz : forall (s : zmod list),
  s \in dlist dzmod (N-1) <=> (size s = N-1).
+ move=> s; have h := supp_dlist dzmod (N-1) s _; 1:smt().
  split=> [/h [//]|szs]; apply/h; split=> //; apply/allP.
  by move=> x _; rewrite dunifin_fu.
case (j=dlr). rnd. skip. smt(gt1_N).
pose F := fun i => if i+1 = j then s2 - s1 else Zp.zero.
pose f := fun (l : zmod list) => mkseq (fun i => l.[i] + F i) (N-1).
pose g := fun (l : zmod list) => mkseq (fun i => l.[i] - F i) (N-1).
have hszmk : forall (Z : int -> zmod), size (mkseq Z (N-1)) = N-1.
+ by move=> Z; rewrite size_mkseq max_ler // [smt(gt1_N)].
have c1 : forall (l : _ list), size l = N-1 => f (g l) = l.
+ move=> s szs; apply/(eq_from_nth witness); 1:smt().
  move=> i; rewrite hszmk => lti.
  by do! rewrite !nth_mkseq //=; ringeq.
rnd f g => /=; skip=> &1 &2 |>. move => eqsec jneqid; split; 1:smt(gt1_N).
move=> _; split=> [s /hsz szs|].
+ rewrite !dlist1E 1,2:[smt(gt1_N)] szs hszmk /=.
  have: exists c, forall x, c = mu dzmod (pred1 x).
  - exists (mu dzmod (pred1 witness)) => x.
    by rewrite !dunifin1E.
  case=> c eqc; rewrite -(BRM.eq_bigr _ (fun _ => c)) //.
  rewrite big_const -(BRM.eq_bigr _ (fun _ => c)) //.
  by rewrite big_const; congr; rewrite !count_predT hszmk.
move=> _ s /hsz szs. split; first by apply/hsz; rewrite hszmk.
move=> _; split; first apply/(eq_from_nth witness) => [|i].
+ by rewrite hszmk.
+ by rewrite szs => lti; do! rewrite !nth_mkseq //=; ringeq.
move=> _; split=> /=; first by rewrite hszmk szs /#.
move=> i ltiN [ne_ij|eq]; last by trivial. case: (i = 0) => [->>|nz_i]; last first.
+ by rewrite nth_mkseq 1:/# /= /F -addzA /= ne_ij addr0.
rewrite !(big_nth witness<:zmod>) predT_comp /(\o) /idfun /=.
rewrite hszmk szs; rewrite !(bigD1 _ _ (j-1)) /= ?range_uniq.
+ by rewrite mem_range /#.
+ by rewrite mem_range /#.
rewrite 2!opprD 2!addrA; congr; last first. (* addrA => too slow *)
+ congr; rewrite !(big_seq_cond (predC1 _)) /=.
  apply/eq_bigr=> k /= @/predC1 [/mem_range ltk ne_k_pj].
  by rewrite nth_mkseq 1:/# /= /F (_ : k+1 <> j) 1:/# addr0.
by rewrite nth_mkseq 1:/# /= /F -addzA /=; ringeq.
qed.

(* Correctness of additive secret sharing. *)
local lemma share_additive_correct s0 :
  hoare [ Protocol(E.QP).share_additive :
    s = s0 ==> size res = N /\ sum res = s0 ].
proof.
proc.
auto=> |> &1 mx H.
have hsz : forall (s : zmod list),
  s \in dlist dzmod (N-1) <=> (size s = N-1).
+ move=> s; have h := supp_dlist dzmod (N-1) s _; 1:smt(gt1_N).
  split=> [/h [//]|szs]; apply/h; split=> //; apply/allP.
  by move=> x _; rewrite dunifin_fu.
split; first by smt(gt1_N).
by rewrite big_cons /predT /idfun /=; ringeq.
qed.

(* -------------------------------------------------------------------- *)

(* --- Lemmas for Replicated Secret Sharing --- *)

(* Correctness of replicated secret sharing *)
local lemma share_replicated_integr s0 :
  hoare [ Protocol(E.QP).share_replicated :
    s = s0 /\ 0 <= id < N ==>
    repss_integr res /\ reconstruct_vss_one res = s0 ].
proof.
proc.
have efn := (eq_from_nth<:zmod> witness).
call (share_additive_correct s0)=> //.
auto. progress [-delta]. smt(size_mkseq nth_mkseq gt1_N).
rewrite /reconstruct_vss_one /mkrepshares.
congr. apply efn. smt(size_mkseq). rewrite size_mkseq. move => i idbd.
rewrite nth_mkseq 1:/# //=.
have tmp: (majority
     (drop_elem i
        (col N i (vec N (fun (i0 : int) => result.[i0 <- witness]))))) =
      Some result.[i]; last smt().
have ->:(col N i (vec N (fun (i0 : int) => result.[i0 <- witness]))=
          (nseq N result.[i]).[i <- witness]).
smt(size_mkseq size_nseq nth_mkseq nth_nseq).
have sz1:(size (nseq N result.[i]).[i <- witness]=N) by smt(size_nseq size_mkseq).
have sz2:(size (drop_elem i (nseq N result.[i]).[i <- witness])=N-1) by smt(size_drop_elem). 
apply majority_all. smt(gt3_N size_drop_elem size_mkseq size_nseq).
rewrite -all_pred1P sz2.
smt(nth_nseq nth_mkseq size_nseq nth_drop_elem size_drop_elem size_mkseq gt3_N).
qed.

(* We probably don't need i *)
(* Secrecy of replicated secret sharing against 1 corruption *)
local lemma share_replicated_private i advid :
  0 <= advid < N =>
  equiv [ Protocol(E.QP).share_replicated ~ Protocol(E.QP).share_replicated :
      ={id} /\ i = id{1} /\ (advid<>i ) ==>
      repss_private advid res{1} res{2}
   /\ repss_integr res{1}
   /\ repss_integr res{2} ].
proof.
move=> Hadvid; proc.
call (share_additive_private i advid Hadvid). 
skip => &1 &2; smt(size_mkseq nth_mkseq eq_in_mkseq).
qed.

(* -------------------------------------------------------------------- *)

(* --- Lemmas for do_one_sharing --- *)
local lemma do_one_sharing_integr id sinp :
  hoare [ E.do_one_sharing :
      sinp = s /\ id = i /\ 0 <= id < N /\ 0 <= E.advid < N
      ==>
      square N res /\
      (id <> E.advid => repss_integr res /\
      reconstruct_vss_one res = sinp )].
proof.
proc.
if; first by call Awf; auto; smt().
by call (share_replicated_integr sinp); auto; smt(). 
qed.

local lemma do_one_sharing_private id:
  equiv [ E.do_one_sharing ~ E.do_one_sharing :
      ={glob A, E.advid, i} /\ id = i{1} /\ 0 <= E.advid{1} < N
   /\ (i{1} = E.advid{1} => ={s})
      ==>
      ={glob A, E.advid}
   /\ repss_private E.advid{1} res{1} res{2}
   /\ (id = E.advid{1} => ={res})
   /\ (id<> E.advid{1} => repss_integr res{1}) 
   /\ (id<> E.advid{1} => repss_integr res{2}) ].
proof.
proc.
conseq
  (_ : ={glob A, E.advid, i} /\ id = i{1} /\ 0 <= E.advid{1} < N /\ (i{1} = E.advid{1} => ={s})
    ==> _).
if; 1:by [].
+ conseq
    (_ :  ={glob A, E.advid, i, s} ==> ={glob A, E.advid, i, s, shares})
    (_ : true ==> square N shares)
    (_ : true ==> square N shares) => //;
  1,2: by call Awf.
  - by call (_ : true); auto.
+ exists* E.advid{1}; elim*=> advid.
  case @[ambient]: (0 <= advid < N); last first.
  * move=> ?; call (_ : true); first by inline *; auto.
    by skip=> &1 &2 |> /#.
  move=> hadv.
  call (share_replicated_private id advid hadv). auto; smt().
qed.

(* -------------------------------------------------------------------- *)

(* --- Lemmas for do_sharing --- *)

local lemma do_sharing_integr advid sx :
  hoare [ E.do_sharing :
      sx = s
   /\ E.advid = advid /\ 0 <= E.advid < N
      ==>
      E.advid = advid
   /\ (cube N res ) /\ 
      (forall id, 0 <= id < N =>
        id <> E.advid => repss_integr res.[id])
   /\ (forall id, 0 <= id < N => id <> E.advid =>repss_correct1 sx.[id] res.[id]) ].
proof.
proc; sp.
while (  
     E.advid = advid
  /\ s = sx
  /\ 0 <= E.advid < N
  /\ 0 <= i <= N
  /\ cube N shares
  /\ (forall id, 0 <= id < i =>
        id <> E.advid => repss_integr shares.[id])
  /\ (forall id, 0 <= id < i => id <> E.advid =>repss_correct1 sx.[id] shares.[id]));
last skip;smt(size_nseq nth_nseq).
wp.
exists* i; elim*=> ii. 
call (do_one_sharing_integr ii sx.[ii]).
auto=> &1 |>. progress [-delta]. smt(). smt(). smt(size_set size_mkseq nth_mkseq). 
smt(size_mkseq nth_mkseq nth_rcons size_set).
move => id0.
rewrite /repss_correct1 in H5. search mkaddshares.
case (id<i{1}); first smt(get_set_if). 
move => eq. move: H8. have ->: i{1}=id by smt(). move => H8.
rewrite get_set_if. 
have ->  : (0 <= id < size shares{1})=true by smt().
simplify.
smt(mkadd_recon).
qed.

(* The sharing of all the inputs (including the adversary's) fulfil privacy.
   I.e. the adversary gets one share of each of the other party's secrets.
   But it reveals no information about the honest parties input. *)
local lemma do_sharing_private s1 s2 advid:
  equiv [ E.do_sharing ~ E.do_sharing :
      ={glob A, E.advid} /\ 0 <= E.advid{1} < N
   /\ s{1}.[E.advid{1}] = s{2}.[E.advid{1}]
   /\ s{1}=s1 /\ s{2}=s2 /\ E.advid{1}=advid
      ==>
      ={glob A, E.advid} /\ 0 <= E.advid{1} < N
   /\ cube N res{1} /\ cube N res{2}
   /\ res{1}.[E.advid{1}] = res{2}.[E.advid{2}] (* shares that Adv sends are same *)
   /\ (forall id, 0 <= id < N =>  (* shares that Adv receives are same *)
        repss_private E.advid{1} res{1}.[id] res{2}.[id])
   /\ (forall id, 0 <= id < N => id <> E.advid{1} => repss_integr res{1}.[id])  (* These really should be separate lemma. *)
   /\ (forall id, 0 <= id < N => id <> E.advid{1} => repss_integr res{2}.[id])
  ].
proof.
conseq (_: ={glob A, E.advid} /\ 0 <= E.advid{1} < N
   /\ s{1}.[E.advid{1}] = s{2}.[E.advid{1}]
      ==>
      ={glob A, E.advid} /\ 0 <= E.advid{1} < N
   /\ res{1}.[E.advid{1}] = res{2}.[E.advid{2}] 
   /\ (forall id, 0 <= id < N => 
        repss_private E.advid{1} res{1}.[id] res{2}.[id]))
      (do_sharing_integr advid s1)
      (do_sharing_integr advid s2) => //=.
proc; wp; sp.
while (
     ={glob A, E.advid, i}
  /\ 0 <= i{1} <= N /\ 0 <= E.advid{1} < N
  /\ cube N shares{1} /\ cube N shares{2}
  /\ (s{1}.[E.advid{1}] = s{2}.[E.advid{2}])
  /\ repss_private_aux E.advid{1} i{1} shares{1} shares{2}
); last by skip;smt(size_nseq size_mkseq nth_mkseq nth_nseq). 
wp; exists* i{1}; elim*=> i.
call (do_one_sharing_private i).
skip=> &1 &2;smt(size_nseq size_mkseq nth_mkseq nth_nseq). 
qed.

(* -------------------------------------------------------------------- *)
(* We represent the maximal knowledge the adv has *)
pred reqs_pshares_compat (rx : reqs list) (pshares : zmod matrix3) =
  square N rx  /\
  forall id, 0 <= id < N =>
    forall j k l,
      0 <= j < N => 0 <= k < N => 0 <= l < N =>
      k <> j => l <> j => 
      ! rx.[id].[j] =>
      pshares.[k].[id].[j] = pshares.[l].[id].[j].

(* -------------------------------------------------------------------- *)
pred reqs_integr (advid : int) (rx : reqs list) =
  forall i j,
    0 <= i < N => 0 <= j < N => i <> advid => rx.[i].[j] => j <> advid.

(* -------------------------------------------------------------------- *)
(* Verify_shares *)
local lemma verify_shares_integr (shares : zmod matrix3) :
  hoare [ E.verify_shares :
          0 <= E.advid < N
       /\ (forall id, 0 <= id < N => id <> E.advid => repss_integr shares.[id])
       /\ E.pshares = distribute_shares shares
      ==>
          E.pshares = distribute_shares shares
       /\ reqs_integr E.advid res
       /\ reqs_pshares_compat res E.pshares
       /\ square N res].
admitted. (* Same as for additive case *)

local lemma verify_shares_private (shares1 shares2 : zmod matrix3) :
  equiv [ E.verify_shares ~ E.verify_shares :
           ={glob A, E.advid}
        /\ shares1.[E.advid{1}] = shares2.[E.advid{2}] (* shares that Adv sent are same *)
        /\ (forall id, 0 <= id < N =>  (* shares that Adv received are same *)
             repss_private E.advid{1} shares1.[id] shares2.[id])
        /\ (forall id, 0 <= id < N => id <> E.advid{1} => repss_integr shares1.[id])  (* valid SS *)
        /\ (forall id, 0 <= id < N => id <> E.advid{1} => repss_integr shares2.[id])
        /\ 0 <= E.advid{1} < N
        /\ E.pshares{1} = distribute_shares shares1
        /\ E.pshares{2} = distribute_shares shares2
     ==>
        ={glob A, E.advid, res} 
(* Not a relational property:     /\ reqs_integr Environment.advid{2} res{1} *)].
proof.
exists* E.advid{1}; elim*=> advid.
pose p1 := distribute_shares shares1.
pose p2 := distribute_shares shares2.
pose I  := fun x1 x2 =>
  x1 = p1 /\ x2 = p2 /\
  shares1.[advid] = shares2.[advid]  /\
  (forall id, 0 <= id < N =>  
             repss_private advid shares1.[id] shares2.[id]) /\
  (forall id, 0 <= id < N => id <> advid => repss_integr shares1.[id]) /\  
  (forall id, 0 <= id < N => id <> advid => repss_integr shares2.[id]).
proc. sp. 
sp; conseq (_ :
     ={glob A, E.advid, i, rx}
  /\ (E.advid, i, rx){1} = (advid, 0, nseq N witness)
  /\ I E.pshares{1} E.pshares{2} /\  0 <= E.advid{1} < N ==> _) => //.
while (={glob A, E.advid, i, rx}
  /\ E.advid{1} = advid
  /\ 0 <= i{1} <= N
  /\ size rx{1} = N
  /\ I E.pshares{1} E.pshares{2} /\  0 <= E.advid{1} < N);
last by skip=> &1 &2 |>; smt(size_nseq gt1_N). 
wp=> /=.
inline Protocol(Environment(A).QP).verify.
sp; wp.
while (={glob A, E.advid, id, rx, rx0, i, j}
  /\ i{1} = id{1}
  /\ E.advid{1} = advid
  /\ 0 <= i{1} < N
  /\ 0 <= j{1} <= N
  /\ size rx{1} = N
  /\ I E.pshares{1} E.pshares{2} /\  0 <= E.advid{1} < N);
last by skip=> &1 &2 |>; smt(size_nseq size_rcons size_set).
sp; wp.
while (={glob A, E.advid, id, rx, rx0, i, j, k}
  /\ i{1} = id{1}
  /\ E.advid{1} = advid
  /\ 0 <= i{1} < N
  /\ 0 <= j{1} < N
  /\ 0 <= k{1} <= N
  /\ size rx{1} = N
  /\ I E.pshares{1} E.pshares{2});
last by skip=> &1 &2 |>; smt(size_nseq size_rcons size_set).
sp; wp.
while (={glob A, E.advid, id, rx, rx0, i, j, k, l}
  /\ i{1} = id{1}
  /\ E.advid{1} = advid
  /\ 0 <= i{1} < N
  /\ 0 <= j{1} < N
  /\ 0 <= k{1} < N
  /\ 0 <= l{1} <= N
  /\ size rx{1} = N
  /\ I E.pshares{1} E.pshares{2});
last by skip=> &1 &2 |>; smt(size_nseq size_rcons size_set).
wp.
if; 1:smt(); last by skip=> &1 &2 |> /#.
seq 1 1 : (={glob A, E.advid, id, rx, rx0, i, j, k, l, b}
  /\ i{1} = id{1}
  /\ E.advid{1} = advid
  /\ 0 <= i{1} < N
  /\ 0 <= j{1} < N
  /\ 0 <= k{1} < N
  /\ 0 <= l{1} < N
  /\ size rx{1} = N
  /\ I E.pshares{1} E.pshares{2});
last by if; auto=> /#.
inline Environment(A).QP.complains.
sp; wp.
if=> //=.
if=> //=; last by auto=> &1 &2 |>; smt(nth_mkseq).
exists* id0{1}. elim* => id11. exists* id0{2}. elim* => id12. 
exists* j{1}. elim* => j11. exists* j{2}. elim* => j12. sp.
exists* pa{1}. elim* => pa01. exists* pa{2}. elim* => pa02.
call(Acomplains2 id11 id12 j11 j12 pa01 pa02).
skip=> &1 &2 |>. 
qed.

(* -------------------------------------------------------------------- *)
(* --- Predicates for broadcast --- *)

pred reqs_bcast_compat (advid : int) (rx : reqs list) (bx : bcast list) (pshares : zmod matrix list) =
  forall i j v, 0 <= i < N => 0 <= j < N =>
    (bx.[i].[j] = None <=> !rx.[i].[j]) /\
    (i <> advid =>
      (rx.[i].[j] => bx.[i].[j] = Some pshares.[fresh j j].[i].[j]) /\
      (bx.[i].[j] = Some v => rx.[i].[j] /\ v = pshares.[i].[i].[j])).

(* Used only in broadcast_shares_integr *)
pred reqs_bcast_compat_aux ib (advid : int) (rx : reqs list) (bx : bcast list) (pshares : zmod matrix3) =
  forall i j v, 0 <= i < ib => 0 <= j < N =>
    (bx.[i].[j] = None <=> ! rx.[i].[j]) /\
     (i <> advid =>
      (rx.[i].[j] => bx.[i].[j] = Some pshares.[fresh j j].[i].[j]) /\
      (bx.[i].[j] = Some v => rx.[i].[j] /\ v = pshares.[i].[i].[j])).

lemma cube_fix (advid : int) (pshares : zmod matrix3) (bx : bcast list) : 
   cube N (fix advid pshares bx) by smt(nth_mkseq size_mkseq gt0_N).

lemma fix_integr (advid : int) (pshares : zmod matrix3) (bx : bcast list) (rx:reqs list): 
   0<= advid < N => cube N pshares => (reqs_bcast_compat advid rx bx pshares) => (reqs_pshares_compat rx pshares) => 
   forall i, 0<=i< N => (repss_integr (col N i (fix advid pshares bx))).
   (* all (repss_integr (transpose (fix advid pshares bx))). *)
move => abd cub rqs pc i ibd.
split. split; smt(nth_mkseq size_mkseq). split; first smt(nth_mkseq size_mkseq).
move =>  rec1 rec1bd rec2 rec2bd c cond.
rewrite !col3 //=. 
rewrite /fix. do 3!rewrite !nth_mkseq //=. smt(). smt(). 
have -> :! rec1 = c by smt(). have -> :! rec2 = c by smt().
simplify.
rewrite /reqs_bcast_compat in rqs.
rewrite /reqs_pshares_compat in pc.
smt().
qed.

(* -------------------------------------------------------------------- *)

(* --- Lemmas for broadcast --- *)
local lemma broadcast_shares_integr reqs :
  hoare [ E.broadcast_shares :
    rx = reqs /\ square N rx /\ 0 <= E.advid < N ==>
    square N res /\
    reqs_bcast_compat E.advid reqs res E.pshares ].
proof.
exists* E.advid; elim*=> advid.
proc.
sp.
conseq (_ :
  (E.advid, i, rx, bx) = (advid, 0, reqs, nseq N (nseq N witness)) /\
  0 <= E.advid < N /\ square N rx ==>  
  0 <= i  <= N /\
  square N bx /\ reqs_bcast_compat_aux N E.advid reqs bx E.pshares);1,2:smt().
while (
     E.advid = advid
  /\ 0 <= i <= N
  /\ rx = reqs
  /\ 0 <= E.advid < N
  /\ square N rx
  /\ square N bx
  /\ reqs_bcast_compat_aux i E.advid rx bx E.pshares); last by skip=> &1 &2 |>; smt(size_nseq nth_nseq).
seq 1 :
(    E.advid = advid
  /\ 0 <= i <= N
  /\ rx = reqs
  /\ 0 <= E.advid < N
  /\ square N rx
  /\ square N bx
  /\ reqs_bcast_compat_aux i E.advid rx bx E.pshares). 
if. 
  + by call (Abroadcast reqs.[advid]); auto; smt().
    by auto=> &1 |>; smt(size_rcons nth_rcons size_mkseq nth_mkseq gt1_N).
wp; sp.
while (
     E.advid = advid
  /\ 0 <= i <= N
  /\ rx = reqs
  /\ 0 <= E.advid < N
  /\ square N rx
  /\ square N bx
  /\ reqs_bcast_compat_aux i E.advid rx bx E.pshares); last by skip=> &1 &2 |>; smt(size_nseq nth_nseq).
if; [ by call abort_false_1 | by auto ].
qed.

pred broadcast_private (advid dlr:int) (bx11 bx12: bcast) =
     (advid=dlr => bx11=bx12)/\(advid<>dlr => forall j, (0<=j<N/\ j<>advid) => bx11.[j]=bx12.[j]).
pred reqs_bcast_private (advid i j :int) (rx1 rx2: reqs list) (bx11 bx12: bcast) =
     if i=advid then (rx1.[i].[j] && bx11.[j] = None) = (rx2.[i].[j] && bx12.[j] = None)
                else ((rx1.[i].[j] => bx11.[j] <> None) /\ (rx2.[i].[j] => bx12.[j] <> None)).

local lemma broadcast_shares_private (shares1 shares2 : zmod matrix3) :
  equiv [ E.broadcast_shares ~ E.broadcast_shares :
      ={glob A, E.advid, rx}
   /\ 0 <= E.advid{1} < N
   /\ (forall id, 0 <= id < N => id <> E.advid{1} => repss_integr shares1.[id])  (* valid SS *)
   /\ (forall id, 0 <= id < N => id <> E.advid{1} => repss_integr shares2.[id])
   /\ reqs_integr E.advid{1} rx{1}
   /\ shares1.[E.advid{1}] = shares2.[E.advid{2}] (* shares that Adv sent are same *)
   /\ (forall id, 0 <= id < N =>  (* shares that Adv received are same *)
        repss_private E.advid{1} shares1.[id] shares2.[id])
   /\ E.pshares{1} = distribute_shares shares1
   /\ E.pshares{2} = distribute_shares shares2
      ==>
      ={glob A, res} /\ square N res{1}
  /\ reqs_bcast_compat E.advid{1} E.rx{1} res{1} E.pshares{1}
  /\ reqs_bcast_compat E.advid{1} E.rx{2} res{2} E.pshares{2}
].
proof.
proc.
exists* E.advid{1}; elim*=> advid. 
sp.
conseq (_ :
     ={glob A, E.advid, i, rx, bx}
  /\ (E.advid, i, bx){1} = (advid, 0, nseq N (nseq N witness))
  /\ 0 <= E.advid{1} < N
  /\ (forall id, 0 <= id < N => id <> E.advid{1} => repss_integr shares1.[id])
  /\ (forall id, 0 <= id < N => id <> E.advid{1} => repss_integr shares2.[id])
  /\ reqs_integr E.advid{1} rx{1}
  /\ repss_list_private E.advid{1} shares1 shares2
  /\ E.pshares{1} = distribute_shares shares1
  /\ E.pshares{2} = distribute_shares shares2
  /\ broadcast_private advid i{1} bx1{1} bx1{2} ==> _); first by smt().
while (={glob A, E.advid, i, rx, bx}
  /\ E.advid{1} = advid
  /\ 0 <= E.advid{1} < N
  /\ 0 <= i{1} <= N
  /\ (forall id, 0 <= id < N => id <> E.advid{1} => repss_integr shares1.[id])
  /\ (forall id, 0 <= id < N => id <> E.advid{1} => repss_integr shares2.[id])
  /\ reqs_integr E.advid{1} rx{1}
  /\ repss_list_private E.advid{1} shares1 shares2
  /\ E.pshares{1} = distribute_shares shares1
  /\ E.pshares{2} = distribute_shares shares2
  /\ square N bx{1}
  /\ reqs_bcast_compat_aux i{1} E.advid{2} E.rx{1} bx{1} E.pshares{1}
  /\ reqs_bcast_compat_aux i{2} E.advid{2} E.rx{2} bx{2} E.pshares{2}
  /\ broadcast_private advid i{1} bx1{1} bx1{2}
  /\ (0<i{1} => forall j, 0<=j<N => reqs_bcast_private advid i{1} j rx{1} rx{2} bx1{1} bx1{2}));
last by skip=> &1 &2 |> ; smt(size_nseq nth_nseq).
seq 1 1 :
(={glob A, E.advid, i, rx, bx, bx1}
  /\ E.advid{1} = advid
  /\ 0 <= i{1} < N
  /\ (forall id, 0 <= id < N => id <> E.advid{1} => repss_integr shares1.[id])
  /\ (forall id, 0 <= id < N => id <> E.advid{1} => repss_integr shares2.[id])
  /\ reqs_integr E.advid{1} rx{1}
  /\ repss_list_private E.advid{1} shares1 shares2
  /\ E.pshares{1} = distribute_shares shares1
  /\ E.pshares{2} = distribute_shares shares2
  /\ square N bx{1}
  /\ forall j, 0<=j<N => reqs_bcast_private advid i{1} j rx{1} rx{2} bx1{1} bx1{2}
). exists* rx{1}.[i{1}]; elim*=> rxi1. exists* rx{2}.[i{2}]; elim*=> rxi2.
if=> //; first by call (Abroadcast2 rxi1 rxi2); auto => |> /#.
  auto => |>. progress [-delta]. 
  apply eq_in_mkseq => j hj /=; do 4!(rewrite nth_mkseq /= 1:/#); case (rx{2}.[i{2}].[j])=> //= /#. 
rewrite /reqs_bcast_private H13 /=.
rewrite !nth_mkseq //=.
split; move => -> //=. 
wp; sp;
while
(={glob A, E.advid, i, j, rx, bx, bx1}
  /\ E.advid{1} = advid
  /\ 0 <= i{1} < N
  /\ 0 <= j{1} <= N
  /\ (forall id, 0 <= id < N => id <> E.advid{1} => repss_integr shares1.[id])
  /\ (forall id, 0 <= id < N => id <> E.advid{1} => repss_integr shares2.[id])
  /\ repss_list_private E.advid{1} shares1 shares2
  /\ E.pshares{1} = distribute_shares shares1
  /\ E.pshares{2} = distribute_shares shares2
); last by skip=> &1 &2 |>;smt(gt1_N).
(* in the loop *)
if => //; last by call abort_false_2.
qed.

(* -------------------------------------------------------------------- *)
local lemma extract_advinpsx_spec advid pshares :
  0 <= advid < N => 
  (forall i, 0<=i<N => repss_integr (col N i pshares)) =>
  forall id j,
    0 <= id < N => 0 <= j < N => id <> advid => id <> j =>
    (mkaddshares (extract advid pshares)).[j] = pshares.[id].[advid].[j].
proof.
move =>  N4 abd.
progress [-delta].
rewrite nth_mkseq //=. 
rewrite /extract.
rewrite -col3. smt(gt1_N fresh_is_fresh). 
have tmp:=(abd advid N4). smt(fresh_is_fresh).
qed.

(* ------------------------ *)
(* Invariants for pi1_spec *)

abbrev idealfct_of_inp (inp : zmod matrix3) = 
   idealfct (map reconstruct_vss_one (transpose inp)). 
    (* was: vec N (fun id => col N id inp))). *)

(* Invariant for the input phase *)
pred inp_invariant (advid : int) (inp: zmod matrix3) (rx:reqs list) (bx:bcast list) 
       (initadvshares:zmod matrix) (psharesbeforefix: zmod matrix3)
       (advinpsx:zmod list) (secrets:zmod list)=
      cube N psharesbeforefix     
   /\ (forall r c,
        0 <= r < N =>
        0 <= c < N =>
        r <> advid =>
        r <> c =>
        initadvshares.[r].[c] = psharesbeforefix.[r].[advid].[c])
   /\ reqs_integr advid rx
   /\ reqs_pshares_compat rx psharesbeforefix
   /\ square N bx
   /\ reqs_bcast_compat advid rx bx psharesbeforefix
   /\ inp = fix advid psharesbeforefix bx
   /\ (forall i, 0<=i<N => repss_integr (col N i inp))
   /\ repss_correct advid secrets (transpose inp)
(* We could move this assignment into the input phase in the protocol.*)
   /\ advinpsx = mkaddshares (extract advid inp)
   /\ secrets.[advid]=sum (mkaddshares (extract advid inp)).

(* Invariant in the computation phase *)
pred comp_invariant (comp : zmod matrix) (inp : zmod matrix3) =
     (forall id, 0<=id<N => repss_integr (col N id inp)) 
  /\ (repss_integr comp)
  /\ (reconstruct_vss_one comp = idealfct_of_inp inp).

local lemma fix_honest advid shares rx bx:
  let pshares = distribute_shares shares in
    cube N shares =>  
    reqs_integr advid rx =>
    reqs_pshares_compat rx pshares =>
    reqs_bcast_compat advid rx bx pshares =>
    (forall i, 0<=i<N => i<>advid => repss_integr shares.[i]) =>
    (forall i, 0<=i<N => i<>advid => 
      (col N i (fix advid pshares bx)) = shares.[i]).
proof.
move => pshares size H H0 H1 H2 i ibd neq.
have [sq rest]:=(H2 i ibd neq). clear H2.
elim H0=> sq1 comp.
rewrite /fix //=.
apply meq_eq.
split; smt(size_mkseq nth_mkseq).
smt(size_mkseq nth_mkseq).
rewrite /(\eqm).
split; first by split; smt(size_mkseq nth_mkseq).
split; first smt(size_mkseq nth_mkseq).
move => id j idbd jbd. rewrite /reqs_bcast_compat in H1.
do 4!rewrite nth_mkseq //=. 
case (id=j); first smt(). move => neqidj.
case (rx.[i].[j]); last smt(transpose_unfold).
move => yes.
have ->:(bx.[i].[j] = Some pshares.[id].[i].[j]) by smt(nth_mkseq).
smt(transpose_unfold).
qed.
    
pred shared_terms_rep_integr (shared_terms_rep:zmod matrix5) =
  cube5 N shared_terms_rep /\
  (forall i j sen, 0 <= i < N => 0 <= j < N => 0 <= sen < N =>
    i <> sen => j <> sen => (* parties i and j don't share term a_i*b_j *)
    repss_integr shared_terms_rep.[i].[j].[sen] (* all parties output valid sharings *)
 ).

pred sharedterms_rep_distr_integr (sharedterms_rep_distr:zmod matrix5) = 
  cube5 N sharedterms_rep_distr /\  
  (forall i j sen, 0 <= i < N => 0 <= j < N => 0 <= sen < N =>
    i <> sen => j <> sen => (* parties i and j don't share term a_i*b_j *)
    repss_integr (col N sen sharedterms_rep_distr.[i].[j]) (* all parties output valid sharings *)).  

lemma distribute_shared_terms_invol: forall M, cube4 N M => distribute_shared_terms (distribute_shared_terms M)= M.
rewrite /distribute_shared_terms. 
move => M cub. 
rewrite (matrix_unfold M). smt(). rewrite !map_mkseq /(\o) =>//=. 
apply eq_in_mkseq => //= i ibd. rewrite !map_mkseq /(\o) =>//=. 
smt(eq_in_mkseq transpose_invol).
qed.

lemma distribute_sharedterms_integr (shared_terms_rep:zmod matrix5) : 
  shared_terms_rep_integr shared_terms_rep => sharedterms_rep_distr_integr (distribute_shared_terms shared_terms_rep).
move => [cub hyp]. 
split.
 split; first smt(size_map nth_mkseq size_mkseq gt1_N).
 move => i ibd. rewrite (nth_map witness); first smt(nth_mkseq size_mkseq gt1_N).
 split; first  smt(nth_map size_map nth_mkseq size_mkseq gt1_N).
 move => j jbd. rewrite (nth_map witness); smt(nth_mkseq size_mkseq gt1_N).
move => i j sen ibd jbd senbd isen jsen. split. 
 split; first smt(nth_mkseq size_mkseq gt1_N). 
 move => k kbd. rewrite nth_mkseq //=. do 2!rewrite (nth_map witness) 1:/#. smt(nth_mkseq size_mkseq gt1_N).
split. 
 move => id idbd. rewrite nth_mkseq //=. do 2!rewrite (nth_map witness) 1:/#. do 2!rewrite nth_mkseq //=. smt(). 
move => rec1 rec1bd rec2 rec2bd c cond. rewrite !nth_mkseq //=. do 2!rewrite (nth_map witness) 1:/#. smt(nth_mkseq). 
qed.

(* -------------------------------------------------------------------- *)
(* We will now start proving correctness                                *)

(* Final messages the honest parties send in the output phase *)
op finalmsg (advid : int) (y : zmod) (pviewadv : zmod list) : zmod matrix =
  mkseq (fun id =>
    mkseq (fun c =>
      if id = c then witness
      else if c = advid /\ (id<>advid) then y - sum (drop_elem advid pviewadv)
      else pviewadv.[c]) N) N.

lemma comp_eq_finalmsg (advid : int) (inp: zmod matrix3) (comp: zmod matrix): 
  0<=advid<N =>
  comp_invariant comp inp =>
    (finalmsg advid (idealfct_of_inp inp) comp.[advid]) = comp.
proof.
move => advbd [inpvalid [compvalid correct]].
rewrite -eqmeq.
(split; first smt(size_mkseq nth_mkseq)). smt(size_mkseq nth_mkseq).
(split; first smt(size_mkseq nth_mkseq)). smt(size_mkseq nth_mkseq).
(split; first smt(size_mkseq nth_mkseq)). (split; first smt(size_mkseq nth_mkseq)). 
move => id c idbd cbd /=.
rewrite /finalmsg -{3}(mkseq_nth witness comp). have ->:(size comp=N) by smt().
do 2!rewrite !nth_mkseq //=.
case (c = advid/\id<>advid); last smt(nth_mkseq).
move => [-> neqida] //=.
rewrite -correct 1:///reconstruct_vss_one neqida/=.
rewrite subr_eq addrC sum_drop_elem_plus 1:/#.
congr.
have ->:(size comp.[advid])=N by smt().
apply eq_in_mkseq => i ibd /=. 
have HH:(majority (drop_elem i (col N i comp)) = Some (if i <> advid then comp.[advid].[i] else comp.[id].[advid])); last by smt().
apply majority_all'; first by smt(size_drop_elem size_mkseq gt3_N).
move => j jbd. rewrite nth_drop_elem 1:/#.
smt(nth_mkseq size_drop_elem size_mkseq gt3_N). 
qed.

local lemma distribute_resshares_majority advid advc comp :
  0 <= advid < N =>
  repss_integr comp =>
  let presshares = distribute_resshares advid advc comp in
  forall id i j,
    0 <= id < N => 0 <= i < N => 0 <= j < N =>
    i <> j =>
    majority (drop_elem j (col N j presshares.[id])) = Some comp.[i].[j].
proof.
move=> Hadvid Hpcomp presshares id i j hid hi hj inj.
case (j = advid)=> [->> | jnadvid].
- apply (majority_all');
  smt(size_mkseq nth_mkseq size_drop_elem nth_drop_elem gt3_N).
- apply (majority_all_except_one' _ _ (if advid < j then advid else advid-1));
  smt(size_mkseq nth_mkseq size_drop_elem nth_drop_elem gt3_N).
qed.

local lemma distribute_reconstruct_vss (advid :int) (comp : zmod matrix) 
                                       (advres : zmod) (advc : zmod matrix) :
  0 <= advid < N =>
    repss_integr comp =>
    (let resshares = distribute_resshares advid advc comp in
    (forall id, 0<= id < N /\ id<>advid =>
       (reconstruct_vss advid advres resshares).[id] = reconstruct_vss_one comp)).
proof.
move => advidbd Hcompvalid resshares id [idbd idneqadvid].
rewrite /reconstruct_vss /reconstruct_vss_one => //=.
rewrite nth_mkseq => //=.
rewrite idneqadvid => //=.
congr.
apply eq_in_mkseq => x xbd //=.
congr.
rewrite (distribute_resshares_majority advid advc comp _ _  id (fresh x advid) x) => //=; 1,2:smt(fresh_is_fresh gt3_N).
rewrite (majority_all_except_one' _  comp.[fresh x advid].[x] (if x = advid then 0 else if x < advid then advid-1 else advid)) => //=; smt(size_drop_elem size_mkseq gt3_N nth_drop_elem nth_mkseq).
qed.

(* -------------------------------------------------------------------- *)


local lemma inp_spec sx:
   hoare [ E.input :
      sx = s /\ 0 <= E.advid < N
      ==>
      cube N res
   /\ (forall i, 0 <= i < N => repss_integr (col N i res))
   /\ (forall i, 0 <= i < N => repss_correct1 E.secrets.[i] (col N i res)
   /\ E.secrets.[E.advid]=sum (mkaddshares (extract E.advid res))
      ) ].
proof.
conseq (_: _ ==> inp_invariant E.advid res E.rx E.bx E.initadvshares E.psharesbeforefix E.advinpsx E.secrets).
progress [-delta]. have ->:  result = fix Environment.advid{hr} psharesbeforefix bx; smt(cube_fix). 
have ->:  result = fix Environment.advid{hr} psharesbeforefix bx by smt(). 
apply (fix_integr _ _ _ rx) => //=; smt(). 
move => repi. rewrite /inp_invariant in H1. rewrite /extract in H1.
case ( i = Environment.advid{hr}). move => -> //=. smt().
move => hyp //=. rewrite /repss_correct in H1. 
have <-:=(transpose_invol result). smt(nth_mkseq size_mkseq).
rewrite col_transpose //=; smt(nth_mkseq size_mkseq). 
smt().
admitted. (* As in pi1_spec for addition *)

local lemma mult_term_sharing_spec ax bx:
  hoare [ E.mult_term_sharing :
       0 <= E.advid < N
    /\ ax = a /\ bx = b
    /\ repss_integr a
    /\ repss_integr b
   ==>      
       cube5 N res /\
       (forall i j sen, 0 <= i < N => 0 <= j < N => 0 <= sen < N =>
       let ai = mkaddshares ax in
       let bj = mkaddshares bx in
       (sen <> i /\ sen <> j => repss_integr res.[i].[j].[sen]) /\
       (sen <> i /\ sen <> j /\ sen <> E.advid =>
          repss_correct1 (ai.[i] * bj.[j]) res.[i].[j].[sen] ) ) ].
admitted. (* standard reasoning about while loops *)
(* in each iteration: if sen <> i,j, advid, then valshare has integrity and correct1 ai*bj *)

local lemma mult_check_term_sharing_spec shares ax bx:
  hoare [ E.mult_check_term_sharing :
      shares = sharedterms_rep_distr
   /\ 0 <= E.advid < N
   /\ repss_integr ax
   /\ repss_integr bx 
   /\ (forall i j sen, 0 <= i < N => 0 <= j < N => 0 <= sen < N =>
       let ai = mkaddshares ax in
       let bj = mkaddshares bx in
       (sen <> i /\ sen <> j => repss_integr (col N sen sharedterms_rep_distr.[i].[j])) /\
       (sen <> i /\ sen <> j /\ sen <> E.advid =>
         repss_correct1 (ai.[i] * bj.[j]) (col N sen sharedterms_rep_distr.[i].[j]) ) )
     ==>
      let ai = mkaddshares ax in
      let bj = mkaddshares bx in
      (forall i j , 0 <= i < N => 0 <= j < N => 
        (forall rec k, 0 <= rec < N => 0 <= k < N =>
         res.[rec].[i].[j].[k] = Some Zp.zero) =>
         repss_integr (col N (fresh i j) shares.[i].[j]) /\
         repss_correct1 (ai.[i] * bj.[j]) (col N (fresh i j) shares.[i].[j]))
     ].
proof.
proc.
seq 3: (
      shares = sharedterms_rep_distr
  /\ 0 <= E.advid < N
  /\ repss_integr ax
  /\ repss_integr bx
  /\ let ai = mkaddshares ax in
     let bj = mkaddshares bx in
       (forall i j sen, 0 <= i < N => 0 <= j < N => 0 <= sen < N =>
       (sen <> i /\ sen <> j => repss_integr (col N sen sharedterms_rep_distr.[i].[j])) /\
       (sen <> i /\ sen <> j /\ sen <> E.advid =>
         repss_correct1 (ai.[i] * bj.[j]) (col N sen sharedterms_rep_distr.[i].[j]) ) )
    /\ (forall i j sen, 0 <= i < N => 0 <= j < N => 0 <= sen < N =>
       sen <> i => sen <> j =>
       repss_integr (col N sen shares.[i].[j]) /\
       (repss_correct1 (ai.[i] * bj.[j]) (col N sen sharedterms_rep_distr.[i].[j]) =>
       repss_correct1 (ai.[i] * bj.[j]) (col N (fresh i j) sharedterms_rep_distr.[i].[j]) =>
       repss_correct1 Zp.zero (col N sen shared_diff.[i].[j]))
       )).
  call(_: true); auto. progress[-delta]. have tmp:=(H3 i j sen); smt().
do 2! rewrite !nth_mkseq //=. have senbd :(0<=sen <N) by smt().
have repi: repss_integr (col N sen sharedterms_rep_distr{hr}.[i].[j]) by have :=(H3 i j sen);smt().
have repi2: repss_integr (col N (fresh i j) sharedterms_rep_distr{hr}.[i].[j]) by have :=(H3 i j (fresh i j));smt(fresh_is_fresh).
have := (localdiff_correct_zero i j (sharedterms_rep_distr{hr}.[i].[j]) sen senbd H10 H11 repi repi2). 
have ->: (sum (mkaddshares (col N sen sharedterms_rep_distr{hr}.[i].[j])) = (mkaddshares ax).[i] * (mkaddshares bx).[j]).
apply H12. have :=(H3 i j sen); smt().
have ->: (sum (mkaddshares (col N (fresh i j) sharedterms_rep_distr{hr}.[i].[j])) = (mkaddshares ax).[i] * (mkaddshares bx).[j]).
apply H13. have :=(H3 i j (fresh i j)); smt(fresh_is_fresh).
smt(fresh_is_fresh).
admitted. (* standard reasoning with seqs. proofs as the one above. *)

local lemma mult_determine_term_sharing_spec ax bx shares odiff:
   hoare [ E.mult_determine_term_sharing :
      ax = a
   /\ bx = b
   /\ shares = sharedterms_rep_distr
   /\ odiff = opened_diff 
   /\ 0 <= E.advid < N 
   /\ repss_integr a
   /\ repss_integr b 
   /\ let ai = mkaddshares ax in
      let bj = mkaddshares bx in
      (forall i j , 0 <= i < N => 0 <= j < N => 
       (forall rec k, 0 <= rec < N => 0 <= k < N =>
         opened_diff.[rec].[i].[j].[k] = Some Zp.zero) =>
         repss_integr (col N (fresh i j) sharedterms_rep_distr.[i].[j]) /\
         repss_correct1 (ai.[i] * bj.[j]) (col N (fresh i j) sharedterms_rep_distr.[i].[j]))
     ==> 
      let ai = mkaddshares ax in
      let bj = mkaddshares bx in
      (forall i j, 0 <= i < N => 0 <= j < N =>
         repss_integr res.[i].[j] /\
         repss_correct1 (ai.[i] * bj.[j]) res.[i].[j])
   ].
proof.
proc.
admitted. (* standard reasoning with seqs. proofs as the one above. *)

local lemma mklocalsums_M_integr M shares :
  N<=M => 
  size shares = N =>
  (forall id, 0 <= id < N => size shares.[id] = M) =>
  (forall id i, 0 <= id < N => 0 <= i < M => size shares.[id].[i] = N) =>
  (forall c, 0 <= c < M => repss_integr (col N c shares)) =>
  repss_integr (mklocalsums_M M shares).
proof.
move=> leNM sz1 sz2 sz3 integr.
split; first by smt(size_mkseq gt1_N nth_mkseq).
split; first by smt(nth_mkseq).
move => rec1 rec1bd rec2 rec2bd c cond.
rewrite /mklocalsums_M.
do !rewrite nth_mkseq //=. by elim cond. by elim cond. (* smt() does not work here ?? *)
have tmp: (sum (col M c shares.[rec1]) = sum (col M c shares.[rec2])); last smt().
rewrite /repss_integr in integr.
congr. apply eq_in_mkseq => j jbd /=.
have [sq [_ H0]]:= (integr j jbd).
have H1:=(H0 rec1 rec1bd rec2 rec2bd c cond).
smt(nth_mkseq).
qed.

local lemma mult_spec ax bx:
   hoare [ E.multiplication :
      ax = a
   /\ bx = b
   /\ 0 <= E.advid < N
   /\ repss_integr a
   /\ repss_integr b
      ==>
      let aval = reconstruct_vss_one ax in
      let bval = reconstruct_vss_one bx in
      repss_integr res
   /\ repss_correct1 (aval * bval) res ].
proof.
proc.
seq 2: (
     ax = a
  /\ bx = b
  /\ 0 <= E.advid < N 
  /\ repss_integr ax
  /\ repss_integr bx
  /\ (forall i j sen, 0 <= i < N => 0 <= j < N => 0 <= sen < N =>
      let ai = mkaddshares ax in
      let bj = mkaddshares bx in
       (sen <> i /\ sen <> j => repss_integr (col N sen sharedterms_rep_distr.[i].[j])) /\
       (sen <> i /\ sen <> j /\ sen <> E.advid =>
          repss_correct1 (ai.[i] * bj.[j]) (col N sen sharedterms_rep_distr.[i].[j]) ) )
).
wp; call(mult_term_sharing_spec ax bx).
skip; progress[-delta].
rewrite /distribute_shared_terms. rewrite (nth_map witness) //=. smt(). rewrite (nth_map witness) //=. smt().
have <-:=(transpose_invol result). smt(). rewrite col_transpose //=; smt(nth_mkseq size_mkseq). 
rewrite /distribute_shared_terms. rewrite (nth_map witness witness) //=. smt(size_iota). rewrite (nth_map witness) //=. smt(size_iota). rewrite !nth_iota //=. rewrite (nth_map witness witness) //=. smt(size_iota). rewrite (nth_map witness) //=. smt(size_iota). 
have <-:=(transpose_invol result). smt(). rewrite col_transpose //=; smt(nth_mkseq size_mkseq). 
exists* sharedterms_rep_distr; elim* => sharedterms_rep_distr0.   
seq 1: (
     ax = a
  /\ bx = b
  /\ sharedterms_rep_distr0 = sharedterms_rep_distr
  /\ 0 <= E.advid < N 
  /\ repss_integr ax
  /\ repss_integr bx
  /\ let ai = mkaddshares ax in
     let bj = mkaddshares bx in
     (forall i j , 0 <= i < N => 0 <= j < N => 
       (forall rec k, 0 <= rec < N => 0 <= k < N =>
         opened_diff.[rec].[i].[j].[k] = Some Zp.zero) =>
         repss_integr (col N (fresh i j) sharedterms_rep_distr.[i].[j]) /\
         repss_correct1 (ai.[i] * bj.[j]) (col N (fresh i j) sharedterms_rep_distr.[i].[j]))
); first by call(mult_check_term_sharing_spec sharedterms_rep_distr0 ax bx); skip; progress[-delta].
exists* opened_diff; elim* => opened_diff0.
seq 1: (
     ax = a
  /\ bx = b
  /\ sharedterms_rep_distr0 = sharedterms_rep_distr
  /\ 0 <= E.advid < N 
  /\ repss_integr ax
  /\ repss_integr bx /\
     let ai = mkaddshares ax in
     let bj = mkaddshares bx in
       (forall i j, 0 <= i < N => 0 <= j < N =>
         repss_integr sharedterms.[i].[j] /\
         repss_correct1 (ai.[i] * bj.[j]) sharedterms.[i].[j])
); first by call(mult_determine_term_sharing_spec ax bx sharedterms_rep_distr0 opened_diff0);
skip; progress[-delta].
call(_: true); auto.
have termbd1: (forall term, 0 <= term < ((N-1)*N) => 0 <= (term %/ N) < N). move => tm hyp. rewrite ltz_divLR; smt(ltz_divLR gt1_N divz_ge0 gt1_N). 
have termbd2: (forall term, 0 <= term < ((N-1)*N) => 0 <= (term %% N) < N) by smt(ltz_pmod gt1_N modn_ge0).
progress[-delta] => //. apply mklocalsums_M_integr=> //. smt(gt3_N). rewrite /rearrange_sharedterms. smt(size_mkseq nth_mkseq).
rewrite /rearrange_sharedterms. smt(size_mkseq nth_mkseq). rewrite /rearrange_sharedterms.
move => id i idbd ibd. rewrite nth_mkseq //=. rewrite nth_mkseq //=. smt().
rewrite /rearrange_sharedterms. 
move => c cbd. 
have ->:  (col N c (vec N
        (fun (id : int) =>
           vec ((N - 1) * N)
             (fun (term : int) =>
                sharedterms{hr}.[term %/ N].[term %% N].[id])))= 
          (vec N (fun (id : int) => sharedterms{hr}.[c %/ N].[c %% N].[id]))); first smt(eq_in_mkseq nth_mkseq size_mkseq).
have [int _]:=(H3 (c %/ N) (c %% N) (termbd1 c cbd) (termbd2 c cbd)). 
have <-:( sharedterms{hr}.[c %/ N].[c %% N] =  (vec N (fun (id : int) => sharedterms{hr}.[c %/ N].[c %% N].[id]))); last smt().
print mkseq_nth.
pose l:=(sharedterms{hr}.[c %/ N].[c %% N]).
apply eq_sym. have <-: (size l=N); first smt().
apply (mkseq_nth witness l). 
do 2!rewrite -mkadd_recon //=. 
move => rep.
admit (* basic algebra: sum (ai*bj) = sum ai* sum bj for secret sharings *).
qed.
    
local lemma pi1_spec sx:
    hoare [E.pi1 :
      sx = s /\ 0 <= E.advid < N
      ==>
      let inp = snd res in
      let comp = fst res in
      (forall (id : int), 0 <= id < N => repss_integr (col N id inp))
   /\ repss_integr comp 
   /\ (forall i, 0 <= i < N => repss_correct1 E.secrets.[i] (col N i inp))
   /\ reconstruct_vss_one comp = idealfct_of_inp inp 
   /\ E.secrets.[E.advid]=sum (mkaddshares (extract E.advid inp)) ].
proof.
proc.
seq 1: ( 0 <= E.advid < N
      /\ cube N rinp
      /\ (forall i, 0 <= i < N => repss_integr (col N i rinp))
      /\ (forall i, 0 <= i < N => repss_correct1 E.secrets.[i] (col N i rinp))
      /\ E.secrets.[E.advid]=sum (mkaddshares (extract E.advid rinp)) ).
   call(inp_spec sx); auto => |>; progress [-delta].       have :=(H3 i); smt(). smt().
inline E.computation_mult.
sp; wp.
exists* rinp; elim* => inp.       
pose ax := col N 0 inp.
pose bx := col N 1 inp.       
call(mult_spec ax bx).
skip; progress[-delta]. have H20 := (H2 0); smt(). have H21 := (H2 1 gt1_N); smt().
rewrite /idealfct.
have <-: (reconstruct_vss_one (col N 0 rinp{hr}) *
       reconstruct_vss_one (col N 1 rinp{hr}) = reconstruct_vss_one result); first smt(mkadd_recon).
rewrite (nth_map witness). smt(size_mkseq). rewrite (nth_map witness _ _ 1). smt(size_mkseq gt1_N).
congr. congr. rewrite nth_mkseq //=. rewrite nth_mkseq //=.
qed.

(* -------------------------------------------------------------------- *)
(* Correctness of the protocol with respect to the input
   that the adversary is commited to. *)
local lemma correctness sx :
  hoare [ E.protocol :
    sx = s /\ size s = N /\
    0 <= E.advid < N ==>
    forall id,
      0 <= id < N /\ id <> E.advid =>
      res.[id] = idealfct E.secrets ].
proof.
proc.
seq 1: (let inp = E.inp in 
        let advinpsx = E.advinpsx in
           0 <= E.advid < N
         /\ (forall (id : int), 0 <= id < N => repss_integr (col N id inp))
         /\ repss_integr E.comp 
         /\ (forall i, 0 <= i < N => repss_correct1 E.secrets.[i] (col N i inp))
         /\   reconstruct_vss_one E.comp = idealfct_of_inp inp
         /\ (E.secrets.[E.advid]=sum (mkaddshares (extract E.advid inp)))).
call (pi1_spec sx); skip => |>. progress [-delta] => //=. 
inline E.output.
wp; call(_:true); wp; call(_:true); auto => |>.
progress [-delta].
rewrite /reconstruct_vss.
rewrite nth_mkseq 1:// /=  H8 1://=.
rewrite /reconstruct_vss_one.
have ->:(
  (vec N
     (fun (j : int) =>
        oget
          (majority
             (drop_elem j
                (col N j
                   (distribute_resshares Environment.advid{hr} result
                      Environment.comp{hr}).[id])))))=
  (vec N
     (fun (j : int) =>E.comp{hr}.[fresh j j].[j]))).
apply eq_in_mkseq. move => i ibd /=. 
have ->:(majority
     (drop_elem i
        (col N i
           (distribute_resshares Environment.advid{hr} result
              Environment.comp{hr}).[id])) =
Some Environment.comp{hr}.[fresh i i].[i]); last smt(oget_some).
apply (distribute_resshares_majority) => //=; smt(fresh_is_fresh). 
rewrite /repss_correct1 in H3.
rewrite /idealfct. rewrite -H3 1:/#. by apply H1. rewrite -H3 1:/#. by apply H1.
rewrite  mkadd_recon=> //=. rewrite H4 /idealfct.
rewrite (nth_map witness) //=. smt(size_mkseq). rewrite (nth_map witness _ _ 1). smt(size_mkseq gt1_N).
congr.  rewrite mkadd_recon. by apply H1. rewrite !nth_mkseq //=. rewrite !nth_mkseq //=. 
rewrite mkadd_recon => //. by apply H1. 
qed.

(* -------------------------------------------------------------------- *)
(* The output simulation property of the protocol. 
   The adversary learns no more information than the result of the computation. *)
local lemma output_simulation : 
  hoare [ E.protocol :
    size s = N /\
    0 <= E.advid < N ==> let y= oget (majority res) in 
    (finalmsg E.advid y E.comp.[E.advid] = E.comp) ].
proof.
exists* s; elim*=> sx /=. 
proc.
seq 1: (let inp = E.inp in 
        let advinpsx = E.advinpsx in
           0 <= E.advid < N /\
            (forall (id : int), 0 <= id < N => repss_integr (col N id E.inp{hr}))/\
            repss_integr E.comp /\
            reconstruct_vss_one E.comp = idealfct_of_inp inp). call (pi1_spec sx); skip => |>. progress [-delta] => //=. 
inline E.output.
wp. call(_:true). wp. call(_:true). auto => |>.
progress [-delta].
have hyp:=(comp_eq_finalmsg E.advid{hr} E.inp{hr} E.comp{hr}).
rewrite -H3 in hyp. 
have  -> :(oget
     (majority
        (reconstruct_vss Environment.advid{hr} result0
           (distribute_resshares Environment.advid{hr} result
              Environment.comp{hr}))))= (reconstruct_vss_one Environment.comp{hr}).
rewrite /reconstruct_vss /reconstruct_vss_one.
rewrite (majority_all_except_one' _ ( idealfct_of_inp Environment.inp{hr}) E.advid{hr}).
smt(gt3_N size_mkseq). smt(gt3_N size_mkseq). 
rewrite size_mkseq. move => j jbd neq.
rewrite nth_mkseq //=. smt(gt3_N).
rewrite neq //=. rewrite -H3.
rewrite -mkadd_recon 1://=.
congr. apply eq_in_mkseq => //= k kbd.
have tmp:= (distribute_resshares_majority E.advid{hr} result E.comp{hr}).
have -> : ((majority
     (drop_elem k
        (col N k
           (distribute_resshares Environment.advid{hr} result
              Environment.comp{hr}).[j]))) =
Some Environment.comp{hr}.[fresh k k].[k]); last by smt().
apply tmp => //=. smt(). smt(). smt(). 
rewrite oget_some -H3. by rewrite /reconstruct_vss_one. 
apply hyp => //.
qed.

lemma fix_advid advid bx sx1 sx2 :
  0 <= advid < N =>
  repss_list_private advid sx1 sx2 =>
  (fix advid (distribute_shares sx1) bx).[advid] = (fix advid (distribute_shares sx2) bx).[advid].
proof.
move=> Hadvid Hpriv.
rewrite /fix !nth_mkseq //=.
rewrite -eqmeq. smt(nth_mkseq size_mkseq). smt(nth_mkseq size_mkseq).
do 2!(split; first smt(size_mkseq nth_mkseq)).
move => i j ibd jbd.
do 2!(rewrite !nth_mkseq //=).
case  (advid = j /\ advid <> i); first smt().
move => H. (have [neq | eq]: (advid <>j \/ advid=i) by smt()); smt(nth_mkseq).
qed.

(* -------------------------------------------------------------------- *)
(* Privacy of the input phase (i.e. the replicated secret sharing and
   the consistency check/verify) *)
(* This is probably proven within lemma privacy_input_phase.
   It can hopefully be reused in  privacy_computation_phase *)

local lemma privacy_VSS_share id : equiv [ E.vss_share ~ E.vss_share :
      ={glob A, E.advid, dlr} /\ id = dlr{1}
   /\ 0 <= E.advid{1} < N
   /\ 0 <= id < N   
      ==>
      ={glob A, E.advid}
   /\ res{1}.[E.advid{1}] = res{2}.[E.advid{2}]
   /\ repss_integr res{1}
   /\ repss_integr res{2}
   /\ (id=E.advid{1} => ={res})].
proof.
proc.
admitted. (* Same proof as privacy_input_phase.  *)

local lemma privacy_input_phase : equiv [ E.input ~ E.input :
      ={glob A, E.advid}
   /\ 0 <= E.advid{1} < N
   /\ s{1}.[E.advid{1}] = s{2}.[E.advid{2}]  (* Adv's inputs are the same *)
      ==>
      ={glob A}
   /\ res{1}.[E.advid{1}] = res{2}.[E.advid{2}] (* shares that Adv received are same *)
   /\ (forall id, 0<= id < N => repss_integr (col N id res{1})) (* valid SS *)
   /\ (forall id, 0<= id < N => repss_integr (col N id res{2}))
 ].
proof.
proc; wp.
call (_ : true) => //.
seq 1 1 :
  (   ={glob A, E.advid}
  /\ 0 <= E.advid{1} < N
  /\ cube N shares{1} /\ cube N shares{2}
  /\ shares{1}.[E.advid{1}] = shares{2}.[E.advid{2}] (* shares that Adv sends are same *) 
  /\ (forall id, 0 <= id < N =>  (* shares that Adv receives are same *)
        repss_private E.advid{1} shares{1}.[id] shares{2}.[id])
  /\ (forall id, 0 <= id < N => id <> E.advid{1} => repss_integr shares{1}.[id])  (* valid SS *)
  /\ (forall id, 0 <= id < N => id <> E.advid{1} => repss_integr shares{2}.[id])    
); first by  exists* s{1}; elim* => s1; exists* s{2}; elim* => s2; exists* E.advid{2}; elim* => advid; first by call (do_sharing_private s1 s2 advid)=> //.
exists* shares{1}; elim*=> shares1.
exists* shares{2}; elim*=> shares2.
sp.
seq 3 3:
  (  ={glob A, E.advid, E.rx}
  /\ 0 <= E.advid{1} < N
  /\ cube N shares{1} /\ cube N shares{2}
  /\ shares1 = shares{1} 
  /\ shares2 = shares{2}    
  /\ Environment.pshares{1} = transpose shares{1}
  /\ Environment.pshares{2} = transpose shares{2}    
  /\ shares{1}.[E.advid{1}] = shares{2}.[E.advid{2}] (* shares that Adv received are same *)
  /\ (forall id, 0 <= id < N =>  (* shares that Adv sent are same *)
        repss_private E.advid{1} shares{1}.[id] shares{2}.[id]) 
  /\ (forall id, 0 <= id < N => id <> E.advid{1} => repss_integr shares{1}.[id])  (* valid SS *)
  /\ (forall id, 0 <= id < N => id <> E.advid{1} => repss_integr shares{2}.[id])
  /\ reqs_integr E.advid{1} E.rx{1}   (* rx has right size *)
  /\ (forall i j, 0<= i < N => 0<= j < N => i<>E.advid{2} => E.rx{2}.[i].[j] => j<>E.advid{2})
  /\ reqs_pshares_compat E.rx{1} E.pshares{1}  (* if no complaint, then rx and pshares match *)
  /\ reqs_pshares_compat E.rx{2} E.pshares{2}  ).
  call(_: true). 
 (* This is no longer allowed after a proc:
 https://www.easycrypt.info/trac/ticket/17363#ticket
    conseq (verify_shares_private shares1 shares2) verify_shares_integr verify_shares_integr *)
  conseq (_: ={glob A, E.advid} /\
            shares1.[E.advid{1}] = shares2.[E.advid{2}] /\
            (forall (id : int),
               0 <= id < N =>
               repss_private E.advid{1} shares1.[id] shares2.[id]) /\
            (forall (id : int),
               0 <= id < N => id <> E.advid{1} => repss_integr shares1.[id]) /\
            (forall (id : int),
               0 <= id < N => id <> E.advid{1} => repss_integr shares2.[id]) /\
            0 <= E.advid{1} < N /\
            E.pshares{1} = distribute_shares shares1 /\
            E.pshares{2} = distribute_shares shares2 ==>
            ={glob A, E.advid, E.rx})
( _: 0 <= E.advid < N /\
            (forall (id : int),
               0 <= id < N => id <> E.advid => repss_integr shares.[id]) /\
            E.pshares = distribute_shares shares ==>
            E.pshares = distribute_shares shares /\
            reqs_integr E.advid E.rx /\
            reqs_pshares_compat E.rx E.pshares /\ square N E.rx)
( _: 0 <= E.advid < N /\
            (forall (id : int),
               0 <= id < N => id <> E.advid => repss_integr shares.[id]) /\
            E.pshares = distribute_shares shares ==>
            E.pshares = distribute_shares shares /\
            reqs_integr E.advid E.rx /\
            reqs_pshares_compat E.rx E.pshares /\ square N E.rx) => //.
  smt(). 
exists* shares; elim*=> sharesL; call (verify_shares_integr sharesL); call(_: true); by skip. 
exists* shares; elim*=> sharesR; call (verify_shares_integr sharesR); call(_: true); by skip.
call (verify_shares_private shares1 shares2). call(_: true). skip; smt(nth_mkseq eq_in_mkseq).
call(broadcast_shares_private shares1 shares2); skip.
progress[-delta]. 
apply fix_advid => // /#. 
 apply (fix_integr _ _ _ E.rx{2}) => //=; by apply distribute_shares_type.
apply (fix_integr _ _ _ E.rx{2}) => //=; by apply distribute_shares_type.
qed.

(* more predicates -- move elsewhere *)
(* valid opened difference in multiplication *)
pred opened_diff_honest (advid : int) (opened_diff : zmod option matrix4) =
  forall id i j,
  0 <= id < N => 0 <= i < N => 0 <= j < N =>  (* if there is a complaint, then Adv was involved in computation of a_i*b_j *)
  ! (forall k, 0 <= k < N => odflt Zp.one opened_diff.[id].[i].[j].[k] = Zp.zero)
     => i <> advid /\ j <> advid.

pred mult_inp_private (advid : int) (a1 a2 : zmod matrix) (b1 b2 : zmod matrix) =
      0 <= advid < N
   /\ a1.[advid] = a2.[advid]
   /\ b1.[advid] = b2.[advid]
   /\ repss_integr a1
   /\ repss_integr a2
   /\ repss_integr b1      
   /\ repss_integr b2.

pred shared_terms_rep_private (advid : int) (shared_terms_rep1 shared_terms_rep2 : zmod matrix5) =
  (forall i j k, 0 <= i < N /\ 0 <= j < N /\ 0 <= k < N
        => shared_terms_rep1.[i].[j].[k].[advid]  (* shares that are meant to be sent to Adv *)
        = shared_terms_rep2.[i].[j].[k].[advid] ) /\
  (forall i j, 0 <= i < N /\ 0 <= j < N 
        => shared_terms_rep1.[i].[j].[advid]  (* shares that Adv will send *)
         = shared_terms_rep2.[i].[j].[advid] ).

(* honest parties' sharings of a_i*b_j are the same - needed in privacy_mult_check_term_sharing *)       
pred shared_terms_rep_private' (advid : int) (sharedterms_rep_distr1 sharedterms_rep_distr2 : zmod matrix5) =       
  (* if Adv knows a_i and b_j, then all (alleged) sharings of a_i*b_j follow the same distribution in both executions *)
  (forall i j id, 0 <= i < N /\ 0 <= j < N => i <> advid => j <> advid => id <> i => id <> j =>
      sharedterms_rep_distr1.[i].[j].[id] = sharedterms_rep_distr2.[i].[j].[id]) /\
  (* if Adv does not know both a_i and b_j, i.e. all parties involved are honest, then all sharings are sharings of a_i*b_j *)
  (forall i j sen, 0 <= i < N => 0 <= j < N => 0 <= sen < N => 
                   (i = advid \/ j = advid) => (* Adv not involved *)
                     sen <> i => sen <> j => (* all differences are 0 *)
       (* in each program, sen and fresh i j shared the same value *)            
   (   sum (mkaddshares sharedterms_rep_distr1.[i].[j].[sen]) 
     = sum (mkaddshares sharedterms_rep_distr1.[i].[j].[fresh i j]) ) /\
   (   sum (mkaddshares sharedterms_rep_distr2.[i].[j].[sen])
     = sum (mkaddshares sharedterms_rep_distr2.[i].[j].[fresh i j]) )).

(* adversary's knowledge is the same in both programs - needed in privacy_mult_determine_term_sharing *)       
pred sharedterms_rep_distr_private (advid : int) (sharedterms_rep_distr1 sharedterms_rep_distr2 : zmod matrix5) =       
shared_terms_rep_private advid (distribute_shared_terms sharedterms_rep_distr1) (distribute_shared_terms sharedterms_rep_distr2).
       
(* honest parties' sharings of a_i*b_j are the same - needed in privacy_mult_check_term_sharing *)       
pred sharedterms_rep_distr_private' (advid : int) (sharedterms_rep_distr1 sharedterms_rep_distr2 : zmod matrix5) =       
shared_terms_rep_private' advid (distribute_shared_terms sharedterms_rep_distr1) (distribute_shared_terms sharedterms_rep_distr2).
   
pred shared_diff_integr (shared_diff:zmod matrix5) =
  cube5 N shared_diff /\
  (forall i j k, 0 <= i < N /\ 0 <= j < N /\ 0 <= k < N
        /\ i <> k /\ j <> k
        => repss_integr (col N k shared_diff.[i].[j])).

pred shared_diff_private (advid:int) (shared_diff1 shared_diff2 : zmod matrix5) =
  forall i j, 0 <= i < N => 0 <= j < N =>
  (* differences Adv receives *)
  shared_diff1.[i].[j].[advid] = shared_diff2.[i].[j].[advid] /\
  (* differences to what Adv sent *)
  (col N advid shared_diff1.[i].[j]) = (col N advid shared_diff2.[i].[j]).

pred shared_diff_honest (advid : int) (shared_diff : zmod matrix5) =
  (* if Adv does not know both a_i and b_j, i.e. all parties involved are honest, then all opened_diff.[i].[j] are 0 *)
  forall i j sen, 0 <= i < N => 0 <= j < N => 0 <= sen < N => 
                   (i = advid \/ j = advid) => (* Adv not involved *)
                   sen <> i => sen <> j => (* all differences are 0 *)
      reconstruct_vss_one (col N sen shared_diff.[i].[j]) = Zp.zero.

pred opened_diff_private (advid : int) (opened_diff1 opened_diff2 : zmod option matrix4) =
  0 <= advid < N =>
  cube4 N opened_diff1 /\
  cube4 N opened_diff2 /\
  opened_diff1 = opened_diff2 (* these opened values are public *) .

(* auxiliary lemmas for privacy_computation_phase *)
local lemma privacy_mult_term_sharing a1 a2 b1 b2 : equiv [ E.mult_term_sharing ~ E.mult_term_sharing :
      ={glob A, E.advid}
   /\ 0 <= E.advid{1} < N
   /\ a1 = a{1} /\ a2 = a{2} /\ b1 = b{1} /\ b2 = b{2}
   /\ mult_inp_private E.advid{1} a{1} a{2} b{1} b{2}      
      ==>
      ={glob A, E.advid}
   /\ shared_terms_rep_private E.advid{1} res{1} res{2}
   /\ shared_terms_rep_private' E.advid{1} res{1} res{2}
   /\ shared_terms_rep_integr res{1}   
   /\ shared_terms_rep_integr res{2}    ]. 
admitted. (* Basic reasoning about while loops *)

local lemma privacy_mult_check_term_sharing : equiv [ E.mult_check_term_sharing ~ E.mult_check_term_sharing :
      ={glob A, E.advid}
   /\ 0 <= E.advid{1} < N
   /\ sharedterms_rep_distr_integr sharedterms_rep_distr{1}
   /\ sharedterms_rep_distr_integr sharedterms_rep_distr{2}
   /\ sharedterms_rep_distr_private E.advid{1} sharedterms_rep_distr{1} sharedterms_rep_distr{2}
   /\ sharedterms_rep_distr_private' E.advid{1} sharedterms_rep_distr{1} sharedterms_rep_distr{2}     
      ==>
      ={glob A, E.advid}
   /\ 0 <= E.advid{1} < N
   /\ opened_diff_private E.advid{1} res{1} res{2}
   /\ opened_diff_honest E.advid{1} res{1}].
proof.
proc.
seq 3 3: (
      ={glob A, E.advid, shared_diff}
   /\ 0 <= E.advid{1} < N
   /\ shared_diff_integr shared_diff{1}
   /\ shared_diff_private E.advid{1} shared_diff{1} shared_diff{2}   
   /\ shared_diff_honest E.advid{1} shared_diff{1}
   /\ sharedterms_rep_distr_integr sharedterms_rep_distr{1}
   /\ sharedterms_rep_distr_integr sharedterms_rep_distr{2}
   /\ sharedterms_rep_distr_private E.advid{1} sharedterms_rep_distr{1} sharedterms_rep_distr{2}
   /\ sharedterms_rep_distr_private' E.advid{1} sharedterms_rep_distr{1} sharedterms_rep_distr{2} ).
  call(_: true). sp; skip. admitted. (* progress[-delta]. This takes a very long time *)

(* mkrepshares_mult outputs secret sharing with witness on diagonal  *)
local lemma mkrepshares_mult_integr shares:
  size shares = N =>
  (forall i j, 0 <= i < N => 0 <= j < N => shares.[i] = shares.[j]) => 
(* all entries are the same -> there is probably a more convenient way to state this *)
    repss_integr (vec N (fun id => mkrepshares_mult id shares.[id])). 
progress [-delta].
split. split; smt(nth_mkseq size_mkseq gt1_N).
smt(nth_mkseq size_mkseq gt1_N).
qed.
    
local lemma privacy_mult_determine_term_sharing : equiv [E.mult_determine_term_sharing ~ E.mult_determine_term_sharing :
      ={glob A, E.advid}
   /\ 0 <= E.advid{1} < N
   /\ mult_inp_private E.advid{1} a{1} a{2} b{1} b{2}
   /\ sharedterms_rep_distr_integr sharedterms_rep_distr{1}   
   /\ sharedterms_rep_distr_integr sharedterms_rep_distr{2}
   /\ sharedterms_rep_distr_private E.advid{1} sharedterms_rep_distr{1} sharedterms_rep_distr{2}
   /\ opened_diff_private E.advid{1} opened_diff{1} opened_diff{2}
   /\ opened_diff_honest E.advid{1} opened_diff{1}
      ==>
      ={glob A, E.advid}
   /\ (forall i j, 0 <= i < N => 0 <= j < N => repss_integr res{1}.[i].[j]) 
   /\ (forall i j, 0 <= i < N => 0 <= j < N => repss_integr res{2}.[i].[j])    
   /\ (forall i j, 0 <= i < N => 0 <= j < N =>   (* shares that Adv received *)
        res{1}.[i].[j].[E.advid{1}] = res{2}.[i].[j].[E.advid{2}]) ].
proof.
proc.
seq 1 1: (={glob A, E.advid, bx_shares_rep}
   /\ 0 <= E.advid{1} < N
   /\ mult_inp_private E.advid{1} a{1} a{2} b{1} b{2}
   /\ sharedterms_rep_distr_integr sharedterms_rep_distr{1}   
   /\ sharedterms_rep_distr_integr sharedterms_rep_distr{2}
   /\ sharedterms_rep_distr_private E.advid{1} sharedterms_rep_distr{1} sharedterms_rep_distr{2}
   /\ opened_diff_private E.advid{1} opened_diff{1} opened_diff{2}
   /\ opened_diff_honest E.advid{1} opened_diff{1}
   /\ cube4 N bx_shares_rep{1}
   /\ forall rec i j sen, 0<= rec < N => 0<= i < N => 0<= j < N => 0<= sen < N => 
        (bx_shares_rep{1}.[rec].[i].[j].[sen]=(if (sen <> E.advid{1} /\ sen <> i) then a{1}.[fresh i E.advid{2}].[i] else witness
                                           ,if (sen <> E.advid{1} /\ sen <> j) then b{1}.[fresh j E.advid{2}].[j] else witness))).
wp; skip. admit. 
(* EC bug: EC does not work well with large terms.
The seq above just states the conclusion of the weakest precondition.
The seq could be avoided, but it would slow EC down too much.
progress[-delta]. hangs *)
wp; call(_: true).
call(_: true).
auto.
progress[-delta].
  (* repss_integr res{1}.[i].[j] *)
  case (forall (id : int), 0 <= id < N =>
        forall (k  : int), 0 <= k < N =>
                          odflt Zp.one opened_diff{1}.[id].[i].[j].[k] =
                          Zp.zero) => [nocomplaint|complaint].
  (* no complaint *)
   do 2! rewrite nth_mkseq //=.
   have ->:( (forall (id : int), 0 <= id < N =>
               forall (k : int),  0 <= k < N =>
                 odflt Zp.one opened_diff{1}.[id].[i].[j].[k] = Zp.zero)=true) by smt().
    simplify. rewrite /sharedterms_rep_distr_integr in H2.
    have advbd: (0 <= E.advid{2} < N) by smt(). 
    have gt2_N:(2<N) by smt(gt3_N). 
    elim H2 => sub rest. have :=(rest i j (fresh i j)).  smt(fresh_is_fresh).
   (* There was a complaint.
      broadcast and create new sharing using mkrepshares_mult *)
  do 2! rewrite nth_mkseq //=.
  have ->:( (forall (id : int), 0 <= id < N =>
             forall (k : int), 0 <= k < N =>
                 odflt Zp.one opened_diff{1}.[id].[i].[j].[k] = Zp.zero)=false) by smt().
  simplify. have Hadv: (i <> E.advid{2} /\ j <> E.advid{2}) by smt().
  (* remains to prove that input to mkrepshares_mult_integr is list where all entries have same value (a_i, b_j) *)
  apply mkrepshares_mult_integr; first smt(size_map size_mkseq).
  move => i0 j0 i0bd j0bd. 
  rewrite /uncurry map_mkseq //= !nth_mkseq 1,2:/#. 
  rewrite /(\o) /=. congr. (* a / b *) congr. 
   rewrite (majority_all_except_one (drop_elem i _) a{1}.[fresh i E.advid{2}].[i] 
                              (if E.advid{2} < i then E.advid{2} else E.advid{2} - 1)).
   rewrite size_drop_elem //= size_map //= !nth_mkseq //= !nth_mkseq //= nth_mkseq 1,3:/# /= size_set; 
   smt(size_drop_elem size_mkseq nth_mkseq gt3_N size_set).
    apply (all_drop_elem witness).
    move => j1 j1bd. rewrite nth_drop_elem //=.
    case (j1<i) => cs.
     rewrite nth_mkseq //= (nth_map witness witness) //=.  rewrite !nth_mkseq //= !nth_mkseq //= . smt(nth_mkseq size_set).
      rewrite !nth_mkseq //= !nth_mkseq //= !nth_mkseq //=; smt(). (* closes j1<i *)
     have j1bd':j1<N-1. elim j1bd; first smt(). by rewrite !nth_mkseq 1:// size_drop_elem //= size_map //= !nth_mkseq //= !nth_mkseq //= ; smt(size_drop_elem size_mkseq nth_mkseq gt3_N).
     case (j1 + 1 = Environment.advid{2}); first smt().
     case ( j1 + 1 = i \/ i = Environment.advid{2}); first smt().
     rewrite (nth_map witness witness). do 3!rewrite !nth_mkseq //=. smt(nth_mkseq size_set).
     do 3!rewrite !nth_mkseq //=. move => neq neqj1. rewrite get_set_if neqj1 //=. smt().
(* Finished LHS *)
    apply eq_sym. apply (majority_all_except_one (drop_elem i _) a{1}.[fresh i E.advid{2}].[i] (if E.advid{2} < i then E.advid{2} else E.advid{2} - 1)).
(* Here we copy the code above. *)
    rewrite size_drop_elem //= size_map //= !nth_mkseq //= !nth_mkseq //= nth_mkseq 1,3:/# /= size_set; smt(size_drop_elem size_mkseq nth_mkseq gt3_N size_set).
    apply (all_drop_elem witness).
    move => j1 j1bd. rewrite nth_drop_elem //=.
    case (j1<i) => cs.
     rewrite nth_mkseq //= (nth_map witness witness) //=.  rewrite !nth_mkseq //= !nth_mkseq //= . smt(nth_mkseq size_set). 
      rewrite !nth_mkseq //= !nth_mkseq //= !nth_mkseq //=; smt(). (* closes j1<i *)
     have j1bd':j1<N-1. elim j1bd; first smt(). by rewrite !nth_mkseq 1:// size_drop_elem //= size_map //= !nth_mkseq //= !nth_mkseq //= ; smt(size_drop_elem size_mkseq nth_mkseq gt3_N).
    case (j1 + 1 = Environment.advid{2}); first smt().
    case ( j1 + 1 = i \/ i = Environment.advid{2}); first smt().
    rewrite (nth_map witness witness). do 3!rewrite !nth_mkseq //=.  smt(nth_mkseq size_set).
    do 3!rewrite !nth_mkseq //=.
    move => neq neqj1. rewrite get_set_if neqj1 //=. smt().
admit (* And the same for b *).
admit. (* repss_integr res{2}.[i].[j]  is the same proof.*)  (* We want a lemma for the last four cases *)
(* privacy *)
do 2! rewrite !nth_mkseq //=.
have advbd: (0 <= E.advid{2} < N) by smt().
have [cub1 [cub2 ->]]:=(H5 advbd). 
case (forall (id : int), 0 <= id < N =>
      forall (k  : int), 0 <= k < N =>
                          odflt Zp.one opened_diff{2}.[id].[i].[j].[k] =
                          Zp.zero); last smt(nth_mkseq). move: H4.  
rewrite /sharedterms_rep_distr_private /distribute_shared_terms /shared_terms_rep_private.
progress [-delta]. rewrite !nth_mkseq //=. have tmp:=(H4 i j (fresh i j)). 
rewrite (nth_map witness) in tmp. smt(). rewrite (nth_map witness) in tmp. smt().
rewrite transpose_unfold in tmp. smt(). smt(fresh_is_fresh gt3_N). smt().
rewrite (nth_map witness) in tmp. smt(). rewrite (nth_map witness) in tmp. smt().
rewrite transpose_unfold in tmp. smt(). smt(fresh_is_fresh gt3_N). smt(). smt(fresh_is_fresh gt3_N). 
qed.

(* privacy of computation phase. *)
local lemma privacy_computation_phase : equiv [ E.computation_mult ~ E.computation_mult :
      ={glob A, E.advid}
   /\ 0 <= E.advid{1} < N 
   /\ mult_inp_private E.advid{1} (col N 0 pshares{1}) (col N 0 pshares{2}) (col N 1 pshares{1}) (col N 1 pshares{2})   
      ==>
      ={glob A, E.advid}  (* sufficient if next gate is output! For the general case we also need: *)
   /\ repss_integr res{1} (* extra condition to argue about privacy if comp is used as gate *)
   /\ repss_integr res{2} 
   /\ res{1}.[E.advid{1}] = res{2}.[E.advid{2}] ].
proof.
exists* E.advid{1}; elim*=> advid.
proc. 
inline E.multiplication.
sp.
exists* a{1}; elim*=> a1.
exists* a{2}; elim*=> a2.
exists* b{1}; elim*=> b1.
exists* b{2}; elim*=> b2. 
seq 2 2 : ( ={glob A, E.advid}
   /\ 0 <= E.advid{1} < N
   /\ mult_inp_private E.advid{1} a{1} a{2} b{1} b{2}
   /\ sharedterms_rep_distr_integr sharedterms_rep_distr{1}
   /\ sharedterms_rep_distr_integr sharedterms_rep_distr{2}      
   /\ sharedterms_rep_distr_private' E.advid{1} sharedterms_rep_distr{1} sharedterms_rep_distr{2}
   /\ sharedterms_rep_distr_private E.advid{1} sharedterms_rep_distr{1} sharedterms_rep_distr{2} ).
   wp; call(privacy_mult_term_sharing a1 a2 b1 b2); skip. 
   progress [-delta].  smt(distribute_sharedterms_integr). smt(distribute_sharedterms_integr).

rewrite /sharedterms_rep_distr_private'.
rewrite !distribute_shared_terms_invol => //=. smt(size_mkseq nth_mkseq). smt(size_mkseq nth_mkseq). 
rewrite /sharedterms_rep_distr_private.
rewrite !distribute_shared_terms_invol => //=. smt(size_mkseq nth_mkseq). smt(size_mkseq nth_mkseq).
seq 1 1 :( ={glob A, E.advid}
   /\ 0 <= E.advid{1} < N
   /\ mult_inp_private E.advid{1} a{1} a{2} b{1} b{2}
   /\ sharedterms_rep_distr_integr sharedterms_rep_distr{1}   
   /\ sharedterms_rep_distr_integr sharedterms_rep_distr{2}
   /\ sharedterms_rep_distr_private E.advid{1} sharedterms_rep_distr{1} sharedterms_rep_distr{2}
   /\ opened_diff_private E.advid{1} opened_diff{1} opened_diff{2}
   /\ opened_diff_honest E.advid{1} opened_diff{1}).
call (privacy_mult_check_term_sharing). skip => |>.  progress [-delta].
wp; call(_ : true) => /=; wp.
call privacy_mult_determine_term_sharing.
skip. 
have termbd1: (forall term, 0 <= term < ((N-1)*N) => 0 <= (term %/ N) < N). move => tm hyp. rewrite ltz_divLR; smt(ltz_divLR gt1_N divz_ge0 gt1_N). 
have termbd2: (forall term, 0 <= term < ((N-1)*N) => 0 <= (term %% N) < N) by smt(ltz_pmod gt1_N modn_ge0).
progress[-delta].
(* integrity of output *)
rewrite /rearrange_sharedterms.
have geprod: (N <= (N - 1) * N) by smt(gt1_N).
apply mklocalsums_M_integr. smt(). smt(size_mkseq). smt(nth_mkseq size_mkseq). smt(nth_mkseq size_mkseq).
move => c cbd. have :=(H15 (c %/ N) (c %% N) (termbd1 c cbd) (termbd2 c cbd)). move => [[hyp yes] _].
split. split; smt(nth_mkseq size_mkseq). smt(nth_mkseq). 
(* Copy for the RHS *)
rewrite /rearrange_sharedterms.
have geprod: (N <= (N - 1) * N) by smt(gt1_N).
apply mklocalsums_M_integr. smt(). smt(size_mkseq). smt(nth_mkseq size_mkseq). smt(nth_mkseq size_mkseq).
move => c cbd. have :=(H15 (c %/ N) (c %% N) (termbd1 c cbd) (termbd2 c cbd)). move => [[hyp yes] _]. 
split. split; smt(nth_mkseq size_mkseq). split; smt(nth_mkseq). 
(* privacy of output *) 
do !rewrite nth_mkseq //=.
apply eq_in_mkseq' => //= c cbd /=.
case (Environment.advid{2} = c); first by smt().
move => advneq.
congr.
apply eq_in_mkseq' => //= ij ijbd /=.
do !rewrite nth_mkseq //=.
have tmp:= (H17 (ij %/ N) (ij %% N));smt().
qed.

(* -------------------------------------------------------------------- *)
(* Privacy statement for the input and computation phase *)
local lemma input_independence : equiv [ E.pi1 ~ E.pi1 :
      ={glob A, E.advid}
   /\ 0 <= E.advid{1} < N
   /\ s{1}.[E.advid{1}] = s{2}.[E.advid{2}]
      ==>
      ={glob A} ].
proof.
proc. 
seq 1 1 : (={glob A, E.advid}
  /\ 0 <= E.advid{1} < N
  /\ mult_inp_private E.advid{1} (col N 0 rinp{1}) (col N 0 rinp{2}) (col N 1 rinp{1}) (col N 1 rinp{2}));
last by by wp;call privacy_computation_phase.
call privacy_input_phase; skip. 
progress [-delta].
have bd0:(0 <= 0<N) by smt(gt0_N). have bd1:(0<=1<N) by smt(gt1_N).
have := (H6 0 bd0); have := (H6 1 bd1); have := (H7 0 bd0); have := (H7 1 bd1); smt(nth_mkseq ge0_N).
qed.
end section S.