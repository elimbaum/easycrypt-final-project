require import AllCore Bool List Array.
require import IntDiv.
require import Distr.

require import ZModFin.

require import StdRing. import RField.
require import StdOrder. import IntOrder.
require import StdBigop Bigalg. import Bigreal Bigreal.BRM.
require import DList DInterval.

import Zp Zp.ZModule Zp.ZModpRing ZModFinType MZModFinite ZModule.

require import Util.
require import Vote.

pragma -oldip.

(* -------------------------------------------------------------------- *)
abbrev "_.[_]" ['a] (s : 'a list) (i : int) = nth witness s i.

(* -------------------------------------------------------------------- *)
type 'a matrix = 'a list list.

op square (l : int) (m : zmod matrix) =
  size m = l /\ forall i, 0 <= i < l => size m.[i] = l.

(* -------------------------------------------------------------------- *)
clone import BigZModule as ZmodBigZModule with
  type t <- zmod,
  op ZM.zeror <- Zp.zero,
  op ZM.( + ) <- Zp.(+),
  op ZM.([-]) <- Zp.([-])
  proof * by smt.

abbrev sum = ZmodBigZModule.big predT idfun.

lemma sum2E (m : zmod matrix) M : square M m =>
    sum (map sum m)
  = bigi predT (fun i => bigi predT (fun j => m.[i].[j]) 0 M) 0 M.
proof.
case=> [<- sz_m]; rewrite (big_nth witness) size_map.
have ->: predT \o nth witness (map sum m) = predT by done.
rewrite !big_seq; apply/eq_bigr => i /= /mem_range [ge0_i lt_im].
by rewrite (nth_map witness) // (big_nth witness predT idfun) sz_m.
qed.

lemma sum_mkseq F n : sum (mkseq F n) = bigi predT F 0 n.
proof. by rewrite big_map. qed.

(* -------------------------------------------------------------------- *)
abbrev dzmod = MZModFinite.dunifin.

(* -------------------------------------------------------------------- *)
op N : { int | 1 < N } as gt1_N.

lemma gt0_N : 0 < N by smt(gt1_N).
lemma ge0_N : 0 <= N by smt(gt1_N).

hint exact : gt0_N ge0_N.

(* -------------------------------------------------------------------- *)
op idealfct (xs : zmod list) = sum xs.

(* -------------------------------------------------------------------- *)
(* returns the i-th column of the matrix *)
op col i (m : 'a matrix) : 'a list =
  mkseq (fun j => m.[j].[i]) N.

(* -------------------------------------------------------------------- *)
(* Auxiliary lemma: sum is invariant by transposition *)
lemma matrix_sum_commutativity (M : int) (m : zmod matrix) :
     0 <= M => square M m
  => sum (map sum m) = sum (mkseq (fun j => sum (mkseq (fun i => m.[i].[j]) M)) M).
proof.
move=> ge0_M sq_M; rewrite (sum2E _ M sq_M) exchange_big sum_mkseq.
by apply/eq_bigr=> i _ /=; rewrite sum_mkseq.
qed.

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
   Party id (i.e. the dealer) sends to himself all the additive shares. 
   Add witness in the diagonal.
   In row i, column j we add the jth additive share*)
op mkrepshares (id : int) (addshares : zmod list) : zmod matrix =
  mkseq (fun i =>
  mkseq (fun j =>
    if i <> j || i = id then addshares.[j] else witness) N) N.

(* distribute_shares takes shares.[id].[i].[j], where shares.[id] is the
   replicated secret sharing of party id's secret.
   The function returns pshares.[id].[i].[j], where pshares.[id].[i] is 
   the share of party i's secret that party id knows. *)
op distribute_shares (shares : zmod matrix list) : zmod matrix list =
  mkseq (fun id =>
  mkseq (fun i  => shares.[i].[id]) N) N.

(* -------------------------------------------------------------------- *)
(* The local addition of the honest party's shares.
   Each party has a matrix of shares, they sum the columns to get a 
   share of the result of the computation. *)
op mklocalsums (advid : int) (pshares : zmod matrix list) : zmod matrix =
  mkseq (fun id =>
  mkseq (fun j  =>
    (* We only make the sum for the honest parties *)
    if id = advid then witness else
    (* For party j, col j only contains witness *)
    if id = j then witness else 
    sum (col j pshares.[id])) N) N.

(* -------------------------------------------------------------------- *)
(* All parties send their share of the result to all other parties.
   The adversary can send possible different shares to the honest parties.
   advc: row i contains the share that the adversary sends to party i. 
   psums: row i contains party i's share of the result (note that the 
   row index by advid contains only witness. *)
op distribute_resshares advid (advc : zmod matrix) (psums : zmod matrix) : zmod matrix list =
  mkseq (fun id =>
  mkseq (fun i  => if i = advid then advc.[id] else psums.[i]) N) N.

(* -------------------------------------------------------------------- *)
(* Verifiable reconstruction of the result. *)
op reconstruct_vss (advid : int) (advres : zmod)
               (resshares : zmod matrix list) : zmod list =
  mkseq (fun id =>
    if id = advid then advres else
      sum (mkseq (fun j =>
        oget (majority (drop_elem j (col j resshares.[id])))) N)) N.

(* -------------------------------------------------------------------- *)
pred addss_private (j : int) (shares1 shares2 : zmod list) =
     (size shares1 = N /\ size shares2 = N)
  /\ (forall i, 0 <= i < N => i <> j => shares1.[i] = shares2.[i]).

pred repss_private_honest (advid : int) (rshares1 rshares2 : zmod matrix) =
     square N rshares1 /\ square N rshares2
  /\ forall i j,
       0 <= i < N => 0 <= j < N => j <> advid =>
       rshares1.[i].[j] = rshares2.[i].[j].

pred repss_private0 (advid : int) id (m1 m2 : zmod matrix) =
     square N m1 /\ square N m2
  /\ (id = advid => m1 = m2)
  /\ (id <> advid =>
      (forall i j,
          0 <= i < N => 0 <= j < N => j <> advid =>
          m1.[i].[j] = m2.[i].[j]) /\
       forall j, 0 <= j < N => m1.[advid].[j] = m2.[advid].[j]).

pred repss_private_aux (advid : int) l (mx1 mx2 : zmod matrix list) =
     size mx1 = l /\ size mx2 = l
  /\ forall id, 0 <= id < l => repss_private0 advid id mx1.[id] mx2.[id].

pred repss_private (advid : int) (mx1 mx2 : zmod matrix list) =
     size mx1 = N /\ size mx2 = N
  /\ mx1.[advid] = mx2.[advid]
  /\ forall id, 0 <= id < N =>
       square N mx1.[id] /\ square N mx2.[id]
    /\ (id <> advid =>
         (forall i j,
          0 <= i < N => 0 <= j < N => j <> advid =>
          mx1.[id].[i].[j] = mx2.[id].[i].[j]) /\
         forall j, 0 <= j < N => mx1.[id].[advid].[j] = mx2.[id].[advid].[j]).

pred repss_integr_honest (id : int) (m : zmod matrix) =
  square N m /\
  (forall k, 0 <= k < N => k <> id => m.[k].[k] = witness) /\
  (forall i j k,
    0 <= i < N => 0 <= j < N => 0 <= k < N =>
    i <> k => j <> k =>
    m.[i].[k] = m.[j].[k]) /\
  (forall i j,
    0 <= id < N => 0 <= i < N => 0 <= j < N =>
    m.[i].[id] = m.[j].[id]).

pred repss_integr (advid : int) (mx : zmod matrix list) =
  size mx = N /\
  forall id, 0 <= id < N =>
    square N mx.[id] /\
    (id <> advid =>
      (forall k, 0 <= k < N => k <> id => mx.[id].[k].[k] = witness) /\
      (forall i j k,
        0 <= i < N => 0 <= j < N => 0 <= k < N =>
        i <> k => j <> k => mx.[id].[i].[k] = mx.[id].[j].[k]) /\
      (forall i j,
        0 <= id < N => 0 <= i < N => 0 <= j < N => mx.[id].[i].[id] = mx.[id].[j].[id])).

pred repss_integr0 (advid : int) id (m : zmod matrix) =
  square N m /\
  (id <> advid =>
    (forall k, 0 <= k < N => k <> id => m.[k].[k] = witness) /\
    (forall i j k,
      0 <= i < N => 0 <= j < N => 0 <= k < N =>
      i <> k => j <> k =>
      m.[i].[k] = m.[j].[k]) /\
    (forall i j,
      0 <= id < N => 0 <= i < N => 0 <= j < N =>
      m.[i].[id] = m.[j].[id])).

pred repss_integr_aux (advid : int) l (mx : zmod matrix list) =
  size mx = l /\
  forall id, 0 <= id < l => repss_integr0 advid id mx.[id].

pred pshares_integr_full (advid : int) (pshares : zmod matrix list) =
  size pshares = N /\
  (forall i, 0 <= i < N => square N pshares.[i]) /\
  (forall i k,
    0 <= i < N => 0 <= k < N =>
    k <> i => k <> advid =>
    pshares.[i].[k].[i] = witness) /\
  (forall i1 i2 j k,
    0 <= i1 < N => 0 <= i2 < N => 0 <= j < N => 0 <= k < N =>
    i1 <> k => i2 <> k => j <> advid =>
    pshares.[i1].[j].[k] = pshares.[i2].[j].[k]) /\
  (forall i1 i2 k,
    0 <= i1 < N => 0 <= i2 < N => 0 <= k < N =>
    i1 <> k => i2 <> k => i1 <> advid => i2 <> advid =>
    pshares.[i1].[advid].[k] = pshares.[i2].[advid].[k]) /\
  (forall i1 i2 k,
    0 <= i1 < N => 0 <= i2 < N => 0 <= k < N =>
    k <> advid =>
    pshares.[i1].[k].[k] = pshares.[i2].[k].[k]).

(* -------------------------------------------------------------------- *)
pred repss_correct (advid : int) (sx : zmod list) (mx : zmod matrix list) =
  forall id, 0 <= id < N => id <> advid => sum mx.[id].[id] = sx.[id].

pred repss_correct0 (advid : int) id s (m : zmod matrix) =
  id <> advid => sum m.[id] = s.

pred repss_correct_aux (advid : int) l (sx : zmod list) (pshares : zmod matrix list) =
  forall id, 0 <= id < l => repss_correct0 advid id sx.[id] pshares.[id].

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
type reqs = bool array.
type bcast = zmod option list.

(* -------------------------------------------------------------------- *)
module type QueryProtocol = {
  proc complains(id : int, j : int, parties : int * int) : bool
}.

(* -------------------------------------------------------------------- *)
module Protocol (Q : QueryProtocol) = {
  proc share_additive(s : zmod) : zmod list = {
    var mxrd;
    mxrd <$ dlist dzmod (N-1);
    return (s - sum mxrd) :: mxrd;
  }

  proc share_replicated(id : int, s : zmod) : zmod matrix = {
    var addshares : zmod list;
    addshares <- share_additive(s);
    return mkrepshares id addshares;
  }
    
  (* Collect complaints *)
  proc verify(id : int) : reqs = {
    var b, j, k, l;
    var rx = mkarray (mkseq (fun _ => false) N);

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

  proc broadcast(id : int, v : zmod list, bx : reqs) = {
    return mkseq (fun j => bx.[j] ? Some v.[j] : None) N;
  }
}.

(* -------------------------------------------------------------------- *)
module type Adv = {
  proc sharing      (_ : zmod) : zmod matrix
  proc complains    (_ : zmod matrix * zmod * int * int) : bool
  proc broadcast    (_ : reqs) : bcast
  proc localsum     (_ : unit) : unit
  proc bxshareofres (_ : zmod matrix) : zmod matrix
  proc getres       (_ : unit) : zmod
  
(* To model information send *to* the Adv. *)
  proc recv_shares  (_ : zmod matrix) : unit
  proc recv_rx      (_ : reqs list  ) : unit
  proc recv_bx      (_ : bcast list ) : unit
  proc recv_fixed_shares (_ : zmod matrix) : unit
}.

(* -------------------------------------------------------------------- *)
(*  Update the shares as by the protocol:
    - all the honest parties accept the updated values
    - the honest parties ignore sharings that they are not supposed to know *)
op fix (advid : int) (pshares : zmod matrix list) (bx : bcast list) =
  mkseq (fun id =>
  mkseq (fun i  =>
  mkseq (fun j  =>
      if id <> advid && id = j then
        pshares.[id].[i].[j] (* ignore the broadcasted value *)
      else odflt pshares.[id].[i].[j] bx.[i].[j]
    ) N) N) N.

(* -------------------------------------------------------------------- *)
(* pshares is a list of matrices, where matrix i contains the shares 
   that party i knows.
   We get a matrix, where the first row is the row indexed by advid in 
   matrix 1, and row i is the row indexed by advid in matrix i. *)
op getAdvpView_sends advid (pshares : zmod matrix list) : zmod matrix =
  mkseq (fun id =>
    if id = advid then nseq N witness else pshares.[id].[advid]) N.

(* pview is the sharing of the input that the adversary
   committed to during the input phase *)
op extract_advinpsx (pview : zmod matrix) : zmod list =
  mkseq (fun i => oget (majority (drop_elem i (col i pview)))) N.

(* local sum of the shares that the adversary knows
   Note that this is a subprocedure of mklocalsum *)
op extract_resshares advid (initadvshares : zmod matrix)
  (rx : reqs list) (bx : bcast list) (pview : zmod matrix) : zmod list =
  mkseq (fun j => (* we sum the columns *)
    if advid = j then witness else
    sum (mkseq (fun k =>
     if k <> advid then pview.[k].[j] else
       if rx.[advid].[j] then oget bx.[advid].[j]
       else
       (* Pick x s.t. 0 <= x < N and x <> advid and x <> j. Possible in the case N >= 4 *)
       let x = choiceb (fun i => 0 <= i < N /\ i <> advid /\ i <> j) 0 in
       initadvshares.[x].[j]
    ) N)) N.

module Environment(A : Adv) = {
  var advid   : int
  var pshares : zmod matrix list

  (* View variables *)
  var initadvshares    : zmod matrix
  var psharesbeforefix : zmod matrix list
  var rx : reqs list
  var bx : bcast list

  var advinpsx : zmod list
  var advresshares : zmod list

  var comp : zmod matrix
  var y : zmod

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
          (* This is an optimization *)
          aout <@ A.complains(pshares.[advid], vj, id, pa);
        } else {
          (* We here inline the complaining of 2 honest parties *)
          aout <- pshares.[p.`1].[id].[j] <> pshares.[p.`2].[id].[j];
        }
      }

      return aout;
    }
  }

  (* Replicated SS for the secret s of party i. *)
  proc do_one_sharing(i : int, s : zmod) : zmod matrix = {
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

    (shares, i) <- ([], 0); while (i < N)
    {
      (* replicated secret sharing for s.[i] *)
      repshares <@ do_one_sharing(i, s.[i]);
      shares <- rcons shares repshares;
      i <- i + 1;
    }

    return shares;
  }

  proc verify_shares() : reqs list = {
    var i, rx, rx1;

    (rx1, rx, i) <- (witness, [], 0); while (i < N) {
      rx1 <@ Protocol(QP).verify(i);
      rx  <- rcons rx rx1;
      i   <- i + 1;
    }

    return rx;
  }

  proc broadcast_shares(rx : reqs list) : bcast list = {
    var i, j, bx, bx1;

    (bx1, bx, i) <- (witness, [], 0); while (i < N) {
      if (i = advid) {
        bx1 <@ A.broadcast(rx.[i]);
      } else {
        bx1 <@ Protocol(QP).broadcast(i, pshares.[i].[i], rx.[i]);
      }

      (* Verify that all the requests are served, abort the protocol otherwise *)
      j <- 0; while (j < N) {
        if (rx.[i].[j] && bx1.[j] = None)
          Misc.abort();
      }

      bx <- rcons bx bx1;
      i  <- i + 1;
    }

    return bx;
  }

  (* The input phase shares the inputs and does consistency check.
     s is a list of secrets. *)
  proc input(s : zmod list) : zmod matrix list = {
    var shares;

    (* TODO: add the following call *)
    (* A.recv_secret(sx.[advid]); *)

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

    (* Return the global view *)
    return pshares;
  }

  proc computation (pshares : zmod matrix list) : zmod matrix = {
    (* Inform the adversary that we start the local computation phase *)
    A.localsum();
    (* Perform the local addition for all the honest parties and return the view *)
    return mklocalsums advid pshares;
  }

  proc pi1 (s : zmod list) : zmod matrix list * zmod matrix = {
    var rinp, rcomp;

    rinp  <@ input (s);
    rcomp <@ computation (rinp);
    return (rinp, rcomp);
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
    var inp, out;

    (* run the input and computation phase *)
    (inp, comp) <@ pi1 (s);

    (* Extract the adversary's committed input and save it. 
      To make things easier we construct a new list of inputs 
      where we replace the adversary's input with what he committed to *)
    advinpsx <- extract_advinpsx (getAdvpView_sends advid inp);

    (* Extract the adversary's shares of the output *)
    advresshares <- extract_resshares advid initadvshares rx bx inp.[advid];

    (* run the output phase *)   
    out <@ output (comp);
    y   <- oget (majority out);

    return out;
  }
}.

(* -------------------------------------------------------------------- *)
section S.

declare module A : Adv { Environment }.
local module E = Environment(A).

(* We assume that the adversaries shares are well-formed *)
axiom Awf : hoare [ A.sharing : true ==> square N res ].

(* -------------------------------------------------------------------- *)
(* --- Lemmas for Additive Secret Sharing --- *)

(* Privacy of additive secret sharing agains N-1 colluding parties. *)
local lemma share_additive_private j :
  0 <= j < N =>
  equiv [ Protocol(E.QP).share_additive ~ Protocol(E.QP).share_additive :
          true ==> addss_private j res{1} res{2} ].
proof. 
move=> lt_jN; proc; exists* s{1}, s{2}; elim*=> s1 s2 /=.
pose F := fun i => if i+1 = j then s2 - s1 else Zp.zero.
pose f := fun (l : zmod list) => mkseq (fun i => l.[i] + F i) (N-1).
pose g := fun (l : zmod list) => mkseq (fun i => l.[i] - F i) (N-1).
have hsz : forall (s : zmod list),
  s \in dlist dzmod (N-1) <=> (size s = N-1).
+ move=> s; have h := supp_dlist dzmod (N-1) s _; 1:smt().
  split=> [/h [//]|szs]; apply/h; split=> //; apply/allP.
  by move=> x _; rewrite dunifin_fu.
have hszmk : forall (Z : int -> zmod), size (mkseq Z (N-1)) = N-1.
+ by move=> Z; rewrite size_mkseq max_ler // [smt(gt1_N)].
have c1 : forall (l : _ list), size l = N-1 => f (g l) = l.
+ move=> s szs; apply/(eq_from_nth witness); 1:smt().
  move=> i; rewrite hszmk => lti.
  by do! rewrite nth_mkseq //=; ringeq.
rnd f g => /=; skip=> &1 &2 |>; split; 1:smt(gt1_N).
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
+ by rewrite szs => lti; do! rewrite nth_mkseq //=; ringeq.
move=> _; split=> /=; first by rewrite hszmk szs /#.
move=> i ltiN ne_ij; case: (i = 0) => [->>|nz_i]; last first.
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

local lemma share_replicated_integr id0 s0 :
  hoare [ Protocol(E.QP).share_replicated :
    id = id0 /\ s = s0 /\ 0 <= id < N ==>
    repss_integr_honest id0 res /\ sum res.[id0] = s0 ].
proof.
proc.
have efn := (eq_from_nth<:zmod> witness).
call (share_additive_correct s0)=> //.
by auto; smt(size_mkseq nth_mkseq gt1_N).
qed.

local lemma share_replicated_private i advid :
  0 <= advid < N =>
  equiv [ Protocol(E.QP).share_replicated ~ Protocol(E.QP).share_replicated :
      ={id} /\ i = id{1} ==>
      repss_private_honest advid res{1} res{2}
   /\ repss_integr_honest i res{1}
   /\ repss_integr_honest i res{2} ].
proof.
move=> Hadvid; proc.
call (share_additive_private advid Hadvid).
by skip=> &1 &2 |>; progress; smt(size_mkseq nth_mkseq).
qed.

(* -------------------------------------------------------------------- *)

(* --- Lemmas for do_one_sharing --- *)

local lemma do_one_sharing_integr id sinp :
  hoare [ E.do_one_sharing :
      sinp = s /\ id = i /\ 0 <= id < N /\ 0 <= E.advid < N
      ==>
      repss_integr0 E.advid id res /\
      repss_correct0 E.advid id sinp res ].
proof.
proc.
if; first by call Awf; auto; smt().
by call (share_replicated_integr id sinp); auto; smt().
qed.

local lemma do_one_sharing_private id :
  equiv [ E.do_one_sharing ~ E.do_one_sharing :
      ={glob A, E.advid, i} /\ id = i{1} /\ 0 <= E.advid{1} < N
   /\ (i{1} = E.advid{1} => ={s})
      ==>
      ={glob A, E.advid}
   /\ repss_private0 E.advid{1} id res{1} res{2}
   /\ repss_integr0 E.advid{1} id res{1} /\ repss_integr0 E.advid{1} id res{2} ].
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
  call (share_replicated_private id advid hadv).
  by skip=> &1 &2 |> /#.
qed.

(* -------------------------------------------------------------------- *)

(* --- Lemmas for do_sharing --- *)

local lemma do_sharing_integr advid sx :
  hoare [ E.do_sharing :
      sx = s
   /\ E.advid = advid /\ 0 <= E.advid < N
      ==>
      E.advid = advid
   /\ repss_integr E.advid res
   /\ repss_correct E.advid sx res ].
proof.
proc; sp.
while (
     E.advid = advid
  /\ s = sx
  /\ 0 <= E.advid < N
  /\ 0 <= i <= N
  /\ size shares = i
  /\ repss_integr_aux E.advid i shares
  /\ repss_correct_aux E.advid i sx shares);
last by skip=> &1 |> /#.
wp.
exists* i; elim*=> i.
call (do_one_sharing_integr i sx.[i]).
by auto=> &1 |>; smt(size_rcons nth_rcons).
qed.

(* The sharing of all the inputs (including the adversary's) fulfil privacy.
   I.e. the adversary gets one share of each of the other party's secrets.
   But it reveals no information about the honest parties input. *)
local lemma do_sharing_private :
  equiv [ E.do_sharing ~ E.do_sharing :
      ={glob A, E.advid} /\ 0 <= E.advid{1} < N
   /\ s{1}.[E.advid{1}] = s{2}.[E.advid{1}]
      ==>
      ={glob A, E.advid}
   /\ repss_private E.advid{1} res{1} res{2}
   /\ repss_integr E.advid{1} res{1}
   /\ repss_integr E.advid{1} res{2}
  ].
proof.
proc; wp; sp.
while (
     ={glob A, E.advid, i}
  /\ size shares{1} = i{1}
  /\ size shares{2} = i{1}
  /\ 0 <= i{1} <= N /\ 0 <= E.advid{1} < N
  /\ (s{1}.[E.advid{1}] = s{2}.[E.advid{2}])
  /\ repss_private_aux E.advid{1} i{1} shares{1} shares{2}
  /\ repss_integr_aux E.advid{1} i{1} shares{1}
  /\ repss_integr_aux E.advid{1} i{1} shares{2});
last by skip => &1 &2 |> /#.
wp;
exists* i{1}; elim*=> i.
call (do_one_sharing_private i).
by skip=> &1 &2; smt(size_rcons nth_rcons).
qed.

(* -------------------------------------------------------------------- *)
pred reqs_pshares_compat (advid : int) (rx : reqs list) (pshares : zmod matrix list) =
  size rx = N /\
  forall id, 0 <= id < N =>
    size rx.[id] = N /\
    forall j k l,
      0 <= j < N => 0 <= k < N => 0 <= l < N =>
      k <> j => l <> j => k <> advid => l <> advid =>
      ! rx.[id].[j] =>
      pshares.[k].[id].[j] = pshares.[l].[id].[j].

pred reqs_pshares_compat_aux2 advid id j k (lb : int) (r : reqs) (pshares : zmod matrix list) =
  forall l, 0 <= l < lb =>
    k <> j => l <> j => k <> advid => l <> advid =>
    ! r.[j] => pshares.[k].[id].[j] = pshares.[l].[id].[j].

pred reqs_pshares_compat_aux1 advid id j (kb lb : int) (r : reqs) (pshares : zmod matrix list) =
  forall k, 0 <= k < kb =>
    reqs_pshares_compat_aux2 advid id j k lb r pshares.

pred reqs_pshares_compat_aux0 advid id (jb kb lb : int) (r : reqs) (pshares : zmod matrix list) =
  size r = N /\
  forall j, 0 <= j < jb =>
    reqs_pshares_compat_aux1 advid id j kb lb r pshares.

pred reqs_pshares_compat_aux advid (idb jb kb lb : int) (rx : reqs list) (pshares : zmod matrix list) =
  size rx = idb /\
  forall id, 0 <= id < idb =>
    reqs_pshares_compat_aux0 advid id jb kb lb rx.[id] pshares.

lemma reqs_pshares_compat_aux1_set advid id j kb lb r pshares m :
   reqs_pshares_compat_aux1 advid id j kb lb r pshares =>
   reqs_pshares_compat_aux1 advid id j kb lb r.[m <- true] pshares.
proof. by rewrite /reqs_pshares_compat_aux1 /reqs_pshares_compat_aux2; smt(size_set get_set_if). qed.

lemma reqs_pshares_compat_aux0_set advid id jb kb lb r pshares m :
   reqs_pshares_compat_aux0 advid id jb kb lb r pshares =>
   reqs_pshares_compat_aux0 advid id jb kb lb r.[m <- true] pshares.
proof. by rewrite /reqs_pshares_compat_aux0 /reqs_pshares_compat_aux1 /reqs_pshares_compat_aux2; smt(size_set get_set_if). qed.

(* -------------------------------------------------------------------- *)
pred reqs_integr (advid : int) (rx : reqs list) =
  forall i j,
    0 <= i < N => 0 <= j < N => i <> advid => rx.[i].[j] => j <> advid.

pred reqs_integr_aux0 advid i (jb : int) (rx : reqs) =
  i <> advid => forall j, 0 <= j < jb => rx.[j] => j <> advid.

pred reqs_integr_aux advid (ib jb : int) (rx : reqs list) =
  forall i, 0 <= i < ib => reqs_integr_aux0 advid i jb rx.[i].

local lemma reqs_integr_aux0_init advid i :
  reqs_integr_aux0 advid i N (mkarray (mkseq (fun (_ : int) => false) N)).
proof. by move=> _??; rewrite getE ofarrayK nth_mkseq=> //. qed.

(* -------------------------------------------------------------------- *)

(* --- Lemmas for verify_shares --- *)

local lemma verify_shares_integr (shares : zmod matrix list) :
  hoare [ E.verify_shares :
          0 <= E.advid < N
       /\ repss_integr E.advid shares
       /\ E.pshares = distribute_shares shares
      ==>
          E.pshares = distribute_shares shares
       /\ reqs_integr E.advid res
       /\ reqs_pshares_compat E.advid res E.pshares ].
proof.
conseq (_ : _ ==>
          E.pshares = distribute_shares shares
       /\ reqs_integr_aux E.advid N N res
       /\ reqs_pshares_compat_aux E.advid N N N N res E.pshares);
first by move=> &1 |>; rewrite /reqs_pshares_compat /reqs_pshares_compat_aux /reqs_pshares_compat_aux0 /reqs_pshares_compat_aux1 /reqs_pshares_compat_aux2 /#.
proc.
exists* E.advid; elim*=> advid.
pose I := fun x => x = distribute_shares shares /\ repss_integr advid shares.
sp;
conseq (_ : (E.advid, i, rx) = (advid, 0, []) /\ I E.pshares ==> _) => //.
while (
     E.advid = advid
  /\ 0 <= i <= N
  /\ size rx = i
  /\ I E.pshares
  /\ reqs_integr_aux advid i N rx
  /\ reqs_pshares_compat_aux advid i N N N rx E.pshares
);
last by skip => &1 |>; smt(gt1_N).
wp.
inline Protocol(Environment(A).QP).verify.
wp; sp=> /=.
while (
     E.advid = advid
  /\ id = i
  /\ 0 <= i < N
  /\ 0 <= j <= N
  /\ size rx = i
  /\ size rx0 = N
  /\ I E.pshares
  /\ reqs_integr_aux advid i N rx
  /\ reqs_integr_aux0 advid i N rx0
  /\ reqs_pshares_compat_aux advid i N N N rx E.pshares
  /\ reqs_pshares_compat_aux0 advid i j N N rx0 E.pshares
);
last by skip=> &1 |>; smt(size_mkarray size_mkseq nth_rcons size_rcons reqs_integr_aux0_init).
wp; sp=> /=.
while (
     E.advid = advid
  /\ id = i
  /\ 0 <= i < N
  /\ 0 <= j < N
  /\ 0 <= k <= N
  /\ size rx = i
  /\ size rx0 = N
  /\ I E.pshares
  /\ reqs_integr_aux advid i N rx
  /\ reqs_integr_aux0 advid i N rx0
  /\ reqs_pshares_compat_aux advid i N N N rx E.pshares
  /\ reqs_pshares_compat_aux0 advid i j N N rx0 E.pshares
  /\ reqs_pshares_compat_aux1 advid i j k N rx0 E.pshares
);
last by skip=> &1 |> /#.
wp; sp=> /=.
while (
     E.advid = advid
  /\ id = i
  /\ 0 <= i < N
  /\ 0 <= j < N
  /\ 0 <= k < N
  /\ 0 <= l <= N
  /\ size rx = i
  /\ size rx0 = N
  /\ I E.pshares
  /\ reqs_integr_aux advid i N rx
  /\ reqs_integr_aux0 advid i N rx0
  /\ reqs_pshares_compat_aux advid i N N N rx E.pshares
  /\ reqs_pshares_compat_aux0 advid i j N N rx0 E.pshares
  /\ reqs_pshares_compat_aux1 advid i j k N rx0 E.pshares
  /\ reqs_pshares_compat_aux2 advid i j k l rx0 E.pshares
);
last by skip=> &1 |> /#.
wp=> /=.
if; last by skip=> &1 |> /#.
seq 1 :
   ( E.advid = advid
  /\ id = i
  /\ 0 <= i < N
  /\ 0 <= j < N
  /\ 0 <= k < N
  /\ 0 <= l < N
  /\ size rx = i
  /\ size rx0 = N
  /\ I E.pshares
  /\ reqs_integr_aux advid i N rx
  /\ reqs_integr_aux0 advid i N rx0
  /\ reqs_pshares_compat_aux advid i N N N rx E.pshares
  /\ reqs_pshares_compat_aux0 advid i j N N rx0 E.pshares
  /\ reqs_pshares_compat_aux1 advid i j k N rx0 E.pshares
  /\ reqs_pshares_compat_aux2 advid i j k l rx0 E.pshares
  /\ k <> j /\ l <> j /\ k <> l
  /\ (k <> advid => l <> advid =>
       (b <=> E.pshares.[k].[i].[j] <> E.pshares.[l].[i].[j]))
  /\ (id <> advid => b => j <> advid)
).
+ inline Environment(A).QP.complains.
  wp; sp.
  if; last by skip=> &1 |> /#.
  if; last by auto=> &1 |>; smt(nth_mkseq).
  by sp; call(_ : true); skip=> &1 |> /#.
+ if; last by skip=> &1 |> /#.
  wp=> /=.
  skip=> &1 |>; smt(get_set_if reqs_pshares_compat_aux0_set reqs_pshares_compat_aux1_set).
qed.

(* Privacy of verify_shares *)
local lemma verify_shares_private (shares1 shares2 : zmod matrix list) :
  equiv [ E.verify_shares ~ E.verify_shares :
           ={glob A, E.advid}
        /\ repss_private E.advid{1} shares1 shares2
        /\ repss_integr E.advid{1} shares1
        /\ repss_integr E.advid{1} shares2
        /\ 0 <= E.advid{1} < N
        /\ E.pshares{1} = distribute_shares shares1
        /\ E.pshares{2} = distribute_shares shares2
     ==>
        ={glob A, res} ].
proof.
exists* E.advid{1}; elim*=> advid.
pose p1 := distribute_shares shares1.
pose p2 := distribute_shares shares2.
pose I  := fun x1 x2 =>
  x1 = p1 /\ x2 = p2 /\
  repss_private advid shares1 shares2 /\
  repss_integr advid shares1 /\ repss_integr advid shares2.
proc.
sp; conseq (_ :
     ={glob A, E.advid, i, rx}
  /\ (E.advid, i, rx){1} = (advid, 0, [])
  /\ I E.pshares{1} E.pshares{2} ==> _) => //.
while (={glob A, E.advid, rx, i}
  /\ E.advid{1} = advid
  /\ 0 <= i{1} <= N
  /\ size rx{1} = i{1}
  /\ I E.pshares{1} E.pshares{2});
last by skip=> &1 &2 |>; smt(gt1_N).
wp=> /=.
inline Protocol(Environment(A).QP).verify.
sp; wp.
while (={glob A, E.advid, id, rx, rx0, i, j}
  /\ i{1} = id{1}
  /\ E.advid{1} = advid
  /\ 0 <= i{1} < N
  /\ 0 <= j{1} <= N
  /\ size rx{1} = i{1}
  /\ I E.pshares{1} E.pshares{2});
last by skip=> &1 &2 |>; smt(size_rcons).
sp; wp.
while (={glob A, E.advid, id, rx, rx0, i, j, k}
  /\ i{1} = id{1}
  /\ E.advid{1} = advid
  /\ 0 <= i{1} < N
  /\ 0 <= j{1} < N
  /\ 0 <= k{1} <= N
  /\ size rx{1} = i{1}
  /\ I E.pshares{1} E.pshares{2});
last by skip=> &1 &2 |>; smt(size_rcons).
sp; wp.
while (={glob A, E.advid, id, rx, rx0, i, j, k, l}
  /\ i{1} = id{1}
  /\ E.advid{1} = advid
  /\ 0 <= i{1} < N
  /\ 0 <= j{1} < N
  /\ 0 <= k{1} < N
  /\ 0 <= l{1} <= N
  /\ size rx{1} = i{1}
  /\ I E.pshares{1} E.pshares{2});
last by skip=> &1 &2 |>; smt(size_rcons).
wp.
if; 1:smt(); last by skip=> &1 &2 |> /#.
seq 1 1 : (={glob A, E.advid, id, rx, rx0, i, j, k, l, b}
  /\ i{1} = id{1}
  /\ E.advid{1} = advid
  /\ 0 <= i{1} < N
  /\ 0 <= j{1} < N
  /\ 0 <= k{1} < N
  /\ 0 <= l{1} < N
  /\ size rx{1} = i{1}
  /\ I E.pshares{1} E.pshares{2});
last by if; auto=> /#.
inline Environment(A).QP.complains.
sp; wp.
if=> //=.
if=> //=; last by auto=> &1 &2 |>; smt(nth_mkseq).
sp; call(_ : true).
skip=> &1 &2 |>.
have efn := eq_from_nth<:zmod> witness.
progress.
elim H7=>->>[->>[??]].
rewrite /p1 /p2 /= /distribute_shares /=.
do 2!rewrite nth_mkseq /= 1:/#.
apply eq_in_mkseq=> /= i hi.
case (i = E.advid{2})=>[<<-|]; smt().
smt(nth_mkseq).
qed.

(* -------------------------------------------------------------------- *)
(* --- Predicates for broadcast --- *)

pred valid_rx (rx : reqs list) =
  size rx = N /\ (forall i, 0 <= i < N => size rx.[i] = N).

pred valid_bx (advid l : int) (bx : bcast list) =
  size bx = l /\ (forall i, 0 <= i < l /\ i <> advid => size bx.[i] = N).

pred reqs_bcast_compat (advid : int) (rx : reqs list) (bx : bcast list) (pshares : zmod matrix list) =
  forall i j v, 0 <= i < N => 0 <= j < N =>
    (bx.[i].[j] = None <=> !rx.[i].[j]) /\
    (i <> advid =>
      (rx.[i].[j] => bx.[i].[j] = Some pshares.[i].[i].[j]) /\
      (bx.[i].[j] = Some v => rx.[i].[j] /\ v = pshares.[i].[i].[j])).

pred reqs_bcast_compat_aux0 (advid : int) i jb (rs : reqs) (bs : bcast) (pshares : zmod matrix list) =
  i <> advid =>
  forall j v, 0 <= j < jb =>
    (rs.[j] => bs.[j] = Some pshares.[i].[i].[j]) /\
    (bs.[j] = Some v => rs.[j] /\ v = pshares.[i].[i].[j]) /\
    (bs.[j] = None <=> ! rs.[j]).

pred reqs_bcast_compat_aux1 (advid : int) i jb (rs : reqs) (bs : bcast) (pshares : zmod matrix list) =
  i = advid => forall j, 0 <= j < jb => bs.[j] = None <=> !rs.[j].

pred reqs_bcast_compat_aux advid ib jb (rx : reqs list) (bx : bcast list) (pshares : zmod matrix list) =
  forall i, 0 <= i < ib =>
    reqs_bcast_compat_aux0 advid i jb rx.[i] bx.[i] pshares /\
    reqs_bcast_compat_aux1 advid i jb rx.[i] bx.[i] pshares.

(* -------------------------------------------------------------------- *)

(* --- Lemmas for broadcast --- *)

local lemma broadcast_shares_integr reqs :
  hoare [ E.broadcast_shares :
    rx = reqs /\ valid_rx rx /\ 0 <= E.advid < N ==>
    valid_bx E.advid N res /\
    reqs_bcast_compat E.advid reqs res E.pshares ].
proof.
exists* E.advid; elim*=> advid.
proc.
sp.
conseq (_ :
  (E.advid, i, rx, bx) = (advid, 0, reqs, []) /\
  0 <= E.advid < N /\ valid_rx rx ==>
  valid_bx E.advid N bx /\ reqs_bcast_compat_aux E.advid N N reqs bx E.pshares); 1:smt().
+ by rewrite /reqs_bcast_compat_aux /reqs_bcast_compat_aux0 /reqs_bcast_compat_aux1 /#.
while (
     E.advid = advid
  /\ 0 <= i <= N
  /\ rx = reqs
  /\ 0 <= E.advid < N
  /\ valid_rx rx
  /\ valid_bx advid i bx
  /\ reqs_bcast_compat_aux advid i N rx bx E.pshares);
last by skip=> &1 &2 |>; smt(gt1_N).
seq 1 :
(
     E.advid = advid
  /\ 0 <= i < N
  /\ rx = reqs
  /\ valid_rx rx
  /\ 0 <= E.advid < N
  /\ valid_bx advid i bx
  /\ (i <> E.advid => size bx1 = N)
  /\ reqs_bcast_compat_aux advid i N rx bx E.pshares
  /\ reqs_bcast_compat_aux0 advid i N rx.[i] bx1 E.pshares
).
if.
  + by call (_ : true); auto.
  + inline Protocol(Environment(A).QP).broadcast.
    by auto=> &1 |>; smt(size_rcons nth_rcons size_mkseq nth_mkseq gt1_N).
wp; sp.
while (
     E.advid = advid
  /\ 0 <= i < N
  /\ 0 <= j <= N
  /\ rx = reqs
  /\ valid_rx rx
  /\ 0 <= E.advid < N
  /\ valid_bx advid i bx
  /\ (i <> E.advid => size bx1 = N)
  /\ reqs_bcast_compat_aux advid i N rx bx E.pshares
  /\ reqs_bcast_compat_aux0 advid i N rx.[i] bx1 E.pshares
  /\ reqs_bcast_compat_aux1 advid i j rx.[i] bx1 E.pshares
);
first by if; [ by call abort_false_1 | by auto ].
by skip=> &1 |>; smt(size_rcons nth_rcons gt1_N).
qed.

local lemma broadcast_shares_private (shares1 shares2 : zmod matrix list) :
  equiv [ E.broadcast_shares ~ E.broadcast_shares :
      ={glob A, E.advid, rx}
   /\ 0 <= E.advid{1} < N
   /\ repss_integr E.advid{1} shares1
   /\ repss_integr E.advid{1} shares2
   /\ reqs_integr E.advid{1} rx{1}
   /\ reqs_pshares_compat E.advid{1} rx{1} E.pshares{1}
   /\ reqs_pshares_compat E.advid{1} rx{1} E.pshares{2}
   /\ repss_private E.advid{1} shares1 shares2
   /\ E.pshares{1} = distribute_shares shares1
   /\ E.pshares{2} = distribute_shares shares2
      ==>
      ={glob A, res} ].
proof.
proc.
exists* E.advid{1}; elim*=> advid.
sp;
conseq (_ :
     ={glob A, E.advid, i, rx, bx}
  /\ (E.advid, i, bx){1} = (advid, 0, [])
  /\ 0 <= E.advid{1} < N
  /\ repss_integr E.advid{1} shares1
  /\ repss_integr E.advid{1} shares2
  /\ reqs_integr_aux E.advid{1} N N rx{1}
  /\ reqs_pshares_compat E.advid{1} rx{1} E.pshares{1}
  /\ reqs_pshares_compat E.advid{1} rx{1} E.pshares{2}
  /\ repss_private E.advid{1} shares1 shares2
  /\ E.pshares{1} = distribute_shares shares1
  /\ E.pshares{2} = distribute_shares shares2 ==> _);
first by smt().
while (={glob A, E.advid, i, rx, bx}
  /\ E.advid{1} = advid
  /\ 0 <= E.advid{1} < N
  /\ 0 <= i{1} <= N
  /\ repss_integr E.advid{1} shares1
  /\ repss_integr E.advid{1} shares2
  /\ reqs_integr_aux E.advid{1} N N rx{1}
  /\ reqs_pshares_compat E.advid{1} rx{1} E.pshares{1}
  /\ reqs_pshares_compat E.advid{1} rx{1} E.pshares{2}
  /\ repss_private E.advid{1} shares1 shares2
  /\ E.pshares{1} = distribute_shares shares1
  /\ E.pshares{2} = distribute_shares shares2
  );
last by skip=> &1 &2 |>; smt(gt1_N).
seq 1 1 :
(={glob A, E.advid, i, rx, bx, bx1}
  /\ E.advid{1} = advid
  /\ 0 <= i{1} < N
  /\ repss_integr E.advid{1} shares1
  /\ repss_integr E.advid{1} shares2
  /\ reqs_integr_aux E.advid{1} N N rx{1}
  /\ reqs_pshares_compat E.advid{1} rx{1} E.pshares{1}
  /\ reqs_pshares_compat E.advid{1} rx{1} E.pshares{2}
  /\ repss_private E.advid{1} shares1 shares2
  /\ E.pshares{1} = distribute_shares shares1
  /\ E.pshares{2} = distribute_shares shares2
).
if=> //; first by call (_ : true); auto.
+ inline Protocol(Environment(A).QP).broadcast.
  auto=> &1 &2 |> *.
  apply eq_in_mkseq => j hj /=.
  do 4!(rewrite nth_mkseq /= 1:/#).
  by case (rx{2}.[i{2}].[j])=> //= /#.
wp; sp.
while
(={glob A, E.advid, i, j, rx, bx, bx1}
  /\ E.advid{1} = advid
  /\ 0 <= i{1} < N
  /\ 0 <= j{1} <= N
  /\ repss_integr E.advid{1} shares1
  /\ repss_integr E.advid{1} shares2
  /\ repss_private E.advid{1} shares1 shares2
  /\ E.pshares{1} = distribute_shares shares1
  /\ E.pshares{2} = distribute_shares shares2
); last by skip=> &1 &2 |>; smt(gt1_N).
if=> //.
by call abort_false_2.
qed.

(* -------------------------------------------------------------------- *)
local lemma fix_integr_full advid sx shares pshares rx bx :
  0 <= advid < N =>
  repss_integr advid shares =>
  pshares = distribute_shares shares =>
  reqs_integr advid rx =>
  reqs_pshares_compat advid rx pshares =>
  valid_bx advid N bx =>
  reqs_bcast_compat advid rx bx pshares =>
  repss_correct advid sx shares =>
  pshares_integr_full advid (fix advid pshares bx) /\
  repss_correct advid sx (fix advid pshares bx).
proof.
move=> Hadv Hi e Hrix Hri Hb Hrb Hmxc.
split;
first by rewrite /reqs_bcast_compat in Hrb; smt(size_mkseq nth_mkseq gt1_N).
rewrite /reqs_bcast_compat in Hrb.
have := eq_from_nth<:zmod> witness.
have Hpc : repss_correct advid sx pshares by smt(size_mkseq nth_mkseq).
move=> {Hmxc}.
rewrite /repss_correct=> ?.
smt(size_mkseq nth_mkseq).
qed.

pred psums_integr (advid : int) (psums : zmod matrix) =
  square N psums /\
  (forall i j k,
    0 <= i < N => 0 <= j < N => 0 <= k < N =>
    i <> advid => j <> advid => i <> k => j <> k =>
    psums.[i].[k] = psums.[j].[k]) /\
  (forall j, 0 <= j < N => psums.[advid].[j] = witness) /\
  (forall i, 0 <= i < N => psums.[i].[i] = witness).

local lemma mklocalsums_integr advid pshares :
    0 <= advid < N =>
    pshares_integr_full advid pshares =>
    psums_integr advid (mklocalsums advid pshares).
proof. smt(size_mkseq nth_mkseq eq_in_mkseq gt1_N). qed.

pred reconstruct_vss_correct (advid : int) sx (ress : zmod list) =
  forall i, 0 <= i < N => i <> advid => ress.[i] = sum sx.

(* -------------------------------------------------------------------- *)
local lemma distribute_resshares_majority advid advc psums :
  4 <= N =>
  0 <= advid < N =>
  psums_integr advid psums =>
  let presshares = distribute_resshares advid advc psums in
  forall id i j,
    0 <= id < N => 0 <= i < N => 0 <= j < N =>
    i <> advid => i <> j =>
    majority (drop_elem j (col j presshares.[id])) = Some psums.[i].[j].
proof.
move=> nge4 Hadvid Hpsums presshares id i j hid hi hj inadvid inj.
case (j = advid)=> [->> | jnadvid].
- apply (majority_all');
  smt(size_mkseq nth_mkseq size_drop_elem nth_drop_elem).
- apply (majority_all_except_one' _ _ (if advid < j then advid else advid-1));
  smt(size_mkseq nth_mkseq size_drop_elem nth_drop_elem).
qed.

local lemma getAdvpView_sends_majority advid pshares :
  4 <= N =>
  0 <= advid < N =>
  pshares_integr_full advid pshares =>
  forall i j,
    0 <= i < N => 0 <= j < N =>
    i <> advid => i <> j =>
    majority (drop_elem j (col j (getAdvpView_sends advid pshares))) =
    Some pshares.[i].[advid].[j].
proof.
move=> nge4 Hadvid Hfi i j hi hj inj inadvid.
case (j = advid)=> [->> | jnadvid].
- apply (majority_all');
  smt(size_mkseq nth_mkseq size_drop_elem nth_drop_elem).
- apply (majority_all_except_one' _ _ (if advid < j then advid else advid-1));
  smt(size_mkseq nth_mkseq size_drop_elem nth_drop_elem).
qed.

(* -------------------------------------------------------------------- *)
local lemma extract_advinpsx_spec advid pshares :
  4 <= N =>
  0 <= advid < N =>
  pshares_integr_full advid pshares =>
  forall id j,
    0 <= id < N => 0 <= j < N => id <> advid => id <> j =>
    (extract_advinpsx (getAdvpView_sends advid pshares)).[j] = pshares.[id].[advid].[j].
proof.
move=> nge4 hadvid Hfi id j hid hj idnadvid idnj.
rewrite nth_mkseq //=.
pose x := pshares.[id].[advid].[j].
case (j = advid)=> [->> | jnadvid].
- rewrite (majority_all' _ x);
  smt(size_mkseq nth_mkseq size_drop_elem nth_drop_elem).
- rewrite (majority_all_except_one' _ x (if advid < j then advid else advid - 1));
  smt(size_mkseq nth_mkseq size_drop_elem nth_drop_elem).
qed.

local lemma output_spec_aux advid advc advres
                           (sx : zmod list) (pshares : zmod matrix list) :
    4 <= N =>
    0 <= advid < N =>
    let advinp = extract_advinpsx (getAdvpView_sends advid pshares) in
    sx.[advid] = sum advinp =>
    size sx = N =>
    pshares_integr_full advid pshares =>
    repss_correct advid sx pshares =>
    let psums = mklocalsums advid pshares in
    let presshares = distribute_resshares advid advc psums in
    reconstruct_vss_correct advid sx (reconstruct_vss advid advres presshares).
proof.
move=> nge4 Hadvid advinp Hsx Hpshare Hfi Hmx psums presshares id hid hnadvid.
have Hadvinp : size advinp = N by smt(size_mkseq).
pose sxm := mkseq (fun i => if i <> advid then pshares.[i].[i] else advinp) N.
have Hsxm : square N sxm.
+ split; first by smt(size_mkseq nth_mkseq).
  move=> j?.
  case (j = advid)=> [-> | ne]; 1: smt(size_mkseq nth_mkseq).
  by rewrite nth_mkseq //= ne /=; smt(size_mkseq nth_mkseq).
have Hpsums : psums_integr advid (mklocalsums advid pshares)
  by apply mklocalsums_integr.
have : sx = map sum sxm.
+ apply (eq_from_nth witness);
  first by rewrite size_map; smt(size_mkseq).
  move=> j hj.
  case(j = advid)=> [-> | jnadvid];
  by rewrite (nth_map witness witness); smt(nth_mkseq).
move=> ->.
rewrite (matrix_sum_commutativity N) 1,2:/#.
rewrite nth_mkseq //= hnadvid /=.
pose y :=
  big predT idfun
    (mkseq
      (fun j =>
          if advid <= 1 then
            if j <= 2 then psums.[3].[j] else psums.[2].[j]
          else (* 2 <= advid *)
            if 1 <= j then psums.[0].[j] else psums.[1].[j]) N).
apply (eq_trans _ y _).
+ rewrite /y; congr.
  apply eq_in_mkseq=> i hi /=.
  case (advid <= 1)=> [advidle1 | advidge2].
  - case (i <= 2)=> [? | ?];
      [ by rewrite (distribute_resshares_majority _ _ _ nge4 Hadvid Hpsums _ 3 i) // /#
      | by rewrite (distribute_resshares_majority _ _ _ nge4 Hadvid Hpsums _ 2 i) // /# ].
  - case (1 <= i)=> [? | ?];
      [ by rewrite (distribute_resshares_majority _ _ _ nge4 Hadvid Hpsums _ 0 i) // /#
      | by rewrite (distribute_resshares_majority _ _ _ nge4 Hadvid Hpsums _ 1 i) // /# ].
rewrite /y => {y}.
do 2!rewrite big_mapT.
have : N = N-0 by smt(). move=> ->; do 2!rewrite -/(range 0 N).
rewrite /(\o) {1 2}/idfun /=.
apply eq_big_int=> i hi /=.
rewrite /sxm=> {sxm Hsxm}.
pose y :=
  sum (mkseq (fun j => if j <> advid then pshares.[j].[j].[i] else advinp.[i]) N).
apply (eq_trans _ y _); last first.
+ rewrite /y; congr.
  by apply eq_in_mkseq; smt(size_mkseq nth_mkseq).
rewrite /y => {y}.
have Eadvinp :
  advinp.[i] =
    if advid <= 1 then
      if i <= 2 then pshares.[3].[advid].[i] else pshares.[2].[advid].[i]
    else (* 2 <= advid *)
      if 1 <= i then pshares.[0].[advid].[i] else pshares.[1].[advid].[i]
  by smt(size_mkseq nth_mkseq extract_advinpsx_spec).
rewrite Eadvinp=> {Eadvinp}.
case (advid <= 1)=> [advidle1 | advidge2].
- case (i <= 2)=> [jle2 | jgt2].
  + rewrite /psums /mklocalsums.
    rewrite nth_mkseq //= 1:/#.
    rewrite nth_mkseq //=.
    have : (3 <> i) by smt(). move=> -> /=.
    have : (3 <> advid) by smt(). move=> -> /=.
    do 2!rewrite big_mapT.
    rewrite /(\o) /idfun /=.
    have : N = N-0 by smt(). move=> ->; do 2!rewrite -/(range 0 N).
    by apply eq_big_int=> j hj /= /#.
  + rewrite /psums /mklocalsums.
    rewrite nth_mkseq //= 1:/#.
    rewrite nth_mkseq //=.
    have : (2 <> i) by smt(). move=> -> /=.
    have : (2 <> advid) by smt(). move=> -> /=.
    do 2!rewrite big_mapT.
    rewrite /(\o) /idfun /=.
    have : N = N-0 by smt(). move=> ->; do 2!rewrite -/(range 0 N).
    by apply eq_big_int=> j hj /= /#.
- case (1 <= i)=> [jge1 | jl1].
  + rewrite /psums /mklocalsums.
    do 2!rewrite nth_mkseq //=.
    have : (0 <> i) by smt(). move=> -> /=.
    have : (0 <> advid) by smt(). move=> -> /=.
    do 2!rewrite big_mapT.
    rewrite /(\o) /idfun /=.
    have : N = N-0 by smt(). move=> ->; do 2!rewrite -/(range 0 N).
    by apply eq_big_int=> j hj /= /#.
  + rewrite /psums /mklocalsums.
    rewrite nth_mkseq //= 1:/#.
    rewrite nth_mkseq //=.
    have : (1 <> i) by smt(). move=> -> /=.
    have : (1 <> advid) by smt(). move=> -> /=.
    do 2!rewrite big_mapT.
    rewrite /(\o) /idfun /=.
    have : N = N-0 by smt(). move=> ->; do 2!rewrite -/(range 0 N).
    by apply eq_big_int=> j hj /= /#.
qed.

(* -------------------------------------------------------------------- *)
local lemma pi1_spec sx :
  hoare [ E.pi1 :
      sx = s /\ 0 <= E.advid < N
      ==>
      (forall i j,
        0 <= i < N =>
        0 <= j < N =>
        i <> E.advid =>
        i <> j =>
        E.initadvshares.[i].[j] = E.psharesbeforefix.[i].[E.advid].[j])
   /\ reqs_integr E.advid E.rx
   /\ reqs_pshares_compat E.advid E.rx E.psharesbeforefix
   /\ valid_bx E.advid N E.bx
   /\ reqs_bcast_compat E.advid E.rx E.bx E.psharesbeforefix
   /\ fst res = fix E.advid E.psharesbeforefix E.bx
   /\ pshares_integr_full E.advid (fst res)
   /\ repss_correct E.advid sx (fst res)
   /\ snd res = mklocalsums E.advid (fst res) ].
proof.
proc=> /=.
inline Environment(A).computation.
wp; call(_ : true); wp.
conseq (_ : _ ==>
      (forall i j,
        0 <= i < N =>
        0 <= j < N =>
        i <> E.advid =>
        i <> j =>
        E.initadvshares.[i].[j] = E.psharesbeforefix.[i].[E.advid].[j])
   /\ reqs_integr_aux E.advid N N E.rx
   /\ reqs_pshares_compat E.advid E.rx E.psharesbeforefix
   /\ valid_bx E.advid N E.bx
   /\ reqs_bcast_compat E.advid E.rx E.bx E.psharesbeforefix
   /\ rinp = fix E.advid E.psharesbeforefix E.bx
   /\ pshares_integr_full E.advid rinp
   /\ repss_correct E.advid sx rinp
);
first by smt().
inline Environment(A).input.
sp; wp; call(_ : true) => /=.
conseq (_ : _ ==>
    0 <= E.advid < N
 /\ E.psharesbeforefix = E.pshares
 /\ (forall i j,
      0 <= i < N =>
      0 <= j < N =>
      i <> E.advid =>
      i <> j =>
      E.initadvshares.[i].[j] = E.psharesbeforefix.[i].[E.advid].[j])
 /\ repss_integr E.advid shares
 /\ E.pshares = distribute_shares shares
 /\ reqs_integr_aux E.advid N N E.rx
 /\ reqs_pshares_compat E.advid E.rx E.pshares
 /\ valid_bx E.advid N E.bx
 /\ reqs_bcast_compat E.advid E.rx E.bx E.pshares
 /\ fix E.advid E.pshares E.bx = fix E.advid E.psharesbeforefix E.bx
 /\ repss_correct E.advid sx shares);
first by smt(fix_integr_full).
seq 7 :
    (0 <= E.advid < N
 /\ E.psharesbeforefix = E.pshares
 /\ (forall i j,
      0 <= i < N =>
      0 <= j < N =>
      i <> E.advid =>
      i <> j =>
      E.initadvshares.[i].[j] = E.pshares.[i].[E.advid].[j])
 /\ valid_rx E.rx
 /\ repss_integr E.advid shares
 /\ E.pshares = distribute_shares shares
 /\ reqs_integr_aux E.advid N N E.rx
 /\ reqs_pshares_compat E.advid E.rx E.pshares
 /\ repss_correct E.advid sx shares);
last by exists* E.rx; elim*=> rx; call (broadcast_shares_integr rx).
call(_ : true).
seq 5 :
    (0 <= E.advid < N
 /\ E.psharesbeforefix = E.pshares
 /\ (forall i j,
      0 <= i < N =>
      0 <= j < N =>
      i <> E.advid =>
      i <> j =>
      E.initadvshares.[i].[j] = E.pshares.[i].[E.advid].[j])
 /\ repss_integr E.advid shares
 /\ E.pshares = distribute_shares shares
 /\ repss_correct E.advid sx shares);
last by exists* shares; elim*=> shares; call (verify_shares_integr shares); auto; smt().
call(_ : true).
wp.
exists* E.advid; elim*=> advid.
by call(do_sharing_integr advid sx); auto; smt(size_mkseq nth_mkseq).
qed.

(* -------------------------------------------------------------------- *)
(* Final messages the honest parties send in the output phase *)
op finalmsg (advid : int) (y : zmod) (pviewadv : zmod list) : zmod matrix =
  mkseq (fun i =>
    mkseq (fun j =>
      if i = advid then witness
      else if i = j then witness
      else if j = advid then y - sum (drop_elem advid pviewadv)
      else pviewadv.[j]) N) N.

(* -------------------------------------------------------------------- *)
(* Auxiliary lemma for the protocol correctness and output simulation *)
local lemma correctness_outsim_aux sx :
  4 <= N =>
  hoare [ E.protocol :
     sx = s /\ size s = N /\
     0 <= E.advid < N ==>
     (forall id,
       0 <= id < N /\ id <> E.advid =>
       let sx' = mkseq (fun i => if i <> E.advid then sx.[i] else sum E.advinpsx) N in
       res.[id] = idealfct sx')
  /\ (forall id, 0 <= id < N /\ id <> E.advid => res.[id] = E.y)
  /\ (finalmsg E.advid E.y E.advresshares = E.comp) ].
proof.
move=> hn4.
proc.
seq 1 :
      (0 <= E.advid < N
   /\ (forall i j,
        0 <= i < N =>
        0 <= j < N =>
        i <> E.advid =>
        i <> j =>
        E.initadvshares.[i].[j] = E.psharesbeforefix.[i].[E.advid].[j])
   /\ reqs_integr E.advid E.rx
   /\ reqs_pshares_compat E.advid E.rx E.psharesbeforefix
   /\ valid_bx E.advid N E.bx
   /\ reqs_bcast_compat E.advid E.rx E.bx E.psharesbeforefix
   /\ inp = fix E.advid E.psharesbeforefix E.bx
   /\ pshares_integr_full E.advid inp
   /\ repss_correct E.advid sx inp
   /\ E.comp = mklocalsums E.advid inp);
first by call (pi1_spec sx).
wp. inline Environment(A).output.
wp; call(_ : true); wp; call(_ : true); wp; skip.
move=> &1 [hadvid [Hinitadv [Hrixx [Hri [Hb [Hrb [Einp [Hfi [Hmx ->>]]]]]]]]].
pose advinp := extract_advinpsx (getAdvpView_sends Environment.advid{1} inp{1}).
pose psums := mklocalsums E.advid{1} inp{1}.
have Hpsums : psums_integr E.advid{1} psums
  by apply mklocalsums_integr.
move=> advc advres output y.
pose presshares := (distribute_resshares Environment.advid{1} advc psums).
pose sx' := mkseq (fun i => if i <> E.advid{1} then sx.[i] else sum advinp) N.
have H :
  forall id, 0 <= id < N /\ id <> E.advid{1} => output.[id] = sum sx'.
+ move=> id [hid idnadvid].
  by apply (output_spec_aux E.advid{1} advc advres sx' inp{1})=> //; smt(size_mkseq nth_mkseq).
split; first by [].
have H0 : forall id, 0 <= id < N /\ id <> E.advid{1} => output.[id] = y.
+ move=> id [hid idnadvid].
  rewrite /y (majority_all_except_one' _ output.[id] E.advid{1}) //; 1,2:smt(size_mkseq).
  move=> j hj jnadvid.
  by do 2!(rewrite H; 1:smt(size_mkseq)).
split; first by [].
have Ey : y = sum sx'.
+ pose x := if E.advid{1} = 0 then 1 else 0.
  by rewrite -(H0 x) /#.
rewrite /mklocalsums /finalmsg /=.
apply eq_in_mkseq=> i hi /=.
apply eq_in_mkseq=> j hj /=.
case (i = E.advid{1})=> [// | inadvid].
case (i = j)=> [// | hij].
case (j = E.advid{1})=> [->> | jnadvid]; last first.
+ rewrite nth_mkseq //=.
  have : E.advid{1} <> j by smt().
  move=> -> /=.
  do 2!rewrite big_mapT.
  have : N = N-0 by smt().
  move=> ->; rewrite -/(range 0 N).
  apply eq_big_int=> k hk /=.
  rewrite /(\o) /idfun /=.
  case (k = E.advid{1})=> [->> /= | knadvid /=]; last by smt().
  case (E.rx{1}.[E.advid{1}].[j])=> [c | nc];
  first by smt(nth_mkseq).
  rewrite /pshares_integr_full in Hfi.
  rewrite Einp.
  rewrite nth_mkseq //=.
  rewrite nth_mkseq //=.
  rewrite nth_mkseq //=.
  rewrite inadvid hij /=.
  pose x := choiceb (fun i => 0 <= i < N /\ i <> E.advid{1} /\ i <> j) 0.
  have Htmp : exists z, (fun i => 0 <= i < N /\ i <> E.advid{1} /\ i <> j) z.
  - by exists (if E.advid{1} <= 1 then (if j <= 2 then 3 else 2)
          else (if j = 0 then 1 else 0)); smt().
  apply (choicebP _ 0) in Htmp.
  apply (eq_trans _ E.psharesbeforefix{1}.[i].[Environment.advid{1}].[j] _);
  smt(size_mkseq nth_mkseq).
apply eq_sym.
rewrite -(subr0 (sum (col E.advid{1} inp{1}.[i]))).
apply eq_sym.
rewrite eqr_sub addr0.
rewrite addrC.
rewrite sum_drop_elem_plus; 1:smt(size_mkseq).
rewrite size_mkseq max_ler; 1:smt().
pose m :=
      mkseq (fun k =>
      mkseq (fun l =>
        if l = E.advid{1} then inp{1}.[i].[k].[E.advid{1}]
        else
          if k <> E.advid{1} then inp{1}.[E.advid{1}].[k].[l] else
          if E.rx{1}.[E.advid{1}].[l] then oget E.bx{1}.[E.advid{1}].[l]
          else
            let x = if E.advid{1} <= 1 then
             (if l <= 2 then 3 else 2)
             else (if l = 0 then 1 else 0) in
            E.initadvshares{1}.[x].[l])
        N) N.
have Hm : square N m by smt(size_mkseq nth_mkseq).
pose z := sum (mkseq (fun j => sum (mkseq (fun i => m.[i].[j]) N)) N).
apply (eq_trans _ z _); last first.
+ rewrite /z.
  do 3!rewrite big_mapT.
  have : N = N-0 by smt().
  move=> ->; rewrite -/(range 0 N).
  apply eq_big_int=> k hk /=.
  rewrite /(\o) /idfun /=.
  case (k = E.advid{1})=> [->> /= | knadvid /=].
  - rewrite big_mapT -/(range 0 N).
    apply eq_big_int=> l hl /=.
    by rewrite /(\o) /idfun /=; smt(nth_mkseq).
  - rewrite nth_mkseq //=.
    have : E.advid{1} <> k by smt().
    move=> -> /=.
    do 2!rewrite big_mapT -/(range 0 N).
    apply eq_big_int=> l hl /=.
    pose x := choiceb (fun i => 0 <= i < N /\ i <> E.advid{1} /\ i <> k) 0.
    have Htmp : exists z, (fun i => 0 <= i < N /\ i <> E.advid{1} /\ i <> k) z.
    - by exists (if E.advid{1} <= 1 then (if k <= 2 then 3 else 2)
            else (if k = 0 then 1 else 0)); smt().
    apply (choicebP _ 0) in Htmp.
    by rewrite /(\o) /idfun /=; smt(size_mkseq nth_mkseq).
rewrite -(matrix_sum_commutativity N m) //.
rewrite Ey.
rewrite big_mapT.
apply eq_sym; do 2!rewrite big_mapT; apply eq_sym.
rewrite -/(range 0 N).
apply eq_big_int=> k hk /=.
rewrite /(\o) /idfun /=.
case (k = E.advid{1})=> [->> /= | knadvid /=].
+ do 2!rewrite big_mapT.
  have : N = N-0 by smt().
  move=> ->; rewrite -/(range 0 N).
  apply eq_big_int=> l hl /=.
  rewrite /(\o) /idfun /=.
  case(l = E.advid{1})=> [->> | lnadvid];
  first by smt(getAdvpView_sends_majority).
  case(E.rx{1}.[E.advid{1}].[l])=> [c | nc].
  - congr.
    rewrite /reqs_bcast_compat /reqs_bcast_compat0 /reqs_bcast_compat1 in Hrb.
    pose x := if E.advid{1} <= 1 then
              (if l <= 2 then 3 else 2)
              else (if l = 0 then 1 else 0).
    have : E.bx{1}.[E.advid{1}].[l] = Some inp{1}.[x].[E.advid{1}].[l] by smt(size_mkseq nth_mkseq).
    move=> ->.
    smt(getAdvpView_sends_majority size_mkseq nth_mkseq).
  - rewrite /reqs_bcast_compat /reqs_bcast_compat0 /reqs_bcast_compat1 in Hrb.
    pose x := if E.advid{1} <= 1 then
                                if l <= 2 then 3 else 2
                              else if l = 0 then 1 else 0.
    have Htmp := getAdvpView_sends_majority E.advid{1} inp{1} hn4 hadvid Hfi.
    rewrite (Htmp x l) //= 1,2,3:/# oget_some.
    smt(size_mkseq nth_mkseq).
+ rewrite -Hmx //.
  rewrite -(mkseq_nth witness inp{1}.[k].[k]).
  have : size inp{1}.[k].[k] = N by smt(size_mkseq nth_mkseq).
  move=> ->.
  do 2!rewrite big_mapT.
  have : N = N-0 by smt().
  move=> ->; rewrite -/(range 0 N).
  apply eq_big_int=> l hl /=.
  rewrite /(\o) /idfun /=.
  smt(size_mkseq nth_mkseq).
qed.

(* -------------------------------------------------------------------- *)
(* Correctness of the protocol with respect to the input
   that the adversary is commited to. *)
local lemma correctness sx : 4 <= N =>
  hoare [ E.protocol :
    sx = s /\ size s = N /\
    0 <= E.advid < N ==>
    let sx' = mkseq (fun i => if i <> E.advid then sx.[i] else sum E.advinpsx) N in
    forall id,
      0 <= id < N /\ id <> E.advid =>
      res.[id] = idealfct sx' ].
proof. move=> hn4. by conseq (correctness_outsim_aux sx hn4); smt(). qed.

(* -------------------------------------------------------------------- *)
(* The output simulation property of the protocol. 
   The adversary learns no more information than the result of the computation. *)
local lemma output_simulation : 4 <= N =>
  hoare [ E.protocol :
    size s = N /\
    0 <= E.advid < N ==>
    finalmsg E.advid E.y E.advresshares = E.comp ].
proof.
move=> hn4.
exists* s; elim*=> sx.
by conseq (correctness_outsim_aux sx hn4); smt().
qed.

(* -------------------------------------------------------------------- *)
(* Privacy of the input phase (i.e. the replicated secret sharing and
   the consistency check/verify) *)
local lemma privacy_input_phase : equiv [ E.input ~ E.input :
      ={glob A, E.advid}
   /\ 0 <= E.advid{1} < N
   /\ s{1}.[E.advid{1}] = s{2}.[E.advid{2}]
      ==>
      ={glob A} ].
proof.
exists* E.advid{1}; elim*=> advid.
proc; wp.
call (_ : true) => //.
conseq (_ : _ ==> ={glob A, E.bx})=> //.
seq 1 1 :
  (   ={glob A, E.advid}
   /\ 0 <= E.advid{1} < N
   /\ repss_private E.advid{1} shares{1} shares{2}
   /\ repss_integr E.advid{1} shares{1}
   /\ repss_integr E.advid{1} shares{2});
first by call do_sharing_private=> //.
exists* shares{1}; elim*=> shares1.
exists* shares{2}; elim*=> shares2.
sp.
call (broadcast_shares_private shares1 shares2).
call (_ : true).
conseq
(_ :
     shares1 = shares{1}
  /\ shares2 = shares{2}
  /\ E.pshares{1} = distribute_shares shares1
  /\ E.pshares{2} = distribute_shares shares2
  /\ ={glob A, E.advid}
  /\ 0 <= E.advid{1} < N
  /\ repss_integr E.advid{1} shares{1}
  /\ repss_integr E.advid{1} shares{2}
  /\ repss_private E.advid{1} shares{1} shares{2}
  ==>
     shares1 = shares{1}
  /\ shares2 = shares{2}
  /\ E.pshares{1} = distribute_shares shares1
  /\ E.pshares{2} = distribute_shares shares2
  /\ ={glob A, E.advid, E.rx}
  /\ 0 <= E.advid{1} < N
  /\ repss_integr E.advid{1} shares{1}
  /\ repss_integr E.advid{1} shares{2}
  /\ repss_private E.advid{1} shares{1} shares{2}
)
(_ :
     0 <= E.advid < N
  /\ E.pshares = distribute_shares shares1
  /\ repss_integr E.advid shares1
  ==>
     reqs_integr E.advid E.rx
  /\ reqs_pshares_compat E.advid E.rx E.pshares
)
(_ :
     0 <= E.advid < N
  /\ E.pshares = distribute_shares shares2
  /\ repss_integr E.advid shares2
  ==>
     reqs_integr E.advid E.rx
  /\ reqs_pshares_compat E.advid E.rx E.pshares
) => //.
by call (verify_shares_integr shares1); call (_ : true)=> //.
by call (verify_shares_integr shares2); call (_ : true)=> //.
call (verify_shares_private shares1 shares2).
call (_ : true); auto=> &1 &2 |>.
progress.
do 2!(rewrite nth_mkseq /= 1:/#).
by apply eq_in_mkseq=> /= i hi; smt(eq_from_nth).
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
seq 1 1 : (={glob A}); first by call privacy_input_phase.
inline*; wp; sp; by call (_ : true).
qed.

end section S.
