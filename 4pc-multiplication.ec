prover quorum=2 ["Alt-Ergo" "Z3"].
timeout 2.  (* limit SMT solvers to two seconds *)
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

module F4 = {
  var x : matrix
  (* init constant? this should be 4 *)
  var n : int

  (* p has a value x and wants to share it with all other parties *)
  proc share(x : int, p : party) : matrix = {
    var s0, s1, s2, s3 : int;

    var shares : int list;
    shares <- [];

    (* generate 3 random *)
    s0 <$ randint;
    shares <- shares ++ [s0];

    s1 <$ randint;
    shares <- shares ++ [s1];

    s2 <$ randint;
    shares <- shares ++ [s2];

    s3 <- x - s0 - s1 - s2;
    shares <- shares ++ [s3];

    (* TODO: think about if we should use vector here instead of list *)
    (* TODO: basically every `offunm` call is going to have the structure
        if p = s then 0 else ...
       maybe we can factor that out?
     *)
    return offunm ((fun p s =>
        if p = s then 0 else (nth 0 shares s)), n, n);
  }

  (* parties si and sj know x, and want to send it to party d.
     todo: cheating identification (vs just abort)
   *)
  proc jmp(x : int, si sj : party, d : party) : matrix = {
    (* TODO: party d gets x from si, and H(x) from sj *)
    (* abort if hashes don't check out *)
    var g : party;
    (* TODO: this should be the excluded party *)
    g <- 3;
    return offunm ((fun p s =>
        if p = s then 0 else
        if g = s then x else 0), n, n);
  }

  (* parties i and j know x, and want to share it with the two other
     parties.
   *)
  proc inp(x : int, i j : party) : matrix = {
    var r : int;
    var g, h : party;

    (* in the paper this is a PRF, but for now model as RO *)
    r <$ randint;

    g <- 0; h <- 1;

    (* need to derive g, h *)
    return offunm ((fun p s =>
        (* zero on the diagonal, and also shares xi, xj *)
        if p = s \/ p = i \/ p = j then 0 else
        if p = g then r
        else (* p = h *) x - r), n, n);
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

    return m01 + m02 + m03 + m12 + m13 + m23 + mlocal;   
  }

  proc open(m : matrix) : int = {
    (* consistency check? or precondition? *)
    (* add up party 0 shares, then add P1's x0... make this nicer? *)
    return m.[0, 1] + m.[0, 2] + m.[0, 3] + m.[1, 0];
  }

  proc correct() : bool = {
    var x, y, z : int;
    var mx, my, mz : matrix;

    x <$ randint;
    y <$ randint;

    (* assume P1 holds x and P2 holds y *)
    mx <@ share(x, 1);
    my <@ share(y, 2);

    mz <@ mult(mx, my);

    z <@ open(mz);

    return z = x * y;
    
  }
}.

lemma mul_correct(x y : int) :
    hoare[F4.correct : ].
proof.

qed.

