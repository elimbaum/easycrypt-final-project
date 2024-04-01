(* -------------------------------------------------------------------- *)
require import Core Int IntExtra List.

pragma -oldip.

(* -------------------------------------------------------------------- *)
lemma eq_map_mkseq (x0 : 'a) (f : 'a -> 'b) (l : 'a list) n :
  size l = n =>
  map f l = mkseq (fun i => f (nth x0 l i)) n.
proof.
move=><-.
rewrite -(mkseq_nth witness (map f l)) size_map.
by apply eq_in_mkseq; smt(nth_map).
qed.

lemma map_mkseq (f : 'a -> 'b) g n :
  0 <= n => map f (mkseq g n) = mkseq (f \o g) n.
proof.
move=> Hn.
rewrite (eq_map_mkseq witness _ _ n); first by smt(size_mkseq).
by apply eq_in_mkseq; smt(nth_mkseq).
qed.

lemma zip_mkseq (f : int ->'a) (g : int -> 'b) n :
  zip (mkseq f n) (mkseq g n) = mkseq (fun i => (f i, g i)) n.
proof.
apply (eq_from_nth (witness,witness)); 1:smt(size_zip size_mkseq).
move=> i hi.
rewrite nth_zip; 1:smt(size_mkseq).
by do 3!(rewrite nth_mkseq; 1:smt(size_zip size_mkseq)).
qed.

(* -------------------------------------------------------------------- *)
op curry   (f : 'a  * 'b -> 'c) x y = f (x,y).
op uncurry (f : 'a -> 'b -> 'c) p   = f (fst p) (snd p).

lemma uncurry_curry (f : ('a * 'b) -> 'c) : uncurry (curry f) = f.
proof. by apply/fun_ext; move => []. qed.

lemma curry_uncurry (f: 'a -> 'b -> 'c) : curry (uncurry f) = f.
proof. by rewrite /uncurry /curry. qed.

(* -------------------------------------------------------------------- *)
op map2 (f : 'a -> 'b -> 'c) k l = map (uncurry f) (zip k l).

lemma size_map2 (f : 'a -> 'b -> 'c) k l :
  size k = size l => size (map2 f k l) = size k.
proof. smt(size_map size_zip). qed.

lemma map2_mkseq (a0 : 'a) (b0 : 'b) (f: 'a -> 'b -> 'c) (l1 : 'a list) (l2 : 'b list) n :
  size l1 = n =>
  size l2 = n =>
  map2 f l1 l2 = mkseq (fun i => f (nth a0 l1 i) (nth b0 l2 i)) n.
proof.
move => H1 H2. rewrite /map2.
rewrite (eq_map_mkseq (a0,b0) _ _ n); 1:smt(size_zip).
apply eq_in_mkseq=> i hi /=.
by rewrite nth_zip; 1:smt(size_mkseq).
qed.

(* -------------------------------------------------------------------- *)
op drop_elem n (l : 'a list) = take n l ++ drop (n + 1) l.

(* -------------------------------------------------------------------- *)
lemma drop_elem0 n (l : 'a list) :
  n < 0 => drop_elem n l = l.
proof. case l => [// | H x l]; smt(). qed.

lemma drop_elem_oversize n (l : 'a list) :
  size l <= n => drop_elem n l = l.
proof. smt(take_oversize drop_oversize cats0). qed.

lemma size_drop_elem n (l : 'a list) :
  0 <= n < size l =>
  size (drop_elem n l) = max 0 (size l - 1).
proof. smt(size_cat size_take size_drop). qed.

lemma list_decomp x0 n (l : 'a list) :
  0 <= n < size l => l = take n l ++ nth x0 l n :: drop (n + 1) l.
proof. by move=> hn; rewrite -drop_nth // cat_take_drop. qed.

lemma count_drop_elem x0 n p (l : 'a list) : 0 <= n < size l =>
  count p (drop_elem n l) = count p l - b2i (p (nth x0 l n)).
proof. smt(count_cat cat_take_drop drop_nth). qed.

lemma count_drop_elem_1 x0 n p (l : 'a list) : 0 <= n < size l =>
  count p l = count p (drop_elem n l) + b2i (p (nth x0 l n)).
proof. by move=> h; rewrite (count_drop_elem x0 _ _ _ h); smt(). qed.

(* -------------------------------------------------------------------- *)
lemma all_pred1 x0 (l : 'a list) :
  (forall i j, nth x0 l i = nth x0 l j) => exists v, all (pred1 v) l.
proof.
move=> eqh; exists (nth x0 l 0); apply/(all_nthP _ _ x0).
by move=> i _; apply/eqh.
qed.

lemma all_pred1_eq ['a] (x0 : 'a) s v :
  all (pred1 v) s => forall i j,
    0 <= i < size s => 0 <= j < size s => nth x0 s i = nth x0 s j.
proof.
by move/all_nthP/(_ x0)=> @/pred1 eq i j lti ltj; rewrite !eq.
qed.

(* -------------------------------------------------------------------- *)
lemma all_mkseq p n (f : int -> 'a) :
  (forall i, 0 <= i < n => p (f i)) => all p (mkseq f n).
proof. by move=> pf; apply/allP=> x /mkseqP[i [lti ->]]; apply/pf. qed.

lemma size_take_le ['a] n (s : 'a list) : 0 <= n => size (take n s) <= n.
proof. by move=> ge0_n; rewrite size_take // -/(min _ _) /#. qed.

lemma mem_take ['a] (x0 : 'a) n s x :
  x \in take n s => exists i, 0 <= i < n /\ x = nth x0 s i.
proof.
case: (0 <= n) => [ge0_n|/ltzNge /ltzW /take_le0<:'a> ->//].
move=> ^ /nth_index /(_ x0); (pose i := (index _ _)) => {-1}<-.
rewrite -index_mem; have := size_take_le n s ge0_n => le1 le2.
have {le1 le2} lt_in: i < n by smt(). exists i.
by rewrite index_ge0 nth_take.
qed.

lemma all_take ['a] (x0 : 'a) p n (s : 'a list) :
  (forall i, 0 <= i < n => p (nth x0 s i)) => all p (take n s).
proof.
by move=> hp; apply/allP => x /(mem_take x0) [i [hi ->]]; apply: hp.
qed.

lemma mem_drop ['a] (x0 : 'a) n (s : 'a list) x :
  x \in drop n s => exists i, n <= i < size s /\ x = nth x0 s i.
proof.
case: (n <= 0) => [^le0_n|/ltzNge /ltzW ge0_n].
+ move/drop_le0<:'a> => -> ^x_in_s /nth_index/(_ x0) => <-.
  exists (index x s); rewrite index_mem x_in_s /=.
  by apply/(lez_trans 0)/index_ge0.
case: (n < size s) => [lt_n_s|/lezNgt ^le0_n /drop_oversize ->//].
move=> ^ /nth_index /(_ x0); (pose i := (index _ _)) => {-1}<-.
rewrite -index_mem; rewrite size_drop // /max subz_gt0 lt_n_s /=.
move=> lt; exists (n + i); rewrite lez_addl index_ge0 /=.
by rewrite nth_drop // ?index_ge0 /#.
qed.

lemma all_drop x0 p (n : int) (l : 'a list) :
  (forall i, n <= i < size l => p (nth x0 l i)) => all p (drop n l).
proof.
by move => hp; apply /allP => x /(mem_drop x0) [i [hi ->]]; apply: hp.
qed.

lemma drop_elem_in x0 n (l : 'a list) x :
  x \in drop_elem n l =>
    exists i, (0 <= i < n \/ n+1 <= i < size l) /\ x = nth x0 l i.
proof. smt(mem_cat mem_take mem_drop). qed.

lemma drop_elem_in' x0 n (l : 'a list) x : 0 <= n < size l =>
  x \in drop_elem n l =>
    exists i, (0 <= i < size l /\ i <> n) /\ x = nth x0 l i.
proof. by move=> hn /(drop_elem_in x0); smt(). qed.

lemma all_drop_elem x0 p (n : int) (l : 'a list) :
  (forall i, 0 <= i < n \/ n+1 <= i < size l => p (nth x0 l i)) =>
    all p (drop_elem n l).
proof. smt(all_cat all_take all_drop). qed.

lemma all_drop_elem' x0 p (n : int) (l : 'a list) : 0 <= n < size l =>
  (forall i, 0 <= i < size l => i <> n => p (nth x0 l i)) => all p (drop_elem n l).
proof. by move=> hn H; apply (all_drop_elem x0); smt(). qed.

lemma nth_drop_elem x0 n (l : 'a list) i : 0 <= n =>
  nth x0 (drop_elem n l) i = if i < n then nth x0 l i else nth x0 l (i+1).
proof.
move=> ge0_n; rewrite nth_cat size_take //.
by smt(nth_default nth_take nth_drop).
qed.

lemma drop_elem_eq x0 k (l1 l2 : 'a list) :
    size l1 = size l2 =>
    0 <= k < size l1 =>
    (forall i, 0 <= i < size l1 => i <> k => nth x0 l1 i = nth x0 l2 i) =>
    drop_elem k l1 = drop_elem k l2.
proof.
move=> hsize hk H.
apply (eq_from_nth x0);
smt(nth_cat size_cat nth_take size_take nth_drop size_drop).
qed.
