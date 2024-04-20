require import Core List Int IntExtra IntDiv.
require import Util.

lemma count_predU p q l :
  count<:'a> (predU p q) l = count p l + count q l - count (predI p q) l.
proof.
elim: l => [// | x l /= ->].
ringeq.
by rewrite /predU /predI /b2i; case (p x); case (q x).
qed.

(* -------------------------------------------------------------------- *)
op B t (l : 'a list) x = t < count (pred1 x) l.

pred majority_vote (f : 'a list -> 'a option) =
  forall l v, f l = Some v <=> B (size l %/ 2) l v.

(* -------------------------------------------------------------------- *)
(* Majority vote: takes the first element that occurs more than the treshold t *)

op majority_bound (l : 'a list) (t : int) : 'a option =
  ohead (filter (B t l) l).

lemma B_cons v (l : 'a list) t :
  ! B t (v :: l) v => B t (v :: l) = B t l.
proof. move=> H; apply/fun_ext => x; smt(). qed.

lemma majority_cons v l t :
  majority_bound<:'a> (v :: l) t = if B t (v :: l) v then Some v else majority_bound l t.
proof.
rewrite {1}/majority_bound.
rewrite filter_cons.
case (B t (v :: l) v) => [// | H /=].
rewrite B_cons //=.
qed.

lemma majority_spec_1 l t v :
  majority_bound<:'a> l t = Some v => v \in l /\ B t l v.
proof.
elim: l => [// | x l H].
rewrite majority_cons.
by case (B t (x :: l) x)=> [// | nb]; smt().
qed.

lemma majority_spec_2 (l : 'a list) t v :
  v \in l => t < count (pred1 v) l => exists x, majority_bound<:'a> l t = Some x.
proof.
move: v.
elim: l => [// | x l H v H1 H2].
case (v = x)=> [<- | ne]; first by smt().
case (B t (x :: l) x) => [| nb]; first by smt().
by rewrite majority_cons nb /=; smt().
qed.

op majority = fun (l : 'a list) => majority_bound l (size l %/ 2).

lemma majority_spec : majority_vote<:'a> majority.
proof.
move=> l v.
split=> [| Hszv]; first by smt(majority_spec_1).
have Hvl : v \in l by smt(size_ge0 has_count hasP edivzP).
elim (majority_spec_2 _ _ _ Hvl Hszv) => x Hx {Hvl}.
case (v = x) => [-> // | ne].
move: (majority_spec_1 _ _ _ Hx) => [Hxl Hszx] {Hx Hxl}.
have Hi : predI (pred1 v) (pred1 x) = pred0 by apply/fun_ext; smt().
have Hc := count_predU (pred1 v) (pred1 x) l.
rewrite Hi count_pred0 /= in Hc => {Hi ne}.
by smt(count_size edivzP).
(* by smt(count_size ltz_pmod divz_eq).*)
qed.

lemma majority_all (l : 'a list) v :
  2 <= size l =>
  all (pred1 v) l =>
  majority l = Some v.
proof. by smt (majority_spec all_count edivzP). qed.

lemma majority_all' (l : 'a list) v :
  2 <= size l =>
  (forall j, 0 <= j < size l => nth witness l j = v) =>
  majority l = Some v.
proof.
move=> ??.
apply majority_all=> //.
by rewrite -(all_nthP _ _ witness).
qed.

(* If i is out of bound, this is majority all *)
lemma majority_all_except_one (l : 'a list) v i :
  3 <= size l =>
  all (pred1 v) (drop_elem i l)=>
  majority l = Some v.
proof.
have := count_drop_elem<:'a> witness.
smt.
(*   by smt(majority_spec all_count size_drop_elem edivzP majority_all).*)
qed.

lemma majority_all_except_one' (l : 'a list) v i :
  3 <= size l => (0 <= i < size l) => 
  (forall j, 0 <= j < size l => j<>i => nth witness l j = v) =>
  majority l = Some v.
proof.
progress.
apply (majority_all_except_one l v i) => //=. 
have := all_drop_elem<:'a> witness; smt().
qed.

(* -------------------------------------------------------------------- *)
op checkall = fun (l : 'a list) => majority_bound l (size l).
