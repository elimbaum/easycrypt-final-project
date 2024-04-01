(* -------------------------------------------------------------------- *)
require import AllCore.
require import List Bool IntDiv.
require import Number StdOrder Distr.
(*---*) import RealOrder. 

require ZModP. clone import ZModP as Zp.

import Zp.Sub.
import Zp.ZModule.
import Zp.ZModpRing.

(* -------------------------------------------------------------------- *)
clone FinType as ZModFinType with
  type t <- zmod,
  op   enum = map inzmod (range 0 p)
  proof *.

realize enum_spec.
proof.
move=> z; rewrite count_uniq_mem.
- apply/map_inj_in_uniq=> [x y|]; last by apply/range_uniq.
  move=> /mem_range lep_x /mem_range lep_y  /(congr1 asint).
  by rewrite !inzmodK !pmod_small.
rewrite b2i_eq1; apply/mapP; exists (asint z); split.
+ by apply/mem_range/Sub.valP.
+ by rewrite /inzmod pmod_small ?Sub.valP valKd.
qed.

lemma size_zmodfin : size (ZModFinType.enum) = p.
proof. rewrite /enum size_map size_range /= [smt(Zp.le2_p)]. qed.

(* -------------------------------------------------------------------- *)
clone import MFinite as MZModFinite with
  type   t <- zmod,
  theory Support <- ZModFinType.
