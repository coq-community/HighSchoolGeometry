(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


Require Export alignement.
Set Implicit Arguments.
Unset Strict Implicit.
Parameter barycentre : PP -> PP -> PO.
 
Axiom
  add_PP_barycentre :
    forall (a b : R) (A B : PO),
    a + b <> 0 ->
    add_PP (cons a A) (cons b B) =
    cons (a + b) (barycentre (cons a A) (cons b B)).
 
Lemma permute_barycentre :
 forall (a b : R) (A B : PO),
 a + b <> 0 ->
 barycentre (cons a A) (cons b B) = barycentre (cons b B) (cons a A).
intros a b A B H; try assumption.
apply conversion_PP with (a := a + b) (b := b + a); try ring; auto.
repeat rewrite <- add_PP_barycentre; auto.
RingPP.
unfold not in |- *; intros H1; apply H; auto; rewrite <- H1; ring; auto.
Qed.
 
Lemma barycentre_zero :
 forall (a : R) (A B : PO), a <> 0 -> barycentre (cons a A) (cons 0 B) = A.
intros a A B H; try assumption.
apply conversion_PP with (a := a + 0) (b := a); try ring; auto.
repeat rewrite <- add_PP_barycentre; auto.
RingPP.
unfold not in |- *; intros H1; apply H; auto; rewrite <- H1; ring; auto.
replace (a + 0) with a; try ring; auto.
Qed.
 
Lemma bary_assoc :
 forall (a b c : R) (A B C : PO),
 a + b <> 0 ->
 b + c <> 0 ->
 a + (b + c) <> 0 ->
 barycentre (cons a A) (cons (b + c) (barycentre (cons b B) (cons c C))) =
 barycentre (cons (a + b) (barycentre (cons a A) (cons b B))) (cons c C).
intros a b c A B C H H0 H1; try assumption.
apply conversion_PP with (a := a + (b + c)) (b := a + b + c); try ring; auto.
repeat rewrite <- add_PP_barycentre; auto.
Ringvec.
unfold not in |- *; intros H2; apply H1; auto; rewrite <- H2; ring; auto.
Qed.
 
Lemma homogene_barycentre :
 forall (a b k : R) (A B : PO),
 a + b <> 0 ->
 k <> 0 ->
 barycentre (cons (k * a) A) (cons (k * b) B) =
 barycentre (cons a A) (cons b B).
intros a b k A B H H0; try assumption.
apply conversion_PP with (a := k * a + k * b) (b := k * (a + b)); try ring;
 auto.
repeat rewrite <- add_PP_barycentre; auto.
rewrite distrib_mult_cons.
rewrite <- def_mult_PP.
repeat rewrite <- add_PP_barycentre; auto.
replace (k * a + k * b) with (k * (a + b)); try ring.
auto with *.
replace (k * a + k * b) with (k * (a + b)); try ring.
auto with *.
Qed.
 
Lemma def_vecteur_bary :
 forall (a b : R) (A B G : PO),
 a + b <> 0 ->
 G = barycentre (cons a A) (cons b B) ->
 add_PP (mult_PP a (vec G A)) (mult_PP b (vec G B)) = zero.
intros.
cut (zero = mult_PP (a + b) (vec G G)); intros; auto.
rewrite H1.
apply add_PP_vecteur; auto.
rewrite (add_PP_barycentre (a:=a) (b:=b) A B); auto.
rewrite <- H0; auto.
Ringvec.
Qed.
 
Lemma def_vecteur_bary_rec :
 forall (a b : R) (A B G : PO),
 a + b <> 0 ->
 add_PP (mult_PP a (vec G A)) (mult_PP b (vec G B)) = zero ->
 G = barycentre (cons a A) (cons b B).
unfold vec in |- *; intros.
apply conversion_PP with (a := a + b) (b := a + b); auto.
rewrite <- (add_PP_barycentre (a:=a) (b:=b) A B); auto.
replace (cons (a + b) G) with (add_PP (cons (a + b) G) zero).
rewrite <- H0.
RingPP.
RingPP.
Qed.
 
Lemma prop_vecteur_bary :
 forall (a b : R) (A B G M : PO),
 a + b <> 0 ->
 G = barycentre (cons a A) (cons b B) ->
 add_PP (mult_PP a (vec M A)) (mult_PP b (vec M B)) =
 mult_PP (a + b) (vec M G).
intros.
apply add_PP_vecteur; auto.
rewrite (add_PP_barycentre (a:=a) (b:=b) A B); auto.
rewrite <- H0; auto.
Qed.
 
Lemma prop_vecteur_bary_rec :
 forall (a b : R) (A B G M : PO),
 a + b <> 0 ->
 add_PP (mult_PP a (vec M A)) (mult_PP b (vec M B)) =
 mult_PP (a + b) (vec M G) -> G = barycentre (cons a A) (cons b B).
unfold vec in |- *; intros.
apply conversion_PP with (a := a + b) (b := a + b); auto.
rewrite <- (add_PP_barycentre (a:=a) (b:=b) A B); auto.
cut
 (add_PP (cons (- (a + b)) M) (cons (a + b) G) =
  add_PP (mult_PP a (add_PP (cons (-1) M) (cons 1 A)))
    (mult_PP b (add_PP (cons (-1) M) (cons 1 B)))); 
 intros.
RingPP2 H1.
RingPP.
rewrite H0.
RingPP.
Qed.
Hint Resolve add_PP_barycentre: geo.
 
Lemma barycentre_alignes :
 forall (a b : R) (A B : PO),
 a + b <> 0 -> alignes A B (barycentre (cons a A) (cons b B)).
intros a b A B H; try assumption.
apply add_PP_alignes with (a := a) (b := b); auto with geo.
Qed.
 
Lemma colineaire_barycentre :
 forall (k : R) (A B C : PO),
 vec A C = mult_PP k (vec A B) ->
 C = barycentre (cons (1 + - k) A) (cons k B).
unfold vec in |- *; intros.
elim
 cons_inj
  with
    (a := 1)
    (b := 1 + - k + k)
    (A := C)
    (B := barycentre (cons (1 + - k) A) (cons k B)); 
 intros; auto with *.
repeat rewrite <- add_PP_barycentre; auto.
RingPP2 H.
RingPP.
replace (1 + - k + k) with 1; try ring; auto with *.
Qed.
 
Lemma alignes_barycentre :
 forall A B C : PO,
 A <> B ->
 alignes A B C -> exists k : R, C = barycentre (cons k A) (cons (1 + - k) B).
unfold alignes, alignes1 in |- *; intros.
elim H0;
 [ intros H1; tauto
 | intros H1; elim H1; [ intros k H2; try clear H1 H0; try exact H2 ] ].
exists k; auto.
apply conversion_PP with (a := 1) (b := k + (1 + - k)); try ring; auto with *.
rewrite H2; auto.
repeat rewrite <- add_PP_barycentre; auto.
replace (k + (1 + - k)) with 1; try ring; auto with *.
Qed.
Hint Resolve barycentre_alignes prop_vecteur_bary def_vecteur_bary_rec
  def_vecteur_bary homogene_barycentre barycentre_zero: geo.
 
Lemma existence_representant_vecteur :
 forall A B C : PO, ex (fun D : PO => vec A D = vec B C :>PP).
unfold vec in |- *; intros.
exists (barycentre (cons (-1) B) (cons 2 (barycentre (cons 1 A) (cons 1 C)))).
pattern 1 at 2 in |- *.
RReplace 1 (-1 + 2).
repeat rewrite <- add_PP_barycentre; auto.
RingPP.
discrR.
discrR.
Qed.
 
Lemma existence_representant_mult_vecteur :
 forall (A B C : PO) (k : R),
 ex (fun D : PO => vec A D = mult_PP k (vec B C) :>PP).
intros.
elim (classic (k = -1)); intros.
rewrite H.
elim existence_representant_vecteur with (A := A) (B := C) (C := B);
 intros D H0; try clear existence_representant_vecteur; 
 try exact H0.
exists D.
rewrite H0; Ringvec.
unfold vec in |- *.
exists
 (barycentre (cons (- k) B) (cons (1 + k) (barycentre (cons 1 A) (cons k C)))).
pattern 1 at 2 in |- *.
RReplace 1 (- k + (1 + k)).
repeat rewrite <- add_PP_barycentre; auto.
RingPP.
unfold not in |- *; intros; apply H.
RReplace k (1 + k + -1).
rewrite H0.
ring.
RReplace (- k + (1 + k)) 1.
auto with *.
Qed.
 
Lemma existence_representant_som_vecteur :
 forall A B C D : PO,
 ex (fun E : PO => vec A E = add_PP (vec A B) (vec C D) :>PP).
intros.
unfold vec in |- *.
exists (barycentre (cons (-1) C) (cons 2 (barycentre (cons 1 B) (cons 1 D)))).
pattern 1 at 2 in |- *.
RReplace 1 (-1 + 2).
repeat rewrite <- add_PP_barycentre; auto.
RingPP.
discrR.
RReplace (-1 + 2) 1.
discrR.
Qed.
 
Lemma existence_representant_comb_lin_vecteur :
 forall (A B C D : PO) (a b : R),
 ex
   (fun E : PO =>
    vec A E = add_PP (mult_PP a (vec A B)) (mult_PP b (vec C D)) :>PP).
intros.
elim
 existence_representant_mult_vecteur with (A := A) (B := A) (C := B) (k := a);
 intros B' H; try clear existence_representant_mult_vecteur; 
 rewrite <- H.
elim
 existence_representant_mult_vecteur with (A := C) (B := C) (C := D) (k := b);
 intros C' H0; try clear existence_representant_mult_vecteur; 
 rewrite <- H0.
elim
 existence_representant_som_vecteur
  with (A := A) (B := B') (C := C) (D := C'); intros E H1;
 try clear existence_representant_som_vecteur; rewrite <- H1.
exists E; auto.
Qed.
 
Lemma distinct_mult_vecteur :
 forall (A B C D : PO) (a : R),
 A <> B :>PO ->
 a <> 0 :>R -> vec C D = mult_PP a (vec A B) :>PP -> C <> D :>PO.
intros.
elim
 existence_representant_mult_vecteur with (A := A) (B := A) (C := B) (k := a);
 intros E H2; try clear existence_representant_mult_vecteur; 
 try exact H2.
cut (A <> E); intros.
apply distinct_egalite_vecteur with (1 := H3); auto.
rewrite H1; auto.
apply distinct_produit_vecteur with (3 := H2); auto.
Qed.
 
Lemma unicite_coor_bar :
 forall (k k' : R) (A B I : PO),
 A <> B ->
 cons 1 I = add_PP (cons k A) (cons (1 + - k) B) ->
 cons 1 I = add_PP (cons k' A) (cons (1 + - k') B) -> k = k'.
intros.
elim produit_vecteur_nul with (a := k + - k') (A := A) (B := B);
 [ intros H2; try clear produit_vecteur_nul; try exact H2
 | intros H2; try clear produit_vecteur_nul
 | try clear produit_vecteur_nul ].
RReplace k (k + - k' + k').
rewrite H2.
ring.
absurd (A = B); auto.
VReplace (mult_PP (k + - k') (vec A B))
 (add_PP (add_PP (cons k' A) (cons (1 + - k') B))
    (add_PP (cons (- k) A) (cons (-1 + k) B))).
rewrite <- H1.
rewrite H0.
RingPP.
Qed.
 
Lemma unicite_coef_bar :
 forall (x x0 : R) (A B : PO),
 A <> B ->
 1 + x <> 0 ->
 1 + x0 <> 0 ->
 barycentre (cons 1 A) (cons x B) = barycentre (cons 1 A) (cons x0 B) ->
 x = x0.
intros.
cut
 (barycentre (cons (/ (1 + x) * 1) A) (cons (/ (1 + x) * x) B) =
  barycentre (cons (/ (1 + x0) * 1) A) (cons (/ (1 + x0) * x0) B)); 
 intros.
cut (1 + x = 1 + x0); intros.
RReplace x (-1 + (1 + x)).
rewrite H4.
ring.
cut (/ (1 + x) = / (1 + x0)); intros.
replace (1 + x) with (/ / (1 + x)).
rewrite H4.
auto with *.
auto with *.
replace (/ (1 + x)) with (/ (1 + x) * 1).
replace (/ (1 + x0)) with (/ (1 + x0) * 1).
apply
 (unicite_coor_bar (k:=/ (1 + x) * 1) (k':=/ (1 + x0) * 1) (A:=A) (B:=B)
    (I:=barycentre (cons (/ (1 + x) * 1) A) (cons (/ (1 + x) * x) B))); 
 auto.
pattern 1 at 1 in |- *.
replace 1 with (/ (1 + x) * 1 + / (1 + x) * x).
rewrite <- add_PP_barycentre; auto.
replace (1 + - (/ (1 + x) * 1)) with (/ (1 + x) * x); auto.
auto with *.
pattern 1 at 2 in |- *.
replace 1 with (/ (1 + x) * (1 + x)); auto.
ring.
auto with *.
replace (/ (1 + x) * 1 + / (1 + x) * x) with 1; auto.
auto with *.
pattern 1 at 1 in |- *.
replace 1 with (/ (1 + x) * (1 + x)); auto.
ring.
auto with *.
replace (/ (1 + x) * 1 + / (1 + x) * x) with (/ (1 + x) * (1 + x)); auto.
auto with *.
auto with *.
rewrite H3.
pattern 1 at 1 in |- *.
replace 1 with (/ (1 + x0) * 1 + / (1 + x0) * x0).
rewrite <- add_PP_barycentre; auto.
replace (1 + - (/ (1 + x0) * 1)) with (/ (1 + x0) * x0); auto.
pattern 1 at 2 in |- *.
replace 1 with (/ (1 + x0) * (1 + x0)); auto.
ring.
auto with *.
replace (/ (1 + x0) * 1 + / (1 + x0) * x0) with 1; auto.
auto with *.
pattern 1 at 1 in |- *.
replace 1 with (/ (1 + x0) * (1 + x0)); auto.
ring.
auto with *.
replace (/ (1 + x0) * 1 + / (1 + x0) * x0) with (/ (1 + x0) * (1 + x0)); auto.
auto with *.
auto with *.
auto with *.
ring.
rewrite homogene_barycentre.
rewrite homogene_barycentre; auto.
auto with *.
try exact H0.
auto with *.
Qed.
 
Lemma unicite_coor_bar_aux :
 forall (A B C I : PO) (x y x' y' : R),
 x <> x' :>R \/ y <> y' :>R ->
 cons 1 I = add_PP (add_PP (cons x A) (cons y B)) (cons (1 + - (x + y)) C)
 :>PP ->
 cons 1 I =
 add_PP (add_PP (cons x' A) (cons y' B)) (cons (1 + - (x' + y')) C) :>PP ->
 alignes A B C.
intros.
assert (vec C I = add_PP (mult_PP x (vec C A)) (mult_PP y (vec C B))).
unfold vec in |- *.
rewrite H0; Ringvec.
assert (vec C I = add_PP (mult_PP x' (vec C A)) (mult_PP y' (vec C B))).
unfold vec in |- *.
rewrite H1; Ringvec.
assert
 (add_PP (mult_PP (x + - x') (vec C A)) (mult_PP (y + - y') (vec C B)) = zero).
VReplace zero (add_PP (vec C I) (mult_PP (-1) (vec C I))).
pattern (vec C I) at 1 in |- *; rewrite H2; rewrite H3; Ringvec.
assert (mult_PP (x + - x') (vec C A) = mult_PP (y' + - y) (vec C B)).
VReplace (mult_PP (y' + - y) (vec C B))
 (add_PP (mult_PP (y' + - y) (vec C B)) zero).
rewrite <- H4; Ringvec.
elim H; [ intros H6; try clear H; try exact H6 | intros H6; try clear H ].
assert (x + - x' <> 0).
contrapose H6.
RReplace x' (x' + 0).
rewrite <- H; ring.
assert (alignes C B A); auto with geo.
apply colineaire_alignes with (/ (x + - x') * (y' + - y)).
VReplace (mult_PP (/ (x + - x') * (y' + - y)) (vec C B))
 (mult_PP (/ (x + - x')) (mult_PP (y' + - y) (vec C B))).
rewrite <- H5; Fieldvec (x + - x').
assert (y' + - y <> 0).
contrapose H6.
RReplace y (y + 0).
rewrite <- H; ring.
assert (alignes C A B); auto with geo.
apply colineaire_alignes with (/ (y' + - y) * (x + - x')).
VReplace (mult_PP (/ (y' + - y) * (x + - x')) (vec C A))
 (mult_PP (/ (y' + - y)) (mult_PP (x + - x') (vec C A))).
rewrite H5; Fieldvec (y' + - y).
Qed.
 
Lemma unicite_coor_bar2 :
 forall (A B C I : PO) (x y x' y' : R),
 ~ alignes A B C ->
 cons 1 I = add_PP (add_PP (cons x A) (cons y B)) (cons (1 + - (x + y)) C)
 :>PP ->
 cons 1 I =
 add_PP (add_PP (cons x' A) (cons y' B)) (cons (1 + - (x' + y')) C) :>PP ->
 x = x' :>R /\ y = y' :>R.
intros.
assert (~ x <> x' /\ ~ y <> y').
apply not_or_and; auto.
contrapose H.
apply
 (unicite_coor_bar_aux (A:=A) (B:=B) (C:=C) (I:=I) (x:=x) (y:=y) (x':=x')
    (y':=y')); auto.
elim H2; [ intros H3 H4; try clear H2; try exact H3 ].
split; (apply NNPP; auto).
Qed.
 
Lemma parallelogramme_non_concours :
 forall A B A1 B1 S : PO,
 ~ alignes A A1 B ->
 alignes A A1 S ->
 alignes B B1 S ->
 add_PP (cons 1 A) (cons (-1) A1) <> add_PP (cons 1 B) (cons (-1) B1).
intros.
contrapose H.
assert (vec A1 A = vec B1 B).
unfold vec in |- *.
RingPP1 H2.
RingPP.
halignes H1 ipattern:k.
assert (A1 = A); auto with geo.
apply vecteur_nul_conf.
rewrite H3; rewrite H1; Ringvec.
halignes H0 ipattern:k0.
apply colineaire_alignes with (k0 + - k).
VReplace (vec A B) (add_PP (vec A S) (mult_PP (-1) (vec B S))).
rewrite H5; rewrite H4.
VReplace (vec B B1) (mult_PP (-1) (vec B1 B)).
rewrite <- H3.
Ringvec.
Qed.
 
Lemma concours_unique :
 forall A B A1 B1 I J : PO,
 ~ alignes A A1 B ->
 B1 <> B ->
 alignes A A1 I ->
 alignes B1 B I -> alignes A A1 J -> alignes B1 B J -> I = J.
intros A B A1 B1 I J H.
unfold alignes in |- *; intros H50 H0 H1 H2 H3.
elim H3; clear H3; [ intros; tauto | unfold alignes1 in |- *; intros ].
elim H1; clear H1; [ intros; tauto | unfold alignes1 in |- *; intros ].
deroule_triangle A A1 B.
elim H2; clear H2; [ intros; tauto | unfold alignes1 in |- *; intros ].
elim H0; clear H0 H5 H4;
 [ intros; tauto; clear H6 | unfold alignes1 in |- *; intros ].
elim H3; intros k0 H4; try clear H3; try exact H4.
elim H2; intros k1 H3; try clear H2; try exact H3.
elim H1; intros k2 H2; try clear H1; try exact H2.
elim H0; intros k3 H1; try clear H0; try exact H1.
elim (classic (k0 + - k2 = 0)); intros.
cut (k0 = k2); intros.
rewrite H5 in H4.
apply conversion_PP with (a := 1) (b := 1); auto.
rewrite H4; auto.
auto with *.
replace k0 with (k2 + (k0 + - k2)); auto.
rewrite H0; ring.
ring.
cut
 (cons (k0 + - k2) B =
  add_PP (cons (k0 * k3 + - (k2 * k1)) A)
    (cons (k0 + - k2 + - (k0 * k3 + - (k2 * k1))) A1)); 
 intros.
assert (~ alignes1 A A1 B); auto with geo.
absurd
 (ex (fun k0 : R => cons 1 B = add_PP (cons k0 A) (cons (1 + - k0) A1)));
 auto.
exists (/ (k0 + - k2) * (k0 * k3 + - (k2 * k1))).
apply mult_PP_regulier with (k0 + - k2); auto.
pattern 1 at 2 in |- *.
replace 1 with ((k0 + - k2) * / (k0 + - k2)); auto.
rewrite <- distrib_mult_cons.
rewrite def_mult_PP.
replace ((k0 + - k2) * (/ (k0 + - k2) * (k0 * k3 + - (k2 * k1)))) with
 (k0 * k3 + - (k2 * k1)); auto.
replace ((k0 + - k2) * 1) with (k0 + - k2); auto.
replace
 ((k0 + - k2) * / (k0 + - k2) + - (/ (k0 + - k2) * (k0 * k3 + - (k2 * k1))))
 with (/ (k0 + - k2) * (k0 + - k2 + - (k0 * k3 + - (k2 * k1)))); 
 auto.
replace
 ((k0 + - k2) * (/ (k0 + - k2) * (k0 + - k2 + - (k0 * k3 + - (k2 * k1)))))
 with (1 * (k0 + - k2 + - (k0 * k3 + - (k2 * k1)))); 
 auto.
rewrite H5.
RingPP.
replace 1 with ((k0 + - k2) * / (k0 + - k2)); auto.
ring.
auto with *.
ring.
ring.
replace ((k0 + - k2) * (/ (k0 + - k2) * (k0 * k3 + - (k2 * k1)))) with
 ((k0 + - k2) * / (k0 + - k2) * (k0 * k3 + - (k2 * k1))).
replace ((k0 + - k2) * / (k0 + - k2)) with 1.
ring.
auto with *.
ring.
auto with *.
cut
 (add_PP (cons (k0 * k2) B1) (cons (k0 * (1 + - k2)) B) =
  add_PP (cons (k0 * k3) A) (cons (k0 * (1 + - k3)) A1)); 
 intros.
cut
 (add_PP (cons (k2 * k0) B1) (cons (k2 * (1 + - k0)) B) =
  add_PP (cons (k2 * k1) A) (cons (k2 * (1 + - k1)) A1)); 
 intros.
replace (cons (k0 + - k2) B) with
 (add_PP (cons (k0 * (1 + - k2)) B) (cons (- (k2 * (1 + - k0))) B)).
replace (cons (k0 * k3 + - (k2 * k1)) A) with
 (add_PP (cons (k0 * k3) A) (cons (- (k2 * k1)) A)).
replace (cons (k0 + - k2 + - (k0 * k3 + - (k2 * k1))) A1) with
 (add_PP (cons (k0 * (1 + - k3)) A1) (cons (- (k2 * (1 + - k1))) A1)).
RingPP2 H5.
cut
 (add_PP (cons (- (k2 * k0)) B1) (cons (- (k2 * (1 + - k0))) B) =
  add_PP (cons (- (k2 * k1)) A) (cons (- (k2 * (1 + - k1))) A1)); 
 intros.
RingPP2 H8.
RingPP.
replace (add_PP (cons (- (k2 * k0)) B1) (cons (- (k2 * (1 + - k0))) B)) with
 (mult_PP (-1) (add_PP (cons (k2 * k0) B1) (cons (k2 * (1 + - k0)) B))).
rewrite H7.
RingPP.
RingPP.
RingPP.
RingPP.
RingPP.
rewrite distrib_mult_cons.
rewrite distrib_mult_cons.
rewrite <- H4.
rewrite H3; auto.
rewrite distrib_mult_cons.
rewrite distrib_mult_cons.
rewrite <- H2.
rewrite H1; auto.
Qed.
 
Lemma couple_colineaires_parallelogramme :
 forall (A B C D : PO) (k k' : R),
 A <> B ->
 ~ alignes A B C ->
 vec C D = mult_PP k (vec A B) ->
 vec B D = mult_PP k' (vec A C) -> vec B D = vec A C.
unfold vec in |- *; intros.
cut
 (cons 1 D =
  add_PP (add_PP (cons (- k') A) (cons 1 B)) (cons (1 + - (- k' + 1)) C));
 intros.
cut
 (cons 1 D =
  add_PP (add_PP (cons (- k) A) (cons k B)) (cons (1 + - (- k + k)) C));
 intros.
cut (k = k' /\ k = 1); intros.
elim H5; intros H6 H7; try clear H5; try exact H7.
rewrite <- H6 in H2; rewrite H7 in H2.
rewrite H2; Ringvec.
cut (- k = - k' /\ k = 1); intros.
elim H5; intros H6 H7; try clear H5; try exact H7.
split; [ idtac | try assumption ].
replace k with (- - k).
rewrite H6; ring.
ring.
apply (unicite_coor_bar2 (A:=A) (B:=B) (C:=C) (I:=D)); auto.
RingPP2 H1.
RingPP.
RingPP2 H2.
RingPP.
Qed.