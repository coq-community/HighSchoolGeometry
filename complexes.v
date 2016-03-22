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


Require Export trigo.
Set Implicit Arguments.
Unset Strict Implicit.
Parameters (O : PO) (I : PO) (J : PO).
Hypothesis OIJ : repere_orthonormal_direct O I J.
Hint Resolve OIJ: geo.
 
Lemma OIJ_repere_ortho : repere_orthonormal O I J.
auto with geo.
Qed.
 
Lemma OIJ_repere : repere O I J.
auto with geo.
Qed.
 
Lemma OI_distincts : O <> I.
elim OIJ; intros.
auto with geo.
elim H0; intros; auto with geo.
Qed.
 
Lemma OJ_distincts : O <> J.
elim OIJ; intros.
elim H0; intros; auto with geo.
Qed.
Hint Resolve OIJ_repere_ortho OIJ_repere OI_distincts OJ_distincts: geo.
 
Lemma IJ_distincts : I <> J.
cut (repere_orthonormal O I J); intros; auto with geo.
elim H; intros.
apply non_alignes_distincts2 with O; auto.
apply orthogonal_non_alignes; auto with geo.
Qed.
Hint Resolve IJ_distincts: geo.
Parameter C : Type.
Parameter affixe : PO -> C.
Parameter image : C -> PO.
Parameter affixe_vec : PP -> C.
Parameter image_vec : C -> PP.
 
Axiom affixe_image : forall (z : C) (M : PO), M = image z -> z = affixe M.
 
Axiom image_affixe : forall (z : C) (M : PO), z = affixe M -> M = image z.
 
Axiom existence_image_complexe : forall z : C, exists M : PO, M = image z.
 
Axiom existence_affixe_point : forall M : PO, exists z : C, z = affixe M.
 
Axiom
  affixe_point_vecteur :
    forall (z : C) (M : PO), z = affixe M -> z = affixe_vec (vec O M).
 
Axiom
  affixe_vecteur_point :
    forall (z : C) (M : PO), z = affixe_vec (vec O M) -> z = affixe M.
 
Axiom
  image_point_vecteur :
    forall (z : C) (M : PO), M = image z -> vec O M = image_vec z.
 
Axiom
  image_vecteur_point :
    forall (z : C) (M : PO), vec O M = image_vec z -> M = image z.
Hint Resolve image_affixe affixe_image affixe_point_vecteur
  affixe_vecteur_point image_point_vecteur image_vecteur_point: geo.
 
Lemma affixe_image_vecteur :
 forall (z : C) (M : PO), vec O M = image_vec z -> z = affixe_vec (vec O M).
intros; eauto with geo.
Qed.
 
Lemma image_affixe_vecteur :
 forall (z : C) (M : PO), z = affixe_vec (vec O M) -> vec O M = image_vec z.
intros; eauto with geo.
Qed.
 
Lemma existence_image_vecteur_complexe :
 forall z : C, exists M : PO, vec O M = image_vec z.
intros.
elim existence_image_complexe with (z := z); intros M H;
 try clear existence_image_complexe; try exact H.
exists M; eauto with geo.
Qed.
 
Lemma existence_affixe_vecteur_point :
 forall M : PO, exists z : C, z = affixe_vec (vec O M).
intros.
elim existence_affixe_point with (M := M); intros z H;
 try clear existence_affixe_point; try exact H.
exists z; eauto with geo.
Qed.
Parameter cons_cart : R -> R -> C.
 
Axiom
  cart_point_complexe :
    forall (z : C) (a b : R) (M : PO),
    vec O M = add_PP (mult_PP a (vec O I)) (mult_PP b (vec O J)) :>PP ->
    z = affixe M -> z = cons_cart a b.
 
Axiom
  complexe_cart_point :
    forall (z : C) (a b : R) (M : PO),
    z = cons_cart a b ->
    z = affixe M ->
    vec O M = add_PP (mult_PP a (vec O I)) (mult_PP b (vec O J)) :>PP.
Hint Resolve abscisse_def ordonnee_def cart_def cart_point_complexe
  complexe_cart_point: geo.
 
Lemma cart_point_complexe2 :
 forall (z : C) (a b : R) (M : PO),
 vec O M = add_PP (mult_PP a (vec O I)) (mult_PP b (vec O J)) :>PP ->
 M = image z -> z = cons_cart a b.
intros.
eauto with geo.
Qed.
 
Lemma complexe_cart_point2 :
 forall (z : C) (a b : R) (M : PO),
 z = cons_cart a b ->
 M = image z ->
 vec O M = add_PP (mult_PP a (vec O I)) (mult_PP b (vec O J)) :>PP.
intros.
eauto with geo.
Qed.
Hint Resolve cart_point_complexe2 complexe_cart_point2: geo.
 
Lemma existence_parties_relles_imaginaires :
 forall z : C, exists a : R, (exists b : R, z = cons_cart a b).
intros.
elim existence_image_complexe with (z := z); intros M H1;
 try clear existence_image_complexe; try exact H1.
elim existence_coordonnees with (O := O) (I := I) (J := J) (M := M);
 [ intros x H2; elim H2; intros y H3 | auto with geo ].
exists x; exists y.
apply (cart_point_complexe (z:=z) (a:=x) (b:=y) (M:=M)); auto with geo.
Qed.
 
Lemma unicite_parties_relles_imaginaires :
 forall (z : C) (a b a' b' : R),
 z = cons_cart a b -> z = cons_cart a' b' -> a = a' /\ b = b'.
intros.
elim existence_image_complexe with (z := z); intros M H1;
 try clear existence_image_complexe; try exact H1.
apply (unicite_coordonnees (O:=O) (I:=I) (J:=J) (M:=M)); auto with geo.
apply complexe_cart_point with z; auto with geo.
apply complexe_cart_point with z; auto with geo.
Qed.
 
Lemma egalite_point_image :
 forall (z z' : C) (M M' : PO),
 z = affixe M -> z' = affixe M' -> M = M' -> z = z'.
intros.
elim existence_parties_relles_imaginaires with (z := z); intros a H2; elim H2;
 intros b H3; try clear H2; try exact H3.
elim existence_parties_relles_imaginaires with (z := z'); intros a' H2;
 elim H2; intros b' H4; try clear H2; try exact H4.
generalize (complexe_cart_point (z:=z) (a:=a) (b:=b)); intros H2.
cut (vec O M = add_PP (mult_PP a (vec O I)) (mult_PP b (vec O J))); intros;
 auto.
cut (vec O M = add_PP (mult_PP a' (vec O I)) (mult_PP b' (vec O J))); intros.
elim
 unicite_composantes_vecteur
  with
    (a1 := a)
    (a2 := b)
    (b1 := a')
    (b2 := b')
    (O := O)
    (I := I)
    (J := J)
    (A := O)
    (B := M);
 [ intros H7 H8; try clear unicite_composantes_vecteur; try exact H8
 | auto with geo
 | auto
 | auto ].
rewrite H3; rewrite H4; rewrite H7; rewrite H8; auto.
rewrite H1.
apply complexe_cart_point with z'; auto.
Qed.
 
Lemma egalite_affixe_point :
 forall (z z' : C) (M M' : PO),
 z = affixe M -> z' = affixe M' -> z = z' -> M = M'.
intros.
elim existence_parties_relles_imaginaires with (z := z); intros a H2; elim H2;
 intros b H3; try clear H2; try exact H3.
elim existence_parties_relles_imaginaires with (z := z'); intros a' H2;
 elim H2; intros b' H4; try clear H2; try exact H4.
generalize (complexe_cart_point (z:=z) (a:=a) (b:=b)); intros H2.
cut (vec O M = add_PP (mult_PP a (vec O I)) (mult_PP b (vec O J))); intros;
 auto.
cut (vec O M' = add_PP (mult_PP a' (vec O I)) (mult_PP b' (vec O J))); intros.
apply vecteur_nul_conf.
replace (vec M M') with (add_PP (vec O M') (mult_PP (-1) (vec O M)));
 [ idtac | Ringvec ].
elim
 unicite_parties_relles_imaginaires
  with (z := z) (a := a) (b := b) (a' := a') (b' := b');
 [ intros; try exact H8 | auto | auto ].
rewrite H5; rewrite H6; rewrite H7; rewrite H8.
Ringvec.
rewrite H1; auto.
apply complexe_cart_point with z'; auto.
Qed.
 
Lemma egalite_affixe : forall z z' : C, image z = image z' -> z = z'.
intros.
elim existence_image_complexe with (z := z); intros M H0; try exact H0.
elim existence_image_complexe with (z := z'); intros M'; intros.
apply egalite_point_image with (M := M) (M' := M'); auto with geo.
rewrite H0; rewrite H1; auto.
Qed.