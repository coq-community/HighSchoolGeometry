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


Require Export equations_droites.
Require Export contact.
Set Implicit Arguments.
Unset Strict Implicit.
 
Lemma cercle_equation :
 forall (A M : PO) (r a b x y : R),
 a = abscisse A ->
 b = ordonnee A ->
 x = abscisse M ->
 y = ordonnee M -> cercle A r M -> Rsqr (x + - a) + Rsqr (y + - b) = Rsqr r.
icercle.
assert (scalaire (vec A M) (vec A M) = Rsqr r).
rewrite carre_scalaire_distance; rewrite H3; auto.
rewrite <- H4.
assert
 (vec A M =
  add_PP (mult_PP (x + - a) (vec O I)) (mult_PP (y + - b) (vec O J))).
apply composantes_vecAB; auto with geo.
rewrite
 (scalaire_composantes_ABCD (O:=O) (I:=I) (J:=J) (A:=A) (B:=M) (C:=A) (D:=M)
    (x:=x + - a) (y:=y + - b) (x':=x + - a) (y':=y + - b))
 ; auto with geo.
Qed.
 
Lemma equation_cartesienne_cercle :
 forall (M : PO) (x y a b r : R),
 r >= 0 ->
 x = abscisse M ->
 y = ordonnee M ->
 Rsqr (x + - a) + Rsqr (y + - b) = Rsqr r -> exists A : _, cercle A r M.
icercle.
assert (vec O M = add_PP (mult_PP x (vec O I)) (mult_PP y (vec O J)));
 auto with geo.
elim
 existence_representant_comb_lin_vecteur
  with (A := O) (B := I) (C := O) (D := J) (a := a) (b := b); 
 intros A H4.
exists A.
assert
 (vec A M =
  add_PP (mult_PP (x + - a) (vec O I)) (mult_PP (y + - b) (vec O J)));
 auto with geo.
apply composantes_vecAB; eauto with geo.
assert (scalaire (vec A M) (vec A M) = Rsqr r).
rewrite
 (scalaire_composantes_ABCD (O:=O) (I:=I) (J:=J) (A:=A) (B:=M) (C:=A) (D:=M)
    (x:=x + - a) (y:=y + - b) (x':=x + - a) (y':=y + - b))
 ; auto with geo.
rewrite carre_scalaire_distance in H6.
apply Rsqr_inj; auto with geo real.
Qed.
 
Lemma equation_generale_cercle :
 forall (M : PO) (x y a b c : R),
 c + (Rsqr a + Rsqr b) >= 0 ->
 x = abscisse M ->
 y = ordonnee M ->
 Rsqr x + (Rsqr y + (2 * (a * x) + 2 * (b * y))) = c ->
 exists A : _, cercle A (sqrt (c + (Rsqr a + Rsqr b))) M.
intros M x y a b c H H0 H1; try assumption.
RReplace (Rsqr x + (Rsqr y + (2 * (a * x) + 2 * (b * y))))
 (Rsqr x + 2 * (a * x) + (Rsqr y + 2 * (b * y))).
replace (Rsqr x + 2 * (a * x)) with (Rsqr (x + a) + - Rsqr a).
replace (Rsqr y + 2 * (b * y)) with (Rsqr (y + b) + - Rsqr b).
intros; assert (Rsqr (x + - - a) + Rsqr (y + - - b) = c + (Rsqr a + Rsqr b)).
RReplace (x + - - a) (x + a).
RReplace (y + - - b) (y + b).
rewrite <- H2; ring.
apply
 (equation_cartesienne_cercle (M:=M) (x:=x) (y:=y) (a:=
    - a) (b:=- b) (r:=sqrt (c + (Rsqr a + Rsqr b)))); 
 auto with real.
rewrite Rsqr_sqrt; auto with real.
rewrite Rsqr_plus; ring.
rewrite Rsqr_plus; ring.
Qed.
 
Lemma tangente_cercle_equation :
 forall (A C M : PO) (a b c d x y : R),
 a = abscisse A ->
 b = ordonnee A ->
 c = abscisse C ->
 d = ordonnee C ->
 x = abscisse M ->
 y = ordonnee M ->
 tangente_cercle A C C M -> (c + - a) * (x + - c) + (d + - b) * (y + - d) = 0.
icercle.
rewrite <-
 (scalaire_composantes_ABCD (O:=O) (I:=I) (J:=J) (A:=A) (B:=C) (C:=C) (D:=M)
    (x:=c + - a) (y:=d + - b) (x':=x + - c) (y':=y + - d))
 ; auto with geo.
apply composantes_vecAB; eauto with geo.
apply composantes_vecAB; eauto with geo.
Qed.
 
Lemma equation_tangente_cercle :
 forall (A C M : PO) (a b c d x y : R),
 a = abscisse A ->
 b = ordonnee A ->
 c = abscisse C ->
 d = ordonnee C ->
 x = abscisse M ->
 y = ordonnee M ->
 (c + - a) * (x + - c) + (d + - b) * (y + - d) = 0 -> tangente_cercle A C C M.
icercle.
assert (orthogonal (vec A C) (vec C M)).
apply def_orthogonal2.
rewrite
 (scalaire_composantes_ABCD (O:=O) (I:=I) (J:=J) (A:=A) (B:=C) (C:=C) (D:=M)
    (x:=c + - a) (y:=d + - b) (x':=x + - c) (y':=y + - d))
 ; auto with geo.
apply composantes_vecAB; eauto with geo.
apply composantes_vecAB; eauto with geo.
auto with geo.
Qed.
 
Lemma cercle_diametre_equation :
 forall (A A' M : PO) (a b a' b' x y : R),
 a = abscisse A ->
 b = ordonnee A ->
 a' = abscisse A' ->
 b' = ordonnee A' ->
 x = abscisse M ->
 y = ordonnee M ->
 cercle_diametre A A' M ->
 (x + - a) * (x + - a') + (y + - b) * (y + - b') = 0.
intros.
elim (caracterisation_cercle_diametre A A' M); intros.
rewrite <- H6; auto.
rewrite <-
 (scalaire_composantes_ABCD (O:=O) (I:=I) (J:=J) (A:=A) (B:=M) (C:=A') (D:=M)
    (x:=x + - a) (y:=y + - b) (x':=x + - a') (y':=y + - b'))
 ; auto with geo.
VReplace (vec A M) (mult_PP (-1) (vec M A)).
VReplace (vec A' M) (mult_PP (-1) (vec M A')).
Simplscal.
apply composantes_vecAB; eauto with geo.
apply composantes_vecAB; eauto with geo.
Qed.
 
Lemma equation_cercle_diametre :
 forall (A A' M : PO) (a b a' b' x y : R),
 a = abscisse A ->
 b = ordonnee A ->
 a' = abscisse A' ->
 b' = ordonnee A' ->
 x = abscisse M ->
 y = ordonnee M ->
 (x + - a) * (x + - a') + (y + - b) * (y + - b') = 0 ->
 cercle_diametre A A' M.
intros.
elim (caracterisation_cercle_diametre A A' M); intros.
apply H7.
rewrite <- H5.
rewrite <-
 (scalaire_composantes_ABCD (O:=O) (I:=I) (J:=J) (A:=A) (B:=M) (C:=A') (D:=M)
    (x:=x + - a) (y:=y + - b) (x':=x + - a') (y':=y + - b'))
 ; auto with geo.
VReplace (vec A M) (mult_PP (-1) (vec M A)).
VReplace (vec A' M) (mult_PP (-1) (vec M A')).
Simplscal.
apply composantes_vecAB; eauto with geo.
apply composantes_vecAB; eauto with geo.
Qed.
 
Lemma equation_k_cercle :
 forall (A A' K M : PO) (k a b a' b' x y : R),
 k + Rsqr (distance K A) >= 0 ->
 a = abscisse A ->
 b = ordonnee A ->
 a' = abscisse A' ->
 b' = ordonnee A' ->
 x = abscisse M ->
 y = ordonnee M ->
 K = milieu A A' ->
 (x + - a) * (x + - a') + (y + - b) * (y + - b') = k ->
 cercle K (sqrt (k + Rsqr (distance K A))) M.
intros A A' K M k a b a' b' x y H H0 H1 H2 H3 H4 H5 H6; try assumption.
rewrite <-
 (scalaire_composantes_ABCD (O:=O) (I:=I) (J:=J) (A:=A) (B:=M) (C:=A') (D:=M)
    (x:=x + - a) (y:=y + - b) (x':=x + - a') (y':=y + - b'))
 ; auto with geo.
replace (scalaire (vec A M) (vec A' M)) with (scalaire (vec M A) (vec M A')).
intros.
apply ligne_niveau_MAMB_k with A'; auto.
VReplace (vec M A) (mult_PP (-1) (vec A M)).
VReplace (vec M A') (mult_PP (-1) (vec A' M)).
Simplscal.
apply composantes_vecAB; eauto with geo.
apply composantes_vecAB; eauto with geo.
Qed.