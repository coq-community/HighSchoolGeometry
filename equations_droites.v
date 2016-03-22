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


Require Export determinant.
Set Implicit Arguments.
Unset Strict Implicit.
Hint Resolve cart_def not_and_or or_not_and: geo.
Parameter vec_directeur : PP -> DR -> Prop.
 
Axiom
  vec_directeur_def :
    forall A B C D : PO,
    A <> B ->
    C <> D ->
    vec_directeur (vec A B) (droite C D) -> det (vec A B) (vec C D) = 0.
 
Axiom
  vec_directeur_def2 :
    forall A B C D : PO,
    A <> B ->
    C <> D ->
    det (vec A B) (vec C D) = 0 -> vec_directeur (vec A B) (droite C D).
 
Lemma vec_directeur_trivial :
 forall A B : PO, A <> B -> vec_directeur (vec A B) (droite A B).
intros.
apply vec_directeur_def2; auto.
apply determinant_colinearite with 1; auto.
Ringvec.
Qed.
 
Lemma existence_vec_directeur :
 forall A B : PO,
 A <> B ->
 exists C : PO, (exists D : PO, vec_directeur (vec C D) (droite A B)).
intros.
exists A; exists B.
apply vec_directeur_trivial; auto.
Qed.
 
Lemma vec_directeur_permute :
 forall A B C D : PO,
 A <> B ->
 C <> D ->
 vec_directeur (vec A B) (droite C D) -> vec_directeur (vec C D) (droite A B).
intros.
apply vec_directeur_def2; auto.
rewrite determinant_antisymetrique.
rewrite vec_directeur_def; auto.
ring.
Qed.
 
Lemma paralleles_vec_directeur :
 forall A B C D : PO,
 A <> B ->
 C <> D ->
 paralleles (droite A B) (droite C D) -> vec_directeur (vec A B) (droite C D).
intros.
apply vec_directeur_def2; auto.
elim paralleles_vecteur with (A := C) (B := D) (C := A) (D := B);
 [ intros k H3; try clear paralleles_vecteur; try exact H3
 | auto
 | auto
 | auto with geo ].
apply determinant_colinearite with k; auto.
Qed.
Hint Resolve vec_directeur_def vec_directeur_def2 cartvec_def: geo.
Hint Immediate vec_directeur_permute: geo.
 
Lemma vec_directeur_paralleles :
 forall A B C D : PO,
 A <> B ->
 C <> D ->
 vec_directeur (vec A B) (droite C D) -> paralleles (droite A B) (droite C D).
intros.
elim determinant_nul_colinearite with (A := C) (B := D) (C := A) (D := B);
 [ intros k H4; try clear determinant_nul_colinearite; try exact H4
 | auto
 | auto with geo ].
apply colineaires_paralleles with k; auto.
Qed.
Hint Resolve vec_directeur_paralleles paralleles_vec_directeur: geo.
 
Lemma vec_directeur_calcul :
 forall (A B C D : PO) (x y x0 y0 a b : R),
 A <> B ->
 C <> D ->
 x = abscisse D ->
 y = ordonnee D ->
 x0 = abscisse C ->
 y0 = ordonnee C ->
 a = absvec (vec A B) ->
 b = ordvec (vec A B) ->
 vec_directeur (vec A B) (droite C D) ->
 b * (x + - x0) + - (a * (y + - y0)) = 0.
intros A B C D x y x0 y0 a b H H0 H1 H2 H3 H4 H5 H6 H7; try assumption.
cut
 (vec C D =
  add_PP (mult_PP (x + - x0) (vec O I)) (mult_PP (y + - y0) (vec O J)));
 intros.
2: apply composantes_vecAB; eauto with geo.
cut (vec A B = add_PP (mult_PP a (vec O I)) (mult_PP b (vec O J)));
 [ intros | auto with geo ].
RReplace 0 (-0).
rewrite <- (vec_directeur_def (A:=A) (B:=B) (C:=C) (D:=D)); auto.
rewrite
 (determinant_def (A:=A) (B:=B) (C:=C) (D:=D) (x:=a) (y:=b) (x':=
    x + - x0) (y':=y + - y0)); auto.
ring.
Qed.
 
Lemma equation_droite_parallele :
 forall (A B C D : PO) (x y x0 y0 a b : R),
 A <> B ->
 C <> D ->
 x = abscisse D ->
 y = ordonnee D ->
 x0 = abscisse C ->
 y0 = ordonnee C ->
 a = absvec (vec A B) ->
 b = ordvec (vec A B) ->
 paralleles (droite A B) (droite C D) ->
 b * (x + - x0) + - (a * (y + - y0)) = 0.
intros.
apply vec_directeur_calcul with (1 := H) (2 := H0); auto with geo.
Qed.
 
Lemma alignes_equation_cartesienne :
 forall (A B M : PO) (x y : R),
 x = abscisse M ->
 y = ordonnee M ->
 A <> B ->
 alignes A B M ->
 exists a : R,
   (exists b : R,
      (exists c : R, a * x + (b * y + c) = 0 /\ ~ (a = 0 /\ b = 0))).
intros A B M x y H20 H30 H0 H1; try assumption.
cut (vec O M = add_PP (mult_PP x (vec O I)) (mult_PP y (vec O J)));
 [ intros H | auto with geo ].
elim composantes_vecteur with (O := O) (I := I) (J := J) (M := A) (N := B);
 [ intros a H2; elim H2; [ intros b H3; try clear H2; try exact H3 ]
 | auto with geo ].
elim existence_coordonnees with (O := O) (I := I) (J := J) (M := A);
 [ intros x0 H2; elim H2; [ intros y0 H4; try clear H2; try exact H4 ]
 | auto with geo ].
cut
 (vec A M =
  add_PP (mult_PP (x + - x0) (vec O I)) (mult_PP (y + - y0) (vec O J)));
 intros.
2: apply composantes_vecAB; eauto with geo.
exists (- b); exists a; exists (b * x0 + - (a * y0)).
split; [ try assumption | idtac ].
rewrite <- (alignement_determinant (A:=A) (B:=B) (M:=M)); auto.
rewrite
 (determinant_def (A:=A) (B:=B) (C:=A) (D:=M) (x:=a) (y:=b) (x':=
    x + - x0) (y':=y + - y0)); auto.
ring.
contrapose H0.
applatit_and.
apply vecteur_nul_conf.
rewrite H3.
RReplace b (- - b).
rewrite H6; rewrite H7; Ringvec.
Qed.
 
Lemma equation_cartesienne_alignes :
 forall (M : PO) (x y a b c : R),
 x = abscisse M ->
 y = ordonnee M ->
 ~ (a = 0 /\ b = 0) ->
 a * x + (b * y + c) = 0 ->
 exists A : _, (exists B : _, A <> B /\ alignes A B M).
intros M x y a b c H20 H30 H0 H1; try assumption.
cut (vec O M = add_PP (mult_PP x (vec O I)) (mult_PP y (vec O J)));
 [ intros H | auto with geo ].
cut (a <> 0 \/ b <> 0); intros.
elim H2; intros.
elim
 existence_representant_comb_lin_vecteur
  with (A := O) (B := I) (C := O) (D := J) (a := - c / a) (b := 0);
 [ intros A H4; try clear existence_representant_comb_lin_vecteur;
    try exact H4 ].
elim
 existence_representant_comb_lin_vecteur
  with (A := O) (B := I) (C := O) (D := J) (a := - b + - c / a) (b := a);
 [ intros B H6; try clear existence_representant_comb_lin_vecteur;
    try exact H6 ].
exists A; exists B.
cut (vec A B = add_PP (mult_PP (- b) (vec O I)) (mult_PP a (vec O J)));
 intros.
cut (A <> B); intros.
split; [ try assumption | idtac ].
apply determinant_nul_alignement; auto.
cut (vec A M = add_PP (mult_PP (x + c / a) (vec O I)) (mult_PP y (vec O J)));
 intros.
rewrite
 (determinant_def (A:=A) (B:=B) (C:=A) (D:=M) (x:=- b) (y:=a) (x':=
    x + c / a) (y':=y)); auto.
RReplace 0 (-0).
rewrite <- H1; auto.
RReplace (- b * y + - (a * (x + c / a))) (- (b * y + a * (x + c / a))).
unfold Rdiv in |- *.
RReplace (a * (x + c * / a)) (a * x + c * (a * / a)).
RReplace (a * / a) 1.
ring.
RReplace (x + c / a) (x + - (- c / a)).
RReplace y (y + -0).
apply composantes_vecAB; eauto with geo.
unfold Rdiv in |- *.
ring.
contrapose H3.
rewrite H7 in H4.
elim
 unicite_coordonnees
  with
    (O := O)
    (I := I)
    (J := J)
    (M := B)
    (x := - b + - c / a)
    (y := a)
    (x' := - c / a)
    (y' := 0);
 [ intros H9 H10; try clear unicite_coordonnees; try exact H10
 | auto with geo
 | auto
 | auto ].
RReplace (- b) (- b + - c / a + - (- c / a)).
pattern a at 3 in |- *.
RReplace a (a + -0).
apply composantes_vecAB; eauto with geo.
elim
 existence_representant_comb_lin_vecteur
  with (A := O) (B := I) (C := O) (D := J) (a := 0) (b := - c / b);
 [ intros A H4; try clear existence_representant_comb_lin_vecteur;
    try exact H4 ].
elim
 existence_representant_comb_lin_vecteur
  with (A := O) (B := I) (C := O) (D := J) (a := - b) (b := a + - c / b);
 [ intros B H6; try clear existence_representant_comb_lin_vecteur;
    try exact H6 ].
exists A; exists B.
cut (vec A B = add_PP (mult_PP (- b) (vec O I)) (mult_PP a (vec O J)));
 intros.
cut (A <> B); intros.
split; [ try assumption | idtac ].
apply determinant_nul_alignement; auto.
cut (vec A M = add_PP (mult_PP x (vec O I)) (mult_PP (y + c / b) (vec O J)));
 intros.
rewrite
 (determinant_def (A:=A) (B:=B) (C:=A) (D:=M) (x:=- b) (y:=a) (x':=x)
    (y':=y + c / b)); auto.
RReplace 0 (-0).
rewrite <- H1; auto.
RReplace (- b * (y + c / b) + - (a * x)) (- (b * (y + c / b) + a * x)).
unfold Rdiv in |- *.
RReplace (b * (y + c * / b)) (b * y + c * (b * / b)).
RReplace (b * / b) 1.
ring.
RReplace (y + c / b) (y + - (- c / b)).
RReplace x (x + -0).
apply composantes_vecAB; eauto with geo.
unfold Rdiv in |- *.
ring.
contrapose H3.
rewrite H7 in H4.
elim
 unicite_coordonnees
  with
    (O := O)
    (I := I)
    (J := J)
    (M := B)
    (x := - b)
    (y := a + - c / b)
    (x' := 0)
    (y' := - c / b);
 [ intros H9 H10; try clear unicite_coordonnees; try exact H10
 | auto with geo
 | auto
 | auto ].
RReplace 0 (-0).
rewrite <- H9; ring.
RReplace (- b) (- b + -0).
RReplace a (a + - c / b + - (- c / b)).
apply composantes_vecAB; eauto with geo.
apply not_and_or; auto.
Qed.
Parameter vec_normal : PP -> DR -> Prop.
 
Axiom
  vec_normal_def :
    forall A B C D : PO,
    A <> B ->
    C <> D ->
    vec_normal (vec A B) (droite C D) -> orthogonal (vec A B) (vec C D).
 
Axiom
  vec_normal_def2 :
    forall A B C D : PO,
    A <> B ->
    C <> D ->
    orthogonal (vec A B) (vec C D) -> vec_normal (vec A B) (droite C D).
Require Export angles_droites.
Hint Resolve vec_normal_def vec_normal_def2: geo.
 
Lemma existence_vec_normal :
 forall A B : PO,
 A <> B -> exists C : PO, (exists D : PO, vec_normal (vec C D) (droite A B)).
intros.
soit_orthogonal A B ipattern:D.
exists A; exists D; auto with geo.
Qed.
 
Lemma vec_normal_permute :
 forall A B C D : PO,
 A <> B ->
 C <> D ->
 vec_normal (vec A B) (droite C D) -> vec_normal (vec C D) (droite A B).
intros.
eauto with geo.
Qed.
Hint Immediate vec_normal_permute: geo.
 
Lemma vec_normal_directeur_orthogonaux :
 forall A B C D E F : PO,
 A <> B ->
 C <> D ->
 E <> F ->
 vec_normal (vec C D) (droite A B) ->
 vec_directeur (vec E F) (droite A B) -> orthogonal (vec C D) (vec E F).
intros.
apply vec_normal_def; auto.
elim determinant_nul_colinearite with (A := A) (B := B) (C := E) (D := F);
 [ intros k H4; try clear determinant_nul_colinearite; try exact H4
 | auto
 | auto with geo ].
apply vec_normal_def2; auto.
apply ortho_sym.
rewrite H4; eauto with geo.
Qed.
 
Lemma vec_normal_orthogonal_directeur :
 forall A B C D E F : PO,
 A <> B ->
 C <> D ->
 E <> F ->
 vec_normal (vec C D) (droite A B) ->
 orthogonal (vec C D) (vec E F) -> vec_directeur (vec E F) (droite A B).
intros.
apply paralleles_vec_directeur; auto.
elim
 orthogonal_colineaires
  with (A := C) (B := D) (C := A) (D := B) (E := E) (F := F);
 [ intros k H4; try clear orthogonal_colineaires; try exact H4
 | auto
 | auto
 | auto with geo
 | auto with geo ].
apply colineaires_paralleles with k; auto.
Qed.
 
Lemma vec_directeur_orthogonal_normal :
 forall A B C D E F : PO,
 A <> B ->
 C <> D ->
 E <> F ->
 vec_directeur (vec E F) (droite A B) ->
 orthogonal (vec C D) (vec E F) -> vec_normal (vec C D) (droite A B).
intros.
apply vec_normal_def2; auto.
apply ortho_sym.
elim determinant_nul_colinearite with (A := E) (B := F) (C := A) (D := B);
 [ intros k H4; try clear determinant_nul_colinearite; try exact H4
 | auto
 | auto with geo ].
rewrite H4; auto with geo.
Qed.
 
Lemma paralleles_l_vec_normal :
 forall A B C D E F : PO,
 A <> B ->
 C <> D ->
 E <> F ->
 paralleles (droite A B) (droite E F) ->
 vec_normal (vec A B) (droite C D) -> vec_normal (vec E F) (droite C D).
intros.
elim paralleles_vecteur with (A := E) (B := F) (C := A) (D := B);
 [ intros k H4; try clear paralleles_vecteur | auto | auto | auto with geo ].
apply vec_normal_def2; auto.
rewrite H4; eauto with geo.
Qed.
 
Lemma vec_normal_paralleles_l :
 forall A B C D E F : PO,
 A <> B ->
 C <> D ->
 E <> F ->
 vec_normal (vec A B) (droite C D) ->
 vec_normal (vec E F) (droite C D) -> paralleles (droite A B) (droite E F).
intros.
elim
 orthogonal_colineaires
  with (A := C) (B := D) (C := E) (D := F) (E := A) (F := B);
 [ intros k H4; try clear orthogonal_colineaires; try exact H4
 | auto
 | auto
 | auto with geo
 | auto with geo ].
apply colineaires_paralleles with k; auto.
Qed.
 
Lemma vec_normal_paralleles_r :
 forall A B C D E F : PO,
 A <> B ->
 C <> D ->
 E <> F ->
 vec_normal (vec A B) (droite C D) ->
 vec_normal (vec A B) (droite E F) -> paralleles (droite C D) (droite E F).
intros.
elim
 orthogonal_colineaires
  with (A := A) (B := B) (C := E) (D := F) (E := C) (F := D);
 [ intros k H4; try clear orthogonal_colineaires; try exact H4
 | auto
 | auto
 | auto with geo
 | auto with geo ].
apply colineaires_paralleles with k; auto.
Qed.
 
Lemma paralleles_r_vec_normal :
 forall A B C D E F : PO,
 A <> B ->
 C <> D ->
 E <> F ->
 paralleles (droite C D) (droite E F) ->
 vec_normal (vec A B) (droite C D) -> vec_normal (vec A B) (droite E F).
intros.
elim paralleles_vecteur with (A := E) (B := F) (C := C) (D := D);
 [ intros k H4; try clear paralleles_vecteur | auto | auto | auto with geo ].
apply vec_normal_def2; auto.
apply ortho_sym.
rewrite H4; eauto with geo.
Qed.
 
Lemma vec_normal_calcul :
 forall (A B C D : PO) (x y x0 y0 a b : R),
 A <> B ->
 C <> D ->
 x = abscisse D ->
 y = ordonnee D ->
 x0 = abscisse C ->
 y0 = ordonnee C ->
 a = absvec (vec A B) ->
 b = ordvec (vec A B) ->
 vec_normal (vec A B) (droite C D) -> a * (x + - x0) + b * (y + - y0) = 0.
intros A B C D x y x0 y0 a b H H0 H1 H2 H3 H4 H5 H6 H7; try assumption.
elim existence_representant_vecteur with (A := O) (B := A) (C := B);
 [ intros M H10 ].
elim existence_representant_vecteur with (A := O) (B := C) (C := D);
 [ intros N H20 ].
cut
 (vec C D =
  add_PP (mult_PP (x + - x0) (vec O I)) (mult_PP (y + - y0) (vec O J)));
 intros.
2: apply composantes_vecAB; eauto with geo.
cut (vec A B = add_PP (mult_PP a (vec O I)) (mult_PP b (vec O J)));
 [ intros | auto with geo ].
replace 0 with (scalaire (vec A B) (vec C D)); auto with geo.
rewrite <- H10; rewrite <- H20.
rewrite
 (scalaire_coordonnees (O:=O) (I:=I) (J:=J) (M:=M) (N:=N) (x:=a) (y:=b)
    (x':=x + - x0) (y':=y + - y0)); auto with geo.
rewrite H10; auto.
rewrite H20; auto.
Qed.
 
Lemma equation_droite_orthogonal :
 forall (A B C D : PO) (x y x0 y0 a b : R),
 A <> B ->
 C <> D ->
 x = abscisse D ->
 y = ordonnee D ->
 x0 = abscisse C ->
 y0 = ordonnee C ->
 a = absvec (vec A B) ->
 b = ordvec (vec A B) ->
 orthogonal (vec A B) (vec C D) -> a * (x + - x0) + b * (y + - y0) = 0.
intros.
apply vec_normal_calcul with (1 := H) (2 := H0); auto with geo.
Qed.
 
Lemma orthogonal_equation_cartesienne :
 forall (A B M : PO) (x y : R),
 x = abscisse M ->
 y = ordonnee M ->
 A <> B ->
 orthogonal (vec A B) (vec A M) ->
 exists a : R,
   (exists b : R,
      (exists c : R, a * x + (b * y + c) = 0 /\ ~ (a = 0 /\ b = 0))).
intros A B M x y H20 H30 H0 H1; try assumption.
cut (vec O M = add_PP (mult_PP x (vec O I)) (mult_PP y (vec O J)));
 [ intros H | auto with geo ].
elim composantes_vecteur with (O := O) (I := I) (J := J) (M := A) (N := B);
 [ intros a H2; elim H2; [ intros b H3; try clear H2; try exact H3 ]
 | auto with geo ].
elim existence_coordonnees with (O := O) (I := I) (J := J) (M := A);
 [ intros x0 H2; elim H2; [ intros y0 H4; try clear H2; try exact H4 ]
 | auto with geo ].
cut
 (vec A M =
  add_PP (mult_PP (x + - x0) (vec O I)) (mult_PP (y + - y0) (vec O J)));
 intros.
2: apply composantes_vecAB; eauto with geo.
exists a; exists b; exists (- (a * x0) + - (b * y0)).
split; [ try assumption | idtac ].
discrimine A M.
cut (x = x0 /\ y = y0); intros.
applatit_and.
rewrite H7; rewrite H8; ring.
rewrite H5 in H4.
apply unicite_composantes_vecteur with (2 := H) (3 := H4); auto with geo.
RReplace (a * x + (b * y + (- (a * x0) + - (b * y0))))
 (a * (x + - x0) + b * (y + - y0)).
apply vec_normal_calcul with (1 := H0) (2 := H5); eauto with geo.
contrapose H0.
applatit_and.
apply vecteur_nul_conf.
rewrite H3.
RReplace b (- - b).
rewrite H6; rewrite H7; Ringvec.
Qed.
 
Lemma equation_cartesienne_orthogonal :
 forall (M : PO) (x y a b c : R),
 x = abscisse M ->
 y = ordonnee M ->
 ~ (a = 0 /\ b = 0) ->
 a * x + (b * y + c) = 0 ->
 exists A : _, (exists B : _, A <> B /\ orthogonal (vec A B) (vec A M)).
intros M x y a b c H20 H30 H0 H1; try assumption.
cut (vec O M = add_PP (mult_PP x (vec O I)) (mult_PP y (vec O J)));
 [ intros H | auto with geo ].
cut (a <> 0 \/ b <> 0); intros.
elim H2; intros.
elim
 existence_representant_comb_lin_vecteur
  with (A := O) (B := I) (C := O) (D := J) (a := - c / a) (b := 0);
 [ intros A H4; try clear existence_representant_comb_lin_vecteur;
    try exact H4 ].
elim
 existence_representant_comb_lin_vecteur
  with (A := O) (B := I) (C := O) (D := J) (a := a + - c / a) (b := b);
 [ intros B H6; try clear existence_representant_comb_lin_vecteur;
    try exact H6 ].
exists A; exists B.
cut (vec A B = add_PP (mult_PP a (vec O I)) (mult_PP b (vec O J))); intros.
cut (A <> B); intros.
split; [ try assumption | idtac ].
cut (scalaire (vec A B) (vec A M) = 0); auto with geo.
cut (vec A M = add_PP (mult_PP (x + c / a) (vec O I)) (mult_PP y (vec O J)));
 intros.
elim existence_representant_vecteur with (A := O) (B := A) (C := B);
 [ intros N H21 ].
elim existence_representant_vecteur with (A := O) (B := A) (C := M);
 [ intros P H22 ].
rewrite <- H21; rewrite <- H22.
rewrite
 (scalaire_coordonnees (O:=O) (I:=I) (J:=J) (M:=N) (N:=P) (x:=a) (y:=b)
    (x':=x + c / a) (y':=y)); auto with geo.
rewrite <- H1; auto.
unfold Rdiv in |- *.
RReplace (a * (x + c * / a)) (a * x + c * (a * / a)).
RReplace (a * / a) 1.
ring.
rewrite H21; auto.
rewrite H22; auto.
RReplace (x + c / a) (x + - (- c / a)).
RReplace y (y + -0).
apply composantes_vecAB; eauto with geo.
unfold Rdiv in |- *.
ring.
contrapose H3.
rewrite H7 in H4.
RReplace a (a + - c / a + - (- c / a)).
cut (a + - c / a = - c / a); intros.
rewrite H8.
unfold Rdiv in |- *.
ring.
elim
 unicite_coordonnees
  with
    (O := O)
    (I := I)
    (J := J)
    (M := B)
    (x := a + - c / a)
    (y := b)
    (x' := - c / a)
    (y' := 0);
 [ intros H9 H10; try clear unicite_coordonnees; try exact H9
 | auto with geo
 | auto
 | auto ].
RReplace b (b + -0).
RReplace a (a + - c / a + - (- c / a)).
apply composantes_vecAB; eauto with geo.
elim
 existence_representant_comb_lin_vecteur
  with (A := O) (B := I) (C := O) (D := J) (a := 0) (b := - c / b);
 [ intros A H4; try clear existence_representant_comb_lin_vecteur;
    try exact H4 ].
elim
 existence_representant_comb_lin_vecteur
  with (A := O) (B := I) (C := O) (D := J) (a := a) (b := b + - c / b);
 [ intros B H6; try clear existence_representant_comb_lin_vecteur;
    try exact H6 ].
exists A; exists B.
cut (vec A B = add_PP (mult_PP a (vec O I)) (mult_PP b (vec O J))); intros.
cut (A <> B); intros.
split; [ try assumption | idtac ].
cut (scalaire (vec A B) (vec A M) = 0); auto with geo.
cut (vec A M = add_PP (mult_PP x (vec O I)) (mult_PP (y + c / b) (vec O J)));
 intros.
elim existence_representant_vecteur with (A := O) (B := A) (C := B);
 [ intros N H21 ].
elim existence_representant_vecteur with (A := O) (B := A) (C := M);
 [ intros P H22 ].
rewrite <- H21; rewrite <- H22.
rewrite
 (scalaire_coordonnees (O:=O) (I:=I) (J:=J) (M:=N) (N:=P) (x:=a) (y:=b)
    (x':=x) (y':=y + c / b)); auto with geo.
rewrite <- H1; auto.
unfold Rdiv in |- *.
RReplace (b * (y + c * / b)) (b * y + c * (b * / b)).
RReplace (b * / b) 1.
ring.
rewrite H21; auto.
rewrite H22; auto.
RReplace (y + c / b) (y + - (- c / b)).
RReplace x (x + -0).
apply composantes_vecAB; eauto with geo.
unfold Rdiv in |- *.
ring.
contrapose H3.
rewrite H7 in H4.
RReplace b (b + - c / b + - (- c / b)).
cut (b + - c / b = - c / b); intros.
rewrite H8.
unfold Rdiv in |- *.
ring.
elim
 unicite_coordonnees
  with
    (O := O)
    (I := I)
    (J := J)
    (M := B)
    (x := a)
    (y := b + - c / b)
    (x' := 0)
    (y' := - c / b);
 [ intros H9 H10; try clear unicite_coordonnees; try exact H10
 | auto with geo
 | auto
 | auto ].
RReplace a (a + -0).
RReplace b (b + - c / b + - (- c / b)).
apply composantes_vecAB; eauto with geo.
apply not_and_or; auto.
Qed.