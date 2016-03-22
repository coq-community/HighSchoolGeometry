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


Require Export coplanarite.
Require Export barycentre.
Set Implicit Arguments.
Unset Strict Implicit.
 
Axiom geometrie_plane : forall A B C D : PO, coplanaires A B C D.
Hint Resolve geometrie_plane: geo.
 
Definition repere (O I J : PO) := triangle O I J.
 
Lemma existence_coordonnees :
 forall O I J M : PO,
 repere O I J ->
 exists x : R,
   (exists y : R,
      vec O M = add_PP (mult_PP x (vec O I)) (mult_PP y (vec O J))).
unfold repere, triangle in |- *; intros.
assert (coplanaires O I J M); auto with geo.
hcoplanaires H0 ipattern:k ipattern:k'.
exists k; exists k'; auto.
Qed.
 
Lemma unicite_coordonnees :
 forall (O I J M : PO) (x y x' y' : R),
 repere O I J ->
 vec O M = add_PP (mult_PP x (vec O I)) (mult_PP y (vec O J)) ->
 vec O M = add_PP (mult_PP x' (vec O I)) (mult_PP y' (vec O J)) ->
 x = x' /\ y = y'.
unfold vec, repere in |- *; intros.
deroule_triangle O I J.
cut
 (cons 1 M = add_PP (add_PP (cons x I) (cons y J)) (cons (1 + - (x + y)) O));
 intros.
apply unicite_coor_bar2 with (2 := H6); auto.
auto with geo.
RingPP2 H1.
RingPP.
RingPP2 H0.
RingPP.
Qed.
 
Lemma composantes_vecteur :
 forall O I J M N : PO,
 repere O I J ->
 exists x : R,
   (exists y : R,
      vec M N = add_PP (mult_PP x (vec O I)) (mult_PP y (vec O J))).
unfold repere, triangle in |- *; intros.
assert (coplanaires O I J M); auto with geo.
hcoplanaires H0 ipattern:k ipattern:k'.
assert (coplanaires O I J N); auto with geo.
hcoplanaires H1 ipattern:k0 ipattern:k'0.
replace (vec M N) with (add_PP (vec O N) (mult_PP (-1) (vec O M))).
rewrite H1; rewrite H0.
exists (k0 + -1 * k); exists (k'0 + -1 * k').
Ringvec.
Ringvec.
Qed.
Parameter abscisse : PO -> R.
Parameter ordonnee : PO -> R.
 
Axiom
  abscisse_def :
    forall (O I J M : PO) (x y : R),
    repere O I J ->
    vec O M = add_PP (mult_PP x (vec O I)) (mult_PP y (vec O J)) :>PP ->
    x = abscisse M.
 
Axiom
  ordonnee_def :
    forall (O I J M : PO) (x y : R),
    repere O I J ->
    vec O M = add_PP (mult_PP x (vec O I)) (mult_PP y (vec O J)) :>PP ->
    y = ordonnee M.
 
Axiom
  cart_def :
    forall (O I J M : PO) (x y : R),
    repere O I J ->
    x = abscisse M ->
    y = ordonnee M ->
    vec O M = add_PP (mult_PP x (vec O I)) (mult_PP y (vec O J)) :>PP.
 
Lemma composantes_vecAB :
 forall (a1 a2 b1 b2 : R) (O I J A B : PO),
 repere O I J ->
 a1 = abscisse A ->
 a2 = ordonnee A ->
 b1 = abscisse B ->
 b2 = ordonnee B ->
 vec A B =
 add_PP (mult_PP (b1 + - a1) (vec O I)) (mult_PP (b2 + - a2) (vec O J)) :>PP.
intros.
generalize (cart_def (O:=O) (I:=I) (J:=J) (M:=A) (x:=a1) (y:=a2)); intros.
generalize (cart_def (O:=O) (I:=I) (J:=J) (M:=B) (x:=b1) (y:=b2)); intros.
replace (vec A B) with (add_PP (vec O B) (mult_PP (-1) (vec O A)));
 [ idtac | Ringvec ].
rewrite H4; auto.
rewrite H5; auto.
Ringvec.
Qed.
Parameter absvec : PP -> R.
Parameter ordvec : PP -> R.
 
Axiom
  absvec_def :
    forall (a b : R) (O I J M N : PO),
    repere O I J ->
    vec M N = add_PP (mult_PP a (vec O I)) (mult_PP b (vec O J)) :>PP ->
    a = absvec (vec M N).
 
Axiom
  ordvec_def :
    forall (a b : R) (O I J M N : PO),
    repere O I J ->
    vec M N = add_PP (mult_PP a (vec O I)) (mult_PP b (vec O J)) :>PP ->
    b = ordvec (vec M N).
 
Axiom
  cartvec_def :
    forall (a b : R) (O I J M N : PO),
    repere O I J ->
    a = absvec (vec M N) ->
    b = ordvec (vec M N) ->
    vec M N = add_PP (mult_PP a (vec O I)) (mult_PP b (vec O J)) :>PP.
 
Lemma unicite_composantes_vecteur :
 forall (a1 a2 b1 b2 : R) (O I J A B : PO),
 repere O I J ->
 vec A B = add_PP (mult_PP a1 (vec O I)) (mult_PP a2 (vec O J)) :>PP ->
 vec A B = add_PP (mult_PP b1 (vec O I)) (mult_PP b2 (vec O J)) :>PP ->
 a1 = b1 :>R /\ a2 = b2 :>R.
intros.
elim existence_representant_vecteur with (A := O) (B := A) (C := B);
 [ intros D H2; try clear existence_representant_vecteur; try exact H2 ].
rewrite <- H2 in H0.
rewrite <- H2 in H1.
apply
 (unicite_coordonnees (O:=O) (I:=I) (J:=J) (M:=D) (x:=a1) (y:=a2) (x':=b1)
    (y':=b2)); auto.
Qed.
 
Lemma cartvec_AB :
 forall (a1 a2 b1 b2 : R) (O I J A B : PO),
 repere O I J ->
 a1 = abscisse A :>R ->
 a2 = ordonnee A :>R ->
 b1 = abscisse B :>R ->
 b2 = ordonnee B :>R ->
 b1 + - a1 = absvec (vec A B) :>R /\ b2 + - a2 = ordvec (vec A B) :>R.
intros.
apply
 (unicite_composantes_vecteur (a1:=b1 + - a1) (a2:=
    b2 + - a2) (b1:=absvec (vec A B)) (b2:=ordvec (vec A B)) (O:=O) (I:=I)
    (J:=J) (A:=A) (B:=B)); auto.
apply composantes_vecAB; auto.
apply cartvec_def; auto.
Qed.
Hint Resolve abscisse_def ordonnee_def cartvec_AB unicite_composantes_vecteur
  absvec_def ordvec_def: geo.
 
Lemma absvec_abscisse :
 forall O I J M : PO, repere O I J -> absvec (vec O M) = abscisse M.
intros.
elim existence_coordonnees with (O := O) (I := I) (J := J) (M := M);
 [ intros x H0; elim H0; [ intros y H1; try clear H0; try exact H1 ] | auto ].
rewrite <- (absvec_def H H1); eauto with geo.
Qed.
 
Lemma ordvec_ordonnee :
 forall O I J M : PO, repere O I J -> ordvec (vec O M) = ordonnee M.
intros.
elim existence_coordonnees with (O := O) (I := I) (J := J) (M := M);
 [ intros x H0; elim H0; [ intros y H1; try clear H0; try exact H1 ] | auto ].
rewrite <- (ordvec_def H H1); eauto with geo.
Qed.