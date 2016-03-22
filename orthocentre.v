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


Require Export projection_orthogonale.
Require Export angles_droites.
Set Implicit Arguments.
Unset Strict Implicit.
 
Lemma deux_hauteurs_trois :
 forall A B C H : PO,
 orthogonal (vec H A) (vec B C) ->
 orthogonal (vec H B) (vec A C) -> orthogonal (vec H C) (vec A B).
intros.
apply def_orthogonal2.
replace (vec H C) with (add_PP (vec H A) (vec A C)) by Ringvec.
lapply (def_orthogonal (A:=H) (B:=A) (C:=B) (D:=C)); auto; intros.
lapply (def_orthogonal (A:=H) (B:=B) (C:=A) (D:=C)); auto; intros.
Simplscal.
replace (scalaire (vec H A) (vec A B)) with (scalaire (vec H A) (vec A C)).
replace (scalaire (vec H A) (vec A C) + scalaire (vec A C) (vec A B))  with
 (scalaire (add_PP (vec H A) (vec A B)) (vec A C)).
replace (add_PP (vec H A) (vec A B)) with (vec H B); auto.
Ringvec.
Simplscal.
rewrite (scalaire_sym A B A C); auto.
replace (vec A B) with (add_PP (vec A C) (vec C B)).
Simplscal.
replace (vec C B) with (mult_PP (-1) (vec B C)).
Simplscal.
rewrite H2; ring.
Ringvec.
Ringvec.
Qed.
 
Lemma triangle_rectangle_une_fois :
 forall A B C : PO,
 triangle A B C ->
 orthogonal (vec A B) (vec A C) ->
 ~ orthogonal (vec A B) (vec B C) /\ ~ orthogonal (vec A C) (vec C B).
intros.
cut (triangle A C B); intros; auto with geo.
deroule_triangle A C B.
split; [ try assumption | idtac ].
red in |- *; intros; apply H2.
elim orthogonal_paralleles with (A := A) (B := B) (C := C) (E := B) (F := C);
 [ intros k H7; try exact H7
 | auto with geo
 | auto with geo
 | auto with geo
 | auto with geo ].
apply colineaire_alignes with (- k + 1); auto.
replace (vec A B) with (add_PP (mult_PP (-1) (vec B C)) (vec A C));
 [ idtac | Ringvec ].
rewrite H7; Ringvec.
deroule_triangle A B C.
red in |- *; intros; apply H6.
elim orthogonal_paralleles with (A := A) (B := C) (C := B) (E := C) (F := B);
 [ intros k H11; try exact H11
 | auto with geo
 | auto with geo
 | auto with geo
 | auto with geo ].
apply colineaire_alignes with (- k + 1); auto.
replace (vec A C) with (add_PP (mult_PP (-1) (vec C B)) (vec A B));
 [ idtac | Ringvec ].
rewrite H11; Ringvec.
Qed.
 
Lemma triangle_distincts_pied_hauteur :
 forall A B C H : PO,
 triangle A B C -> H = projete_orthogonal A B C -> C <> H :>PO.
intros.
deroule_triangle A B C.
elim (def_projete_orthogonal2 (A:=A) (B:=B) (C:=C) (H:=H)); auto; intros.
red in |- *; intros; apply H2.
rewrite H8; auto.
Qed.
Require Export Droite_espace.
 
Lemma triangle_hauteurs_secantes :
 forall A B C H K : PO,
 triangle A B C ->
 H = projete_orthogonal A B C ->
 K = projete_orthogonal A C B -> concours (droite C H) (droite B K).
intros.
deroule_triangle A B C.
elim (def_projete_orthogonal2 (A:=A) (B:=B) (C:=C) (H:=H)); auto; intros.
elim (def_projete_orthogonal2 (A:=A) (B:=C) (C:=B) (H:=K)); auto; intros.
cut (C <> H); intros.
cut (B <> K); intros.
elim (position_relative_droites_coplanaires (A:=C) (B:=H) (C:=B) (D:=K));
 auto with geo; intros.
absurd (paralleles (droite C H) (droite B K)); auto.
apply angle_non_paralleles; auto.
rewrite
 (angles_droites_orthogonales (A:=A) (B:=C) (C:=A) (D:=B) (E:=B) (F:=K)
    (G:=C) (I:=H)); auto with geo.
apply (triangle_distincts_pied_hauteur (A:=A) (B:=C) (C:=B) (H:=K));
 auto with geo.
apply (triangle_distincts_pied_hauteur (A:=A) (B:=B) (C:=C) (H:=H));
 auto with geo.
Qed.
 
Lemma aux :
 forall A B C H K : PO,
 triangle A B C ->
 H = projete_orthogonal A B C :>PO ->
 K = projete_orthogonal A C B :>PO -> ~ alignes C H B \/ ~ alignes C H K.
intros.
deroule_triangle A B C.
elim (def_projete_orthogonal2 (A:=A) (B:=B) (C:=C) (H:=H)); auto; intros.
elim (def_projete_orthogonal2 (A:=A) (B:=C) (C:=B) (H:=K)); auto; intros.
cut (C <> H); intros.
cut (B <> K); intros.
elim (classic (orthogonal (vec B A) (vec B C))); intros.
cut (H = B); intros.
right; try assumption.
rewrite H14.
cut (~ orthogonal (vec A C) (vec B C)); intros.
red in |- *; intros; apply H15.
assert (alignes B K C); auto with geo.
halignes H17 ipattern:k.
apply ortho_sym.
rewrite H18.
Simplortho.
elim triangle_rectangle_une_fois with (A := B) (B := A) (C := C);
 [ try clear triangle_rectangle_une_fois; intros | auto with geo | auto ].
red in |- *; intros; apply H16.
auto with geo.
apply unicite_projete_orthogonal with (2 := H7) (3 := H8); auto with geo.
left.
red in |- *; intros; apply H13.
halignes H14 ipattern:k.
apply ortho_sym.
replace (vec B C) with (mult_PP (-1) (vec C B)); [ idtac | Ringvec ].
rewrite H15.
replace (mult_PP (-1) (mult_PP k (vec C H))) with (mult_PP k (vec H C));
 [ idtac | Ringvec ].
Simplortho.
apply (triangle_distincts_pied_hauteur (A:=A) (B:=C) (C:=B) (H:=K));
 auto with geo.
apply (triangle_distincts_pied_hauteur (A:=A) (B:=B) (C:=C) (H:=H)); auto.
Qed.
 
Lemma existence_intersection_deux_hauteurs_triangle :
 forall A B C H K : PO,
 triangle A B C ->
 H = projete_orthogonal A B C :>PO ->
 K = projete_orthogonal A C B :>PO ->
 ex (fun I : PO => I = pt_intersection (droite C H) (droite B K) :>PO).
intros.
cut (~ alignes C H B \/ ~ alignes C H K); intros.
apply existence_pt_intersection; auto.
apply (triangle_distincts_pied_hauteur (A:=A) (B:=B) (C:=C) (H:=H)); auto.
apply (triangle_distincts_pied_hauteur (A:=A) (B:=C) (C:=B) (H:=K));
 auto with geo.
apply triangle_hauteurs_secantes with (A := A); auto.
apply aux with (A := A); auto.
Qed.
Parameter orthocentre : PO -> PO -> PO -> PO.
 
Axiom
  orthocentre_def :
    forall A B C H : PO,
    orthogonal (vec H A) (vec B C) ->
    orthogonal (vec H B) (vec A C) ->
    orthogonal (vec H C) (vec A B) -> H = orthocentre A B C :>PO.
 
Axiom
  orthocentre_def2 :
    forall A B C H : PO,
    H = orthocentre A B C :>PO ->
    (orthogonal (vec H A) (vec B C) /\ orthogonal (vec H B) (vec A C)) /\
    orthogonal (vec H C) (vec A B).
 
Lemma orthocentre_ordre :
 forall A B C H : PO,
 triangle A B C -> H = orthocentre A B C :>PO -> H = orthocentre C A B :>PO.
intros.
elim orthocentre_def2 with (A := A) (B := B) (C := C) (H := H);
 [ intros | auto ].
elim H2; intros H4 H5; try clear H2; try exact H5.
apply orthocentre_def; auto with geo.
Qed.
 
Lemma orthocentre_permute :
 forall A B C H : PO,
 triangle A B C -> H = orthocentre A B C :>PO -> H = orthocentre B A C :>PO.
intros.
elim orthocentre_def2 with (A := A) (B := B) (C := C) (H := H);
 [ intros | auto ].
elim H2; intros H4 H5; try clear H2; try exact H5.
apply orthocentre_def; auto with geo.
Qed.
Hint Immediate orthocentre_ordre orthocentre_permute: geo.
 
Lemma orthocentre_triangle_rectangle :
 forall A B C : PO,
 triangle A B C ->
 orthogonal (vec A B) (vec B C) -> B = orthocentre A B C :>PO.
intros.
apply orthocentre_def; auto with geo.
replace (vec B B) with zero; auto with geo.
Ringvec.
Qed.
 
Lemma intersection_deux_hauteurs_orthocentre_triangle :
 forall A B C H K I : PO,
 triangle A B C ->
 H = projete_orthogonal A B C :>PO ->
 K = projete_orthogonal A C B :>PO ->
 I = pt_intersection (droite C H) (droite B K) :>PO ->
 I = orthocentre A B C :>PO.
intros A B C H K I H0 H2 H3 H4.
deroule_triangle A B C.
elim (def_projete_orthogonal2 (A:=A) (B:=B) (C:=C) (H:=H)); auto; intros.
elim (def_projete_orthogonal2 (A:=A) (B:=C) (C:=B) (H:=K)); auto; intros.
cut (C <> H); intros.
cut (B <> K); intros.
cut (~ alignes C H B \/ ~ alignes C H K); intros.
elim def_pt_intersection2 with (A := C) (B := H) (C := B) (D := K) (I := I);
 [ try clear def_pt_intersection2; intros | auto | auto | auto | auto ].
halignes H16 ipattern:k.
halignes H15 ipattern:k0.
cut (orthogonal (vec I B) (vec A C) /\ orthogonal (vec I C) (vec A B));
 intros.
elim H19; intros H20 H21; try clear H19; try exact H21.
apply orthocentre_def; auto.
apply deux_hauteurs_trois.
auto with geo.
auto with geo.
split; [ idtac | try assumption ].
replace (vec I B) with (mult_PP (-1) (vec B I)).
rewrite H17.
replace (mult_PP (-1) (mult_PP k (vec B K))) with (mult_PP k (vec K B)).
Simplortho.
Ringvec.
Ringvec.
replace (vec I C) with (mult_PP (-1) (vec C I)).
rewrite H18.
replace (mult_PP (-1) (mult_PP k0 (vec C H))) with (mult_PP k0 (vec H C)).
Simplortho.
Ringvec.
Ringvec.
apply aux with (A := A); auto.
apply (triangle_distincts_pied_hauteur (A:=A) (B:=C) (C:=B) (H:=K));
 auto with geo.
apply (triangle_distincts_pied_hauteur (A:=A) (B:=B) (C:=C) (H:=H)); auto.
Qed.
 
Lemma orthocentre_intersection_hauteurs :
 forall A B C H K I : PO,
 triangle A B C ->
 H = projete_orthogonal A B C :>PO ->
 K = projete_orthogonal A C B :>PO ->
 I = orthocentre A B C :>PO ->
 I = pt_intersection (droite C H) (droite B K) :>PO.
intros.
elim orthocentre_def2 with (A := A) (B := B) (C := C) (H := I);
 [ intros | auto ].
elim H4; intros H6 H7; try clear H4; try exact H7.
cut (~ alignes C H B \/ ~ alignes C H K); intros.
deroule_triangle A B C.
elim (def_projete_orthogonal2 (A:=A) (B:=B) (C:=C) (H:=H)); auto; intros.
elim (def_projete_orthogonal2 (A:=A) (B:=C) (C:=B) (H:=K)); auto; intros.
cut (C <> H); intros.
cut (B <> K); intros.
apply def_pt_intersection; auto.
elim
 orthogonal_colineaires
  with (A := A) (B := B) (C := H) (D := C) (E := C) (F := I);
 [ intros k H18; try exact H18
 | auto with geo
 | auto with geo
 | auto with geo
 | auto with geo ].
apply colineaire_alignes with (- k); auto.
rewrite H18; Ringvec.
elim
 orthogonal_colineaires
  with (A := A) (B := C) (C := K) (D := B) (E := B) (F := I);
 [ intros k H18; try exact H18
 | auto with geo
 | auto with geo
 | auto with geo
 | auto with geo ].
apply colineaire_alignes with (- k); auto.
rewrite H18; Ringvec.
apply (triangle_distincts_pied_hauteur (A:=A) (B:=C) (C:=B) (H:=K));
 auto with geo.
apply (triangle_distincts_pied_hauteur (A:=A) (B:=B) (C:=C) (H:=H)); auto.
apply aux with (A := A); auto.
Qed.
