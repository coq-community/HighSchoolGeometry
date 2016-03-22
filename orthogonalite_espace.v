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


Require Export orthogonalite.
Require Export Plan_espace.
Set Implicit Arguments.
Unset Strict Implicit.
Parameter orthogonales : DR -> DR -> Prop.
 
Axiom
  def_orthogonales :
    forall A B C D : PO,
    A <> B ->
    C <> D ->
    orthogonal (vec A B) (vec C D) -> orthogonales (droite A B) (droite C D).
 
Axiom
  def_orthogonales2 :
    forall A B C D : PO,
    A <> B ->
    C <> D ->
    orthogonales (droite A B) (droite C D) -> orthogonal (vec A B) (vec C D).
Parameter perpendiculaires : DR -> DR -> Prop.
 
Axiom
  def_perpendiculaires :
    forall A B C D : PO,
    A <> B ->
    C <> D ->
    coplanaires A B C D ->
    orthogonales (droite A B) (droite C D) ->
    perpendiculaires (droite A B) (droite C D).
 
Axiom
  def_perpendiculaires2 :
    forall A B C D : PO,
    A <> B ->
    C <> D ->
    perpendiculaires (droite A B) (droite C D) ->
    coplanaires A B C D /\ orthogonales (droite A B) (droite C D).
Hint Resolve ortho_somme ortho_combinaison_lineaire def_orthogonales2
  def_orthogonales def_perpendiculaires: geo.
 
Lemma perpendiculaires_orthogonales :
 forall A B C D : PO,
 A <> B ->
 C <> D ->
 perpendiculaires (droite A B) (droite C D) ->
 orthogonales (droite A B) (droite C D).
intros.
elim def_perpendiculaires2 with (A := A) (B := B) (C := C) (D := D);
 [ intros; try exact H3 | auto | auto | auto ].
Qed.
 
Lemma orthogonales_2droites_secantes :
 forall A B C D E F G : PO,
 ~ alignes A B C ->
 D <> E ->
 F <> G ->
 coplanaires A B C F ->
 coplanaires A B C G ->
 orthogonales (droite A B) (droite D E) ->
 orthogonales (droite A C) (droite D E) ->
 orthogonales (droite F G) (droite D E).
intros A B C D E F G H; try assumption.
assert (A <> B); auto with geo.
intros.
apply def_orthogonales; auto.
lapply (def_orthogonales2 (A:=A) (B:=B) (C:=D) (D:=E)); auto; intros.
lapply (def_orthogonales2 (A:=A) (B:=C) (C:=D) (D:=E)); auto; intros.
hcoplanaires H3 ipattern:k ipattern:k'.
hcoplanaires H4 ipattern:k0 ipattern:k'0.
replace (vec F G) with (add_PP (mult_PP (-1) (vec A F)) (vec A G)).
rewrite H4.
rewrite H3.
replace
 (add_PP (mult_PP (-1) (add_PP (mult_PP k (vec A B)) (mult_PP k' (vec A C))))
    (add_PP (mult_PP k0 (vec A B)) (mult_PP k'0 (vec A C)))) with
 (add_PP (mult_PP (-1 * k + k0) (vec A B))
    (mult_PP (-1 * k' + k'0) (vec A C))).
Simplortho.
Ringvec.
Ringvec.
apply non_alignes_distincts with B; auto.
Qed.
Parameter orthogonaux : DR -> PL -> Prop.
 
Axiom
  def_orthogonaux :
    forall A B C D E : PO,
    ~ alignes A B C ->
    D <> E ->
    orthogonales (droite A B) (droite D E) ->
    orthogonales (droite A C) (droite D E) ->
    orthogonaux (droite D E) (plan A B C).
 
Axiom
  def_orthogonaux2 :
    forall A B C D E : PO,
    ~ alignes A B C ->
    D <> E ->
    orthogonaux (droite D E) (plan A B C) ->
    orthogonales (droite A B) (droite D E) /\
    orthogonales (droite A C) (droite D E).
 
Lemma vecteurs_orthogonaux :
 forall A B C D E : PO,
 ~ alignes A B C ->
 D <> E ->
 orthogonal (vec A B) (vec D E) ->
 orthogonal (vec A C) (vec D E) -> orthogonaux (droite D E) (plan A B C).
intros.
deroule_triangle A B C.
apply def_orthogonaux; auto with geo.
Qed.
 
Lemma vecteurs_orthogonaux_rec :
 forall A B C D E : PO,
 ~ alignes A B C ->
 D <> E ->
 orthogonaux (droite D E) (plan A B C) ->
 orthogonal (vec A B) (vec D E) /\ orthogonal (vec A C) (vec D E).
intros.
deroule_triangle A B C.
elim def_orthogonaux2 with (A := A) (B := B) (C := C) (D := D) (E := E);
 [ intros H5 H6; try clear def_orthogonaux2; try exact H6
 | auto
 | auto
 | auto ].
intros.
split; auto with geo.
Qed.
 
Lemma orthogonaux_orthogonales_toute_droite :
 forall A B C D E F G : PO,
 ~ alignes A B C ->
 D <> E ->
 F <> G ->
 coplanaires A B C F ->
 coplanaires A B C G ->
 orthogonaux (droite D E) (plan A B C) ->
 orthogonales (droite F G) (droite D E).
intros.
assert (A <> B); auto with geo.
apply orthogonales_2droites_secantes with (1 := H); auto.
elim def_orthogonaux2 with (A := A) (B := B) (C := C) (D := D) (E := E);
 [ try clear def_orthogonaux2; intros; auto | auto | auto | auto ].
elim def_orthogonaux2 with (A := A) (B := B) (C := C) (D := D) (E := E);
 [ try clear def_orthogonaux2; intros; auto | auto | auto | auto ].
Qed.
 
Lemma orthogonales_toute_droite_orthogonaux :
 forall A B C D E : PO,
 ~ alignes A B C ->
 D <> E ->
 (forall F G : PO,
  F <> G ->
  coplanaires A B C F ->
  coplanaires A B C G -> orthogonales (droite F G) (droite D E)) ->
 orthogonaux (droite D E) (plan A B C).
intros.
assert (A <> B); auto with geo.
apply def_orthogonaux; auto with geo.
apply H1; auto with geo.
apply non_alignes_distincts with B; auto with geo.
Qed.
 
Lemma orthogonaux_perce :
 forall A B C D E : PO,
 ~ alignes A B C ->
 D <> E ->
 orthogonaux (droite D E) (plan A B C) -> perce (droite D E) (plan A B C).
intros.
elim
 position_relative_droite_plan
  with (A := A) (B := B) (C := C) (D := D) (E := E);
 [ intros H3; try clear position_relative_droite_plan; intros
 | intros H3; try clear position_relative_droite_plan; try exact H3
 | auto
 | auto ].
absurd (D = E); auto.
elim para_plan_dr_vecteur with (A := A) (B := B) (C := C) (D := D) (E := E);
 [ intros k H4; elim H4; intros k' H5; try clear H4; try exact H5
 | auto
 | auto
 | auto ].
elim
 vecteurs_orthogonaux_rec with (A := A) (B := B) (C := C) (D := D) (E := E);
 [ try clear vecteurs_orthogonaux_rec; intros | auto | auto | auto ].
apply vecteur_nul_conf.
apply scalaire_non_degenere.
pattern (vec D E) at 1 in |- *; rewrite H5.
cut
 (orthogonal (add_PP (mult_PP k (vec A B)) (mult_PP k' (vec A C))) (vec D E));
 intros.
elim
 existence_representant_comb_lin_vecteur
  with (A := A) (B := B) (C := A) (D := C) (a := k) (b := k'); 
 intros E0 H8; try clear existence_representant_comb_lin_vecteur;
 rewrite <- H8.
rewrite <- H8 in H6.
rewrite (def_orthogonal (A:=A) (B:=E0) (C:=D) (D:=E)); auto.
apply ortho_combinaison_lineaire; auto.
Qed.