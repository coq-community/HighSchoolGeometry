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


Require Export droite_Euler.
Require Export parallelisme_concours.
Require Export orthogonalite_espace.
Require Export transformations_contact.

Ltac DecompEx H P := elim H;intro P;intro;clear H.
Ltac DecompExAnd H P := 
  elim H;intro P;let id:=fresh in 
(intro id;decompose [and] id;clear id;clear H).

Ltac soit_milieu I A B :=
let id1 := fresh in ((assert (id1:exists I, I = milieu A B);
[apply (existence_milieu A B)|DecompEx id1 I])).

Ltac soit_intersection I A B C D :=
let id1 := fresh in ((assert (id1:exists I, I =  pt_intersection (droite A B) (droite C D));
[apply (existence_pt_intersection)|DecompEx id1 I])).

Ltac soit_mediatrice I A B :=
let id1 := fresh in ((assert (id1:exists J, milieu A B <> J /\ mediatrice A B J);
[apply (existence_mediatrice)|DecompExAnd id1 I])).

Ltac soit_perpendiculaire I A B C :=
let id1 := fresh in ((assert (id1:exists D, orthogonal (vec A B) (vec C D));
[apply (existence_perpendiculaire)|DecompEx id1 I])).
Check existence_homothetique.

Ltac soit_image C A B :=
let id1 := fresh in ((assert (id1: exists C, A = milieu B C);
[apply (existence_symetrique_milieu)|DecompEx id1 C])).

Lemma existence_parallele :  forall A B C : PO, A <> B -> 
exists D, paralleles (droite A B) (droite C D).
intros.
soit_milieu M A C.
soit_image D M B.
exists D.
eapply colineaires_paralleles with (k:=-1);auto.

unfold not;intro;subst C.
assert (A=B).
rewrite H2 in H1.
eapply unicite_symetrique;eauto.
auto.

VReplace  (mult_PP (-1) (vec C D)) (vec D C).

assert  (parallelogramme A B C D).

assert  (T:=(caract_milieu_parallelogramme A B C D)).
rewrite H1 in H2.
tauto.
auto.

Qed.

Ltac soit_parallele I A B C :=
let id1 := fresh in ((assert (id1:exists D, paralleles (droite A B) (droite C D));
[apply (existence_parallele)|DecompEx id1 I])).

Ltac soit_point_droite I A B :=
let id1 := fresh in ((assert (id1:exists C, alignes A B C);
[apply (existence_point_droite)|DecompEx id1 I])).

Ltac soit_point_cercle I O A :=
let id1 := fresh in ((assert (id1:exists C, cercle_rayon O A C);
[apply (existence_point_droite)|DecompEx id1 I])).

Ltac soit_centre_cercle_circonscrit O A B C :=
let id1 := fresh in ((assert (id1:exists O, circonscrit O A B C);
[apply (existence_cercle_circonscrit)|DecompEx id1 I])).

(*
existence_intersection_droite_cercle_centre
existence_reflexion_AB
existence_rotation_Ia 
*)