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
Set Implicit Arguments.
Unset Strict Implicit.
Parameter projete_orthogonal : PO -> PO -> PO -> PO.
 
Axiom
  def_projete_orthogonal :
    forall A B C H : PO,
    A <> B ->
    alignes A B H ->
    orthogonal (vec A B) (vec H C) -> H = projete_orthogonal A B C.
 
Axiom
  def_projete_orthogonal2 :
    forall A B C H : PO,
    A <> B ->
    H = projete_orthogonal A B C ->
    alignes A B H /\ orthogonal (vec A B) (vec H C).
 
Lemma existence_projete_orthogonal :
 forall A B C : PO, A <> B -> exists H : PO, H = projete_orthogonal A B C.
intros A B C H0; try assumption.
elim
 existence_representant_mult_vecteur
  with
    (A := A)
    (B := A)
    (C := B)
    (k := / scalaire (vec A B) (vec A B) * scalaire (vec A B) (vec A C));
 intros H H1; try clear existence_representant_mult_vecteur.
exists H.
apply def_projete_orthogonal; auto.
apply (colineaire_alignes H1).
apply def_orthogonal2.
cut (scalaire (vec A B) (vec A B) <> 0); intros; auto with geo.
VReplace (vec H C) (add_PP (mult_PP 1 (vec A C)) (mult_PP (-1) (vec A H))).
rewrite H1.
FVReplace
 (mult_PP (-1)
    (mult_PP (/ scalaire (vec A B) (vec A B) * scalaire (vec A B) (vec A C))
       (vec A B)))
 (mult_PP (- (/ scalaire (vec A B) (vec A B) * scalaire (vec A B) (vec A C)))
    (vec A B)) (scalaire (vec A B) (vec A B)).
Simplscal.
field; auto.
Qed.
 
Theorem scalaire_deux_projetes :
 forall A B C H K : PO,
 A <> B ->
 A <> C ->
 H = projete_orthogonal A B C ->
 K = projete_orthogonal A C B ->
 scalaire (vec A B) (vec A C) = scalaire (vec A B) (vec A H) /\
 scalaire (vec A B) (vec A C) = scalaire (vec A K) (vec A C).
intros.
elim (def_projete_orthogonal2 (A:=A) (B:=B) (C:=C) (H:=H)); auto; intros.
elim (def_projete_orthogonal2 (A:=A) (B:=C) (C:=B) (H:=K)); auto; intros.
split; [ try assumption | idtac ].
apply scalaire_avec_projete; auto.
rewrite scalaire_sym.
rewrite (scalaire_sym A K A C).
apply scalaire_avec_projete; auto.
Qed.
 
Ltac soit_projete A B C H :=
  elim (existence_projete_orthogonal (A:=A) (B:=B) C);
   [ intros H; intros | auto ];
   elim (def_projete_orthogonal2 (A:=A) (B:=B) (C:=C) (H:=H)); 
   auto; intros.
 
Lemma existence_perpendiculaire :
 forall A B C : PO, A <> B -> exists D : PO, orthogonal (vec A B) (vec C D).
intros A B C H0; try assumption.
soit_projete A B C ipattern:H.
exists H.
auto with geo.
Qed.
 
Lemma projete_axe :
 forall A B M H : PO,
 A <> B :>PO ->
 H = projete_orthogonal A B M :>PO -> alignes A B M -> H = M :>PO.
intros.
elim (def_projete_orthogonal2 (A:=A) (B:=B) (C:=M) (H:=H)); auto; intros.
apply (unicite_projete_orthogonal (A:=A) (B:=B) (C:=M) (H:=H) (H':=M)); auto.
VReplace (vec M M) zero.
auto with geo.
Qed.
 
Lemma projete_non_axe :
 forall A B M H : PO,
 A <> B :>PO ->
 H = projete_orthogonal A B M :>PO -> ~ alignes A B M -> M <> H :>PO.
intros.
elim (def_projete_orthogonal2 (A:=A) (B:=B) (C:=M) (H:=H)); auto; intros.
red in |- *; intros; apply H2.
rewrite H5; auto.
Qed.