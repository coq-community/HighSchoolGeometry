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


Require Export vecteur.
Set Implicit Arguments.
Unset Strict Implicit.
 
Definition col_vec (A B C D : PO) :=
  exists k : R, vec C D = mult_PP k (vec A B) :>PP.
 
Definition alignes1 (A B C : PO) :=
  exists k : R, cons 1 C = add_PP (cons k A) (cons (1 + - k) B).
 
Lemma colineaire_alignes1 :
 forall (k : R) (A B C : PO), vec A C = mult_PP k (vec A B) -> alignes1 A B C.
unfold alignes1, vec in |- *; intros.
exists (1 + - k); auto.
RingPP2 H.
RingPP.
Qed.
 
Lemma alignes1_colineaire :
 forall A B C : PO, alignes1 A B C -> col_vec A B A C.
unfold alignes1, vec, col_vec in |- *; intros.
elim H; intros k H0; try clear H; try exact H0.
exists (1 + - k); auto.
unfold vec in |- *; rewrite H0.
RingPP.
Qed.
 
Lemma cas_degenere_alignes1 : forall A B C : PO, A <> C -> ~ alignes1 A A C.
unfold alignes1 in |- *; intros.
unfold not in |- *; intros.
elim H0; intros k H1; try clear H0; try exact H1.
apply H.
apply conversion_PP with (a := k + (1 + - k)) (b := 1); auto.
rewrite H1; RingPP.
RReplace (k + (1 + - k)) 1.
discrR.
ring.
Qed.
 
Definition alignes (A B C : PO) := A = B \/ alignes1 A B C.
 
Lemma alignes_trivial : forall A B : PO, alignes A B A.
unfold alignes, alignes1 in |- *; intros.
right; try assumption.
exists 1.
RingPP.
Qed.
 
Lemma alignes_trivial2 : forall A B : PO, alignes A B B.
unfold alignes, alignes1 in |- *; intros.
right; try assumption.
exists 0.
RingPP.
Qed.
 
Lemma alignes_trivial3 : forall A B : PO, alignes A A B.
unfold alignes, alignes1 in |- *; intros.
tauto.
Qed.
Hint Resolve alignes_trivial alignes_trivial2 alignes_trivial3: geo.
 
Lemma existence_point_droite : forall A B : PO, 
exists C, alignes A B C.
Proof.
intros.
exists A.
auto with geo.
Qed.

Lemma non_alignes_expl :
 forall A B C : PO, ~ alignes A B C -> A <> B /\ ~ alignes1 A B C.
unfold alignes in |- *; intros.
intuition.
Qed.
 
Lemma non_alignes_distincts : forall A B C : PO, ~ alignes A B C -> A <> C.
unfold not, alignes, alignes1 in |- *; intros.
apply H.
rewrite H0.
right; exists 1.
RingPP.
Qed.
 
Lemma non_alignes_distincts2 : forall A B C : PO, ~ alignes A B C -> B <> C.
unfold not, alignes, alignes1 in |- *; intros.
apply H.
rewrite H0.
right; exists 0; RingPP.
Qed.
 
Lemma non_alignes_distincts3 : forall A B C : PO, ~ alignes A B C -> A <> B.
unfold alignes in |- *; intros.
intuition.
Qed.
Hint Resolve non_alignes_distincts non_alignes_distincts2
  non_alignes_distincts3: geo.
 
Lemma colineaire_alignes :
 forall (k : R) (A B C : PO), vec A C = mult_PP k (vec A B) -> alignes A B C.
unfold alignes in |- *; intros.
right; try assumption.
apply colineaire_alignes1 with k; auto.
Qed.
Hint Unfold alignes: geo.
 
Ltac hPPalignes H x :=
  elim H; clear H; intros H;
   [ tauto || (try rewrite H; auto with geo) | elim H; clear H; intros x H ].
 
Ltac halignes H k :=
  elim H; clear H; intros H;
   [ tauto || (try rewrite H; auto with geo)
   | elim (alignes1_colineaire H); intros k; intros ].
 
Lemma permute_alignes : forall A B C : PO, alignes A B C -> alignes B A C.
intros.
halignes H ipattern:x.
apply colineaire_alignes with (1 + - x).
VReplace (vec B C) (add_PP (vec B A) (vec A C)).
rewrite H0; Ringvec.
Qed.
Hint Immediate permute_alignes: geo.
 
Lemma alignes_ordre_cycle : forall A B C : PO, alignes A B C -> alignes B C A.
intros.
halignes H ipattern:x.
discrimine B C; auto with geo.
cut (1 + - x <> 0); intros.
apply colineaire_alignes with (/ (1 + - x)).
VReplace (vec B C) (add_PP (vec B A) (vec A C)).
rewrite H0.
Fieldvec (1 + - x).
apply distinct_col_nonun with (2 := H0); auto.
Qed.
 
Lemma alignes_ordre_permute :
 forall A B C : PO, alignes A B C -> alignes A C B.
intros.
halignes H ipattern:x.
discrimine A C; auto with geo.
apply colineaire_alignes with (/ x); auto with geo.
Qed.
Hint Resolve alignes_ordre_permute alignes_ordre_cycle: geo.
 
Lemma alignes_ordre_cycle2 :
 forall A B C : PO, alignes A B C -> alignes C A B.
intros.
apply permute_alignes; auto with geo.
Qed.
Hint Resolve alignes_ordre_cycle2: geo.
 
Lemma alignes_ordre_cycle3 :
 forall A B C : PO, alignes A B C -> alignes C B A.
intros.
apply permute_alignes; auto with geo.
Qed.
Hint Resolve alignes_ordre_cycle3: geo.
 
Lemma non_alignes_permute :
 forall A B C : PO, ~ alignes A B C -> ~ alignes B A C.
intros.
contrapose ipattern:H0.
apply permute_alignes; auto.
Qed.
Hint Resolve non_alignes_permute: geo.
 
Lemma non_alignes_ordre_permute :
 forall A B C : PO, A <> B -> ~ alignes A B C -> ~ alignes A C B.
intros.
contrapose H0.
apply alignes_ordre_permute; auto.
Qed.
Hint Resolve non_alignes_ordre_permute: geo.
 
Lemma non_alignes_ordre_cycle :
 forall A B C : PO, ~ alignes B C A -> ~ alignes A B C.
intros.
contrapose H.
apply alignes_ordre_cycle; auto.
Qed.
Hint Resolve non_alignes_ordre_cycle: geo.
 
Lemma non_alignes_ordre_cycle2 :
 forall A B C : PO, ~ alignes C A B -> ~ alignes A B C.
intros.
contrapose H.
apply alignes_ordre_cycle2; auto.
Qed.
Hint Resolve non_alignes_ordre_cycle2: geo.
 
Lemma non_alignes_ordre_cycle3 :
 forall A B C : PO, ~ alignes C B A -> ~ alignes A B C.
intros.
contrapose H.
apply alignes_ordre_cycle3; auto.
Qed.
Hint Resolve non_alignes_ordre_cycle3: geo.
 
Lemma alignes_trans :
 forall A B C D : PO,
 A <> B :>PO -> alignes A B C -> alignes A B D -> alignes A C D.
intros.
assert (alignes A C B); auto with geo.
halignes H2 ipattern:k.
halignes H1 ipattern:k0.
apply colineaire_alignes with (k0 * k).
rewrite H4; rewrite H3.
Ringvec.
Qed.
 
Lemma alignes_trans2 :
 forall A B C D : PO,
 A <> B -> alignes A B C -> alignes A B D -> alignes B C D.
intros.
assert (alignes B A D); auto with geo.
halignes H2 ipattern:k.
assert (A = B); auto.
tauto.
assert (alignes B C A); auto with geo.
halignes H4 ipattern:k0.
apply colineaire_alignes with (k * k0).
rewrite H3; rewrite H5.
Ringvec.
Qed.
Hint Resolve alignes_trans alignes_trans2: geo.
 
Definition triangle (A B C : PO) : Prop := ~ alignes A B C.
 
Ltac deroule_triangle A B C :=
  match goal with
  | h:(triangle A B C) |- _ =>
      generalize h; unfold triangle in |- *; intros;
       lapply (non_alignes_distincts (A:=A) (B:=B) (C:=C)); 
       auto; intros; lapply (non_alignes_distincts2 (A:=A) (B:=B) (C:=C));
       auto; intros; lapply (non_alignes_distincts3 (A:=A) (B:=B) (C:=C));
       auto; intros
  | h:(~ alignes A B C) |- _ =>
      lapply (non_alignes_distincts (A:=A) (B:=B) (C:=C)); auto; intros;
       lapply (non_alignes_distincts2 (A:=A) (B:=B) (C:=C)); 
       auto; intros; lapply (non_alignes_distincts3 (A:=A) (B:=B) (C:=C));
       auto; intros
  end.
 
Lemma alignes_non_alignes_trans :
 forall A B C D : PO,
 A <> D -> ~ alignes A B C -> alignes A B D -> ~ alignes A D C.
intros.
contrapose H0.
eauto with geo.
Qed.
Hint Resolve alignes_non_alignes_trans: geo.
 
Lemma alignes_non_alignes_trans2 :
 forall A B C D : PO,
 A <> D -> ~ alignes A B C -> alignes A B D -> ~ alignes A C D.
intros.
eauto with geo.
Qed.
 
Lemma alignes_non_alignes_trans3 :
 forall A B C D : PO,
 A <> D -> ~ alignes A B C -> alignes A C D -> ~ alignes A B D.
intros.
contrapose H0.
eauto with geo.
Qed.
Hint Resolve alignes_non_alignes_trans3: geo.
 
Lemma alignes_non_alignes_trans4 :
 forall A B C D : PO,
 A <> D -> ~ alignes A B C -> alignes A C D -> ~ alignes A D B.
intros.
eauto with geo.
Qed.
 
Lemma add_PP_alignes :
 forall (a b : R) (A B C : PO),
 a + b <> 0 -> add_PP (cons a A) (cons b B) = cons (a + b) C -> alignes A B C.
unfold alignes, alignes1, vec in |- *; intros.
right; try assumption.
exists (1 + - (/ (a + b) * b)).
apply mult_PP_regulier with (a + b); auto.
replace (mult_PP (a + b) (cons 1 C)) with (cons (a + b) C);
 [ idtac | RingPP ].
rewrite <- H0.
FieldPP (a + b).
Qed.
 
Lemma triangle_ordre_cycle :
 forall A B C : PO, triangle A B C -> triangle B C A.
unfold triangle in |- *; intros; auto with geo.
Qed.
 
Lemma triangle_ordre_permute :
 forall A B C : PO, triangle A B C -> triangle A C B.
unfold triangle in |- *; intros; auto with geo.
Qed.
Hint Resolve triangle_ordre_cycle triangle_ordre_permute: geo.
 
Lemma triangle_ordre_cycle2 :
 forall A B C : PO, triangle A B C -> triangle C A B.
auto with geo.
Qed.
 
Lemma triangle_ordre_cycle3 :
 forall A B C : PO, triangle A B C -> triangle C B A.
auto with geo.
Qed.
 
Lemma permute_ordre_triangle :
 forall A B C : PO, triangle A B C -> triangle B A C.
auto with geo.
Qed.