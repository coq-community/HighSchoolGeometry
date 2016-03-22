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


Require Export complexes_similitudes.
Set Implicit Arguments.
Unset Strict Implicit.
 
Lemma equation_equiv :
 forall a b z : C,
 z = Cplus (Cmult a z) b -> Cmult (Cplus oneC (Copp a)) z = b.
intros.
replace b with (Cplus z (Copp (Cmult a z))).
ring.
pattern z at 1 in |- *.
rewrite H; ring.
Qed.
 
Lemma equation_equiv2 :
 forall a b z : C,
 Cmult (Cplus oneC (Copp a)) z = b -> z = Cplus (Cmult a z) b.
intros.
rewrite <- H; ring.
Qed.
 
Lemma nonzero_amoins_un :
 forall a : C, a <> oneC -> Cplus oneC (Copp a) <> zeroC.
intros.
red in |- *; intros; apply H.
replace a with (Cplus a zeroC); [ idtac | ring ].
rewrite <- H0; ring.
Qed.
Hint Resolve nonzero_amoins_un: geo.
 
Lemma existence_solution_equation :
 forall a b : C, a <> oneC -> exists z : C, z = Cplus (Cmult a z) b.
intros.
cut (Cplus oneC (Copp a) <> zeroC); intros; auto with geo.
cut (exists z : C, Cmult (Cplus oneC (Copp a)) z = b); intros.
elim H1; intros z H2; try clear H1; try exact H2.
exists z.
apply equation_equiv2; auto.
exists (Cmult (Cinv (Cplus oneC (Copp a))) b).
replace (Cmult (Cplus oneC (Copp a)) (Cmult (Cinv (Cplus oneC (Copp a))) b))
 with (Cmult (Cmult (Cplus oneC (Copp a)) (Cinv (Cplus oneC (Copp a)))) b);
 [ idtac | ring ].
rewrite Cinv_def; auto.
ring.
Qed.
 
Lemma unicite_solution_equation :
 forall a b z z' : C,
 a <> oneC -> z = Cplus (Cmult a z) b -> z' = Cplus (Cmult a z') b -> z = z'.
intros.
cut (Cplus z (Copp z') = zeroC); intros.
replace z with (Cplus (Cplus z (Copp z')) z'); [ idtac | ring ].
rewrite H2; ring.
apply Cintegre with (z := Cplus oneC (Copp a)); auto with geo.
cut (Cmult (Cplus oneC (Copp a)) z = b); intros.
2: apply equation_equiv; auto.
cut (Cmult (Cplus oneC (Copp a)) z' = b); intros.
2: apply equation_equiv; auto.
replace zeroC with (Cplus b (Copp b)); [ idtac | ring ].
pattern b at 1 in |- *.
rewrite <- H2.
rewrite <- H3; ring.
Qed.
 
Lemma existence_point_fixe_complexe :
 forall (a b : C) (f : C -> C),
 a <> oneC ->
 (forall z : C, f z = Cplus (Cmult a z) b) -> exists j : C, f j = j.
intros.
elim existence_solution_equation with (a := a) (b := b);
 [ intros z0 H1; try clear existence_solution_equation; try exact H1 | auto ].
exists z0.
rewrite (H0 z0).
rewrite <- H1; auto.
Qed.
Parameter transforme : (C -> C) -> PO -> PO.
 
Axiom
  transforme_def :
    forall (f : C -> C) (M : PO), transforme f M = image (f (affixe M)).
 
Lemma image_affixe : forall M : PO, image (affixe M) = M.
intros.
elim existence_affixe_point with (M := M); intros z H;
 try clear existence_affixe_point; try exact H.
rewrite <- H; symmetry  in |- *; auto with geo.
Qed.
 
Lemma affixe_image : forall z : C, affixe (image z) = z.
intros.
elim existence_image_complexe with (z := z); intros M H;
 try clear existence_image_complexe; try exact H.
rewrite <- H; symmetry  in |- *; auto with geo.
Qed.
Hint Resolve image_affixe affixe_image: geo.
 
Lemma transforme_image :
 forall (f : C -> C) (z : C), transforme f (image z) = image (f z).
intros.
rewrite transforme_def; rewrite affixe_image; auto.
Qed.
 
Lemma affixe_transforme :
 forall (f : C -> C) (M : PO), affixe (transforme f M) = f (affixe M).
intros.
rewrite transforme_def; auto with geo.
Qed.
 
Lemma f_fonction_transforme :
 forall (f : C -> C) (z : C), f z = affixe (transforme f (image z)).
intros.
rewrite affixe_transforme; rewrite affixe_image; auto with geo.
Qed.
Parameters (a : C) (b : C).
Parameter f : C -> C.
Hypothesis f_def : forall z : C, f z = Cplus (Cmult a z) b.
Parameter g : PO -> PO.
Hypothesis g_def : forall M : PO, g M = transforme f M.
 
Lemma explicitation :
 forall (z z' : C) (M M' : PO),
 z = affixe M -> z' = affixe M' -> M' = g M -> z' = Cplus (Cmult a z) b.
intros.
rewrite H0; rewrite H1; rewrite g_def.
rewrite affixe_transforme; rewrite <- H; rewrite f_def; auto.
Qed.
 
Lemma existence_point_fixe_g : a <> oneC -> exists J : PO, g J = J.
intros.
elim existence_point_fixe_complexe with (a := a) (b := b) (f := f);
 [ intros j H0; try clear existence_point_fixe_complexe; try exact H0
 | auto
 | auto ].
exists (image j).
rewrite g_def; rewrite transforme_image; rewrite H0; auto.
try exact f_def.
Qed.
 
Lemma equation_solution :
 forall z z' j : C,
 z' = f z -> f j = j -> Cplus z' (Copp j) = Cmult a (Cplus z (Copp j)).
intros z z' j; try assumption.
repeat rewrite f_def; intros.
rewrite H.
pattern j at 1 in |- *.
rewrite <- H0; ring.
Qed.
 
Lemma point_fixe_gf : forall M : PO, g M = M -> f (affixe M) = affixe M.
intros M; try assumption.
repeat rewrite g_def; intros.
pattern M at 2 in |- *.
rewrite <- H.
rewrite affixe_transforme; auto.
Qed.
 
Lemma un_module_a_rotation :
 forall x : R,
 a <> oneC ->
 a = cons_pol 1 x -> exists J : PO, (forall M : PO, g M = rotation J x M).
intros.
elim existence_point_fixe_g;
 [ intros J H1; try clear existence_point_fixe_g; try exact H1 | auto ].
exists J; intros.
elim existence_affixe_point with (M := M); intros z H2;
 try clear existence_affixe_point; try exact H2.
elim existence_affixe_point with (M := g M); intros z'; intros; try exact H2.
apply
 (complexe_rotation (a:=x) (j:=affixe J) (z:=z) (z':=z') (J:=J) (M:=M)
    (M':=g M)); auto.
rewrite <- H0.
cut (f (affixe J) = affixe J); intros.
apply (equation_solution (z:=z) (z':=z') (j:=affixe J)); auto with geo.
rewrite H3; rewrite g_def; rewrite H2; rewrite affixe_transforme; auto.
apply point_fixe_gf; auto.
Qed.
 
Lemma a_oneC_translation :
 a = oneC -> exists A : PO, (forall M : PO, g M = translation O A M).
intros.
elim existence_image_complexe with (z := b); intros A H1;
 try clear existence_image_complexe; try exact H1.
exists A; intros.
elim existence_affixe_point with (M := M); intros z H2;
 try clear existence_affixe_point; try exact H2.
elim existence_affixe_point with (M := g M); intros z'; intros; try exact H2.
apply (complexe_translation (a:=b) (z:=z) (z':=z') (A:=A) (M:=M) (M':=g M));
 auto with geo.
rewrite H0; rewrite g_def; rewrite H2; rewrite affixe_transforme;
 rewrite f_def; rewrite H; ring.
Qed.
 
Lemma un_module_a_deplacement :
 module a = 1 ->
 (exists A : PO, (forall M : PO, g M = translation O A M)) \/
 (exists J : PO, (exists x : R, (forall M : PO, g M = rotation J x M))).
intros.
elim (classic (a = oneC)); intros.
left; try assumption.
apply a_oneC_translation; auto.
right; try assumption.
cut (a <> zeroC).
intros H20.
elim existence_forme_polaire with (z := a);
 [ intros r H1; elim H1; intros x H2; elim H2; intros H3 H4; try clear H2 H1;
    try exact H4
 | auto with geo ].
elim un_module_a_rotation with (x := x);
 [ intros J H1; try clear un_module_a_rotation; try exact H1
 | auto with geo
 | auto with geo ].
exists J; exists x; auto with geo.
apply nonzero_module.
rewrite H; discrR.
Qed.
 
Lemma cas_a_reel_homothetie :
 forall x : R,
 a <> oneC ->
 a = Rinj x -> ex (fun J : PO => forall M : PO, g M = homothetie x J M).
intros.
elim existence_point_fixe_g;
 [ intros J H1; try clear existence_point_fixe_g; try exact H1 | auto ].
exists J; intros.
elim existence_affixe_point with (M := M); intros z H2;
 try clear existence_affixe_point; try exact H2.
elim existence_affixe_point with (M := g M); intros z'; intros; try exact H2.
apply
 (complexe_homothetie (k:=x) (j:=affixe J) (z:=z) (z':=z') (J:=J) (M:=M)
    (M':=g M)); auto.
rewrite <- H0.
cut (f (affixe J) = affixe J); intros.
apply (equation_solution (z:=z) (z':=z') (j:=affixe J)); auto.
rewrite H3; rewrite g_def; rewrite H2; rewrite affixe_transforme; auto.
apply point_fixe_gf; auto.
Qed.
 
Lemma cas_a_nonzero_nonone :
 forall r x : R,
 r > 0 ->
 a <> oneC ->
 a = cons_pol r x ->
 ex (fun J : PO => forall M : PO, g M = similitude J r x M).
intros r x H H20 H0; try assumption.
elim existence_point_fixe_g;
 [ intros J H1; try clear existence_point_fixe_g; try exact H1 | auto ].
exists J; intros.
elim existence_affixe_point with (M := M); intros z H2;
 try clear existence_affixe_point; try exact H2.
elim existence_affixe_point with (M := g M); intros z'; intros; try exact H2.
cut (f (affixe J) = affixe J); intros.
apply
 (complexe_similitude (k:=r) (a:=x) (j:=affixe J) (z:=z) (z':=z') (J:=J)
    (M:=M) (M':=g M)); auto.
rewrite <- H0.
apply (equation_solution (z:=z) (z':=z') (j:=affixe J)); auto.
rewrite H3; rewrite g_def; rewrite H2; rewrite affixe_transforme; auto.
apply point_fixe_gf; auto.
Qed.
 
Theorem cas_general_deplacement_similitude :
 a <> zeroC ->
 (ex (fun A : PO => forall M : PO, g M = translation O A M) \/
  ex (fun J : PO => ex (fun x : R => forall M : PO, g M = rotation J x M))) \/
 (exists r : R,
    (exists x : R, (exists J : PO, (forall M : PO, g M = similitude J r x M)))).
intros.
elim existence_forme_polaire with (z := a);
 [ intros r H0; elim H0; intros x H1; elim H1; intros H2 H3; try clear H1 H0;
    try exact H3
 | auto with geo ].
cut (a = cons_pol r x); intros; auto with geo.
elim (classic (module a = 1)); intros.
left; try assumption.
apply un_module_a_deplacement; auto with geo.
right; try assumption.
exists r; exists x.
apply cas_a_nonzero_nonone; auto.
rewrite <- H2; auto with geo.
red in |- *; intros; apply H1.
rewrite H4; auto with geo.
Qed.