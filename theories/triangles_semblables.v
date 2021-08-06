
Require Export alignement.
Require Export angles_vecteurs.
Require Export rotation_plane.
Require Export reflexion_plane.
Require Export dilatations.
Require Export transformations_contact.
Require Export  distance_euclidienne.

(* Definition of similar triangles by  equality of 2 angles *)
Definition trianglesSD (A B C A' B' C' : PO):Prop:=
                triangle A B C /\ triangle A' B' C' /\
                cons_AV (vec B C) (vec B A) = cons_AV (vec B' C') (vec B' A') /\
                cons_AV (vec C A) (vec C B) = cons_AV (vec C' A') (vec C' B' ) .

Definition trianglesSI (A B C A' B' C' : PO):Prop:=
                triangle A B C /\ triangle A' B' C' /\
                cons_AV (vec B C) (vec B A) = cons_AV (vec B' A') (vec B' C') /\
                cons_AV (vec C A) (vec C B) = cons_AV (vec C' B' ) (vec C' A').

Definition triangles_semblables (A B C A' B' C' :PO) :Prop :=
                trianglesSD A B C A' B' C' \/
                trianglesSI A B C A' B' C'.

Ltac deroule_triangles_semblables :=
(*find out others trivial hypotheses from the one*)
  match goal with H : trianglesSD ?A ?B ?C ?D ?E ?F |- _ =>
  generalize H; let name := fresh in intros name ; red in name; decompose [and] name;
  deroule_triangle A B C; deroule_triangle D E F;clear name
| H : trianglesSI ?A ?B ?C ?D ?E ?F |- _ =>
  generalize H; let name := fresh in intros name ; red in name; decompose [and] name;
  deroule_triangle A B C; deroule_triangle D E F; clear name;
  match goal with H' : _ |- _ => move H after H' end
end.


Lemma trianglesSD_angles_egaux :
forall A B C A' B' C' :PO,
trianglesSD A B C A' B' C' -> cons_AV(vec A B) (vec A C) = cons_AV (vec A' B') (vec A' C').
intros A B C A' B' C' H.
deroule_triangles_semblables.
rewrite <- angle_triangle;try auto.
rewrite -> H2;rewrite -> H5.
apply angle_triangle;auto .
Qed.
Lemma trianglesSI_angles_egaux:
forall A B C A' B' C' :PO,
trianglesSI A B C A' B' C'  -> cons_AV (vec A B)(vec A C) = cons_AV (vec A' C') (vec A' B').
intros A B C A' B' C' H.
deroule_triangles_semblables.
rewrite <- angle_triangle;try auto.
rewrite -> H2;rewrite -> H5.
rewrite <-somme_triangle with A' C' B'; try auto.
mesure A' C' A' B'.
mesure B' A' B' C'.
mesure C' B' C' A'.
repeat rewrite <- mes_opp.
repeat rewrite <-add_mes_compatible.
replace (x+(x1+x0) + -(x0+x1)) with x; [auto|ring].
Qed.


Ltac expand_triangles_semblables :=
  deroule_triangles_semblables;
  match goal with H : trianglesSD ?A ?B ?C ?D ?E ?F |- _ =>
    generalize H; let name:=fresh in intros name; apply trianglesSD_angles_egaux in name
  |H : trianglesSI ?A ?B ?C ?D ?E ?F |- _ =>
    generalize H; let name:=fresh in intros name;  apply trianglesSI_angles_egaux in name ;
  match goal with H' : _ |- _ => move H after H' end
end.



Lemma trianglesSD_ordre_cycle :
forall A B C A' B' C' :PO,
trianglesSD A B C A' B' C' -> trianglesSD  B C A B' C' A'.
intros.
expand_triangles_semblables.
repeat split; auto with geo.
Qed.
Lemma trianglesSI_ordre_cycle :
forall A B C A' B' C' :PO,
trianglesSI A B C A' B' C' -> trianglesSI  B C A B' C' A'.
intros.
expand_triangles_semblables.
repeat split; auto with geo.
Qed.

Lemma trianglesSD_ordre_permute :
forall A B C A' B' C' :PO,
trianglesSD A B C A' B' C' -> trianglesSD  A C B A' C' B' .
intros.
expand_triangles_semblables.
repeat split; auto with geo.
Qed.

Lemma trianglesSI_ordre_permute :
forall A B C A' B' C' :PO,
trianglesSI A B C A' B' C' -> trianglesSI  A C B A' C' B' .
intros.
expand_triangles_semblables.
repeat split; auto with geo.
Qed.

#[export] Hint Resolve trianglesSD_ordre_cycle
                      trianglesSI_ordre_cycle
                      trianglesSD_ordre_permute
                      trianglesSI_ordre_permute
                      : geo.



Lemma trianglesSD_ordre_cycle2 :
forall A B C A' B' C' :PO,
trianglesSD A B C A' B' C' -> trianglesSD  C A B C' A' B' .
auto with geo.
Qed.

Lemma trianglesSD_ordre_permute2 :
forall A B C A' B' C' :PO,
trianglesSD A B C A' B' C' -> trianglesSD  B A C B' A' C' .
auto with geo.
Qed.

Lemma trianglesSD_ordre_permute3 :
forall A B C A' B' C' :PO,
trianglesSD A B C A' B' C' -> trianglesSD  C B A C' B' A'.
auto with geo.
Qed.

Lemma trianglesSI_ordre_cycle2 :
forall A B C A' B' C' :PO,
trianglesSI A B C A' B' C' -> trianglesSI  C A B C' A' B' .
auto with geo.
Qed.

Lemma trianglesSI_ordre_permute2 :
forall A B C A' B' C' :PO,
trianglesSI A B C A' B' C' -> trianglesSI  B A C B' A' C' .
auto with geo.
Qed.

Lemma trianglesSI_ordre_permute3 :
forall A B C A' B' C' :PO,
trianglesSI A B C A' B' C' -> trianglesSI  C B A C' B' A'.
auto with geo.
Qed.

Lemma trianglesS_trans_DD:
forall A B C A' B' C' M N P :PO,
trianglesSD A B C A' B' C' -> trianglesSD  A' B' C' M N P ->
trianglesSD A B C M N P.
intros A B C A' B' C' M N P H H1.
expand_triangles_semblables ;clear H1 .
expand_triangles_semblables ;clear H .
rewrite ->H3 in H15.
rewrite ->H6 in H18.
unfold trianglesSD; auto.
Qed.

Lemma trianglesS_trans_DI:
forall A B C A' B' C' M N P :PO,
trianglesSD A B C A' B' C' -> trianglesSI  A' B' C' M N P->
trianglesSI A B C M N P.
intros A B C A' B' C' M N P H H1.
expand_triangles_semblables ;clear H .
expand_triangles_semblables ;clear H1 .
rewrite <-H3 in H15.
rewrite <-H6 in H18.
unfold trianglesSI; auto.
Qed.

Lemma trianglesS_trans_II:
forall A B C A' B' C' M N P :PO,
trianglesSI A B C A' B' C' -> trianglesSI  A' B' C' M N P->
trianglesSD A B C M N P.
intros A B C A' B' C' M N P H H1.
expand_triangles_semblables ;clear H1 .
expand_triangles_semblables ;clear H .
assert (H31: cons_AV (vec B' A') (vec B' C') = cons_AV (vec N P)(vec N M))
by (apply permute_angles ;auto).
assert (H32: cons_AV (vec C' B') (vec C' A') = cons_AV (vec P M)(vec P N))
by (apply permute_angles ;auto).
rewrite H31 in H15.
rewrite H32 in H18.
unfold trianglesSD; auto.
Qed.


(* Lemmes related to similarity between a triangle and its transformations *)

Lemma alignes_imageZeroPi:
forall A B C : PO,
A<>B->A<>C->
alignes A B C ->
(cons_AV(vec A B)(vec A C) = image_angle 0)
  \/(cons_AV(vec A B)(vec A C) = image_angle pi).
intros A B C H H0 H1.
halignes H1 k.
elim (Rtotal_order k 0);intros.
right.
rewrite ->(@angle_produit_negatif_r k A B C A B);auto.
rewrite <-angle_nul;auto .
rewrite plus_commutative with (a :=image_angle 0)(b:=image_angle pi);auto with geo.
elim H3;intro H4.
rewrite H4 in H2.
rewrite (@produit_zero_conf k A C A B) in H0;auto.
elim H0;auto.
rewrite H4;assumption.
left.
rewrite (@angle_produit_positif_r k A B C A B );auto.
rewrite <-angle_nul;auto .
Qed.


Lemma rotation_image_bipoint_coincide :
forall (I A B A' B' :PO) ( a : R),
A' = rotation I a A ->
B' = rotation I a B ->
A =B -> A' = B'.
intros I A B A' B' a H H0 H1.
rewrite ->H1 in H.
rewrite <-H0 in H.
assumption.
Qed.


Lemma rotation_conserve_alignement:
forall (I A B C A' B' C' :PO) ( a : R),
A' = rotation I a A ->
B' = rotation I a B ->
C' = rotation I a C ->
alignes A B C -> alignes A' B' C'.
intros I A B C A' B' C' a H H0 H1 H2 .
discrimine A B .
elim (@rotation_image_bipoint_coincide I A B A' B' a);auto with geo.
discrimine B C .
elim (@rotation_image_bipoint_coincide I B C B' C' a);auto with geo.
discrimine C A .
elim (@rotation_image_bipoint_coincide I C A C' A' a);auto with geo.
assert (cons_AV (vec A B) (vec A C) = cons_AV (vec A' B') (vec A' C')).
apply (@rotation_conserve_angle I A B C A' B' C' a);auto.
elim(@ alignes_imageZeroPi A B C);intros;auto.
rewrite H7 in H6.
elim (@angle_nul_positif_colineaire A' B' C').
intros.
elim H8;intros.
apply colineaire_alignes with x;auto.
apply image_bipoint_distinct with (I:=I)(a:=a) (A:=A)(B:=B);auto.
apply image_bipoint_distinct with (I:=I)(a:=a) (A:=A)(B:=C);auto.
auto.
elim angle_pi_negatif_colineaire with (A:=A')(B:=B')(C:=C').
intros.
elim H8;intros.
apply colineaire_alignes with x;auto.
apply image_bipoint_distinct with (I:=I)(a:=a) (A:=A)(B:=B);auto.
apply image_bipoint_distinct with (I:=I)(a:=a) (A:=A)(B:=C);auto.
rewrite <-H6;assumption.
Qed.

(* Lemme related to similarity between a triangle and its Rotation *)
Lemma triangle_rotation_trianglesSD:
forall (I A B C A' B' C' :PO) ( a : R),
triangle A B C ->
A' = rotation I a A ->
B' = rotation I a B ->
C' = rotation I a C ->
trianglesSD A B C A' B' C'.
intros I A B C A' B' C' a H H1 H2.
deroule_triangle A B C.
unfold trianglesSD.
repeat split;[assumption|idtac|
            apply rotation_conserve_angle with (I:=I)( a:=a);auto with geo|
            apply rotation_conserve_angle with (I:=I)( a:=a);auto with geo].
intro.
elim H0.
apply (@rotation_conserve_alignement I A' B' C' A B C (-a) );
[apply rotation_inverse ;auto with geo|
apply rotation_inverse;auto with geo|
apply rotation_inverse;auto with geo|idtac].
assumption.
Qed.


Lemma reflexion_image_bipoint_coincide :
forall (M N A B A' B' :PO),
M<>N->
A' = reflexion M N A ->
B' = reflexion M N B ->
A =B -> A' = B'.
intros M N A B A' B' H H0 H1 H2.
rewrite ->H2 in H0.
rewrite <-H1 in H0.
assumption.
Qed.
Lemma reflexion_image_bipoint_distinct :
forall (M N A B A' B' :PO),
M<>N->
A' = reflexion M N A ->
B' = reflexion M N B ->
A <>B -> A'<> B'.
intros.
generalize (@reflexion_isometrie M N A A' B B');
 intros H7.
apply (isometrie_distinct (A:=A) (B:=B)); auto.
Qed.

Lemma reflexion_conserve_alignement:
forall (M N A B C A' B' C' :PO) ,
M<>N->
A' = reflexion M N A ->
B' = reflexion M N B ->
C' = reflexion M N C ->
alignes A B C -> alignes A' B' C'.
intros M N A B C A' B' C' H0 H1 H2 H3 H.
discrimine A B .
elim (@reflexion_image_bipoint_coincide M N A B A' B' );auto with geo.
discrimine B C .
elim (@reflexion_image_bipoint_coincide M N B C B' C' );auto with geo.
discrimine C A .
elim (@reflexion_image_bipoint_coincide M N C A C' A' );auto with geo.
assert (cons_AV (vec A' B') (vec A' C') = opp(cons_AV (vec A B) (vec A C))).
apply (@reflexion_anti_deplacement M N A A' B B' C C' );auto.
elim(@ alignes_imageZeroPi A B C);intros;auto.
rewrite H8 in H7.
assert (image_angle (- 0) = opp (image_angle 0)).
apply (@mes_opp 0);auto.
replace (-0) with (0) in H9.
rewrite <-H9 in H7.
elim (@angle_nul_positif_colineaire A' B' C').
intros.
elim H10;intros.
apply colineaire_alignes with x;auto.
apply reflexion_image_bipoint_distinct with (M:=M)(N:=N) (A:=A)(B:=B);auto.
apply reflexion_image_bipoint_distinct with (M:=M)(N:=N) (A:=A)(B:=C);auto.
assumption.
field.

rewrite H8 in H7.
assert (image_angle (pi) = opp(image_angle (pi ))).
rewrite <-mes_opp.
rewrite <-plus_angle_zero.
rewrite <-pi_plus_pi.
rewrite <-add_mes_compatible.
unfold deuxpi.
replace (-pi +(pi +pi)) with (pi).
trivial.
field.
rewrite <-H9 in H7.
elim angle_pi_negatif_colineaire with (A:=A')(B:=B')(C:=C').
intros.
elim H10;intros.
apply colineaire_alignes with x;auto.
apply reflexion_image_bipoint_distinct with (M:=M)(N:=N) (A:=A)(B:=B);auto.
apply reflexion_image_bipoint_distinct with (M:=M)(N:=N) (A:=A)(B:=C);auto.
assumption.
Qed.

(* Lemme related to similarity between a triangle and its Reflexion *)
Lemma triangle_reflexion_trianglesSI:
forall (M N A B C A' B' C' :PO) ,
M<>N->
triangle A B C ->
A' = reflexion M N A ->
B' = reflexion M N B ->
C' = reflexion M N C ->
trianglesSI A B C A' B' C'.

intros M N A B C A' B' C' H H0 H1 H2 H3.
deroule_triangle A B C.
unfold trianglesSI.
repeat split;[assumption|idtac|
            rewrite-> (@reflexion_anti_deplacement M N B B' A A' C C');auto with geo;rewrite->def_opp ; auto|
            rewrite-> (@reflexion_anti_deplacement M N C C' B B' A A' );auto with geo;rewrite->def_opp ; auto].
intro.
elim H4.
apply (@reflexion_conserve_alignement M N A' B' C' A B C );
[assumption|apply reflexion_symetrie ;auto with geo|
apply reflexion_symetrie;auto with geo|
apply reflexion_symetrie;auto with geo|idtac].
assumption.
Qed.

(* Lemme related to similarity between a triangle and its Transition *)
Lemma triangle_translation_trianglesSD:
forall I J A A' B B' C C' : PO,
triangle A B C ->
A' = translation I J A->
B' = translation I J B->
C' = translation I J C ->
trianglesSD A B C A' B' C'.
intros I J A A' B B' C C' H0 H1 H2 H3.
unfold trianglesSD.
repeat split;[assumption|idtac|
            (rewrite (@translation_bipoint I J B B' C C');auto);
(rewrite (@translation_bipoint I J B B' A A');auto)|
            (rewrite (@translation_bipoint I J C C' A A');auto);
(rewrite (@translation_bipoint I J C C' B B');auto)
           ].
unfold triangle in *.
intro H4.
elim H0.
halignes H4 k.
assert (A=B).
apply distance_refl1.
rewrite <-(@ translation_isometrie I J A A' B B');auto.
apply distance_refl2;assumption.
rewrite H;auto with geo.
apply colineaire_alignes with (k:=k);auto.
rewrite (@translation_bipoint I J A A' B B');auto.
rewrite (@translation_bipoint I J A A' C C');auto.
Qed.

Lemma inversion_colineaire :
 forall (k : R) (A B C : PO),
 A <> C -> vec A C = mult_PP k (vec A B) -> vec A B = mult_PP (/ k) (vec A C).
intros.
cut (k <> 0); intros.
rewrite H0.
Fieldvec k.
contrapose H.
apply vecteur_nul_conf.
rewrite H0; rewrite H1; Ringvec.
Qed.

(* Lemma related to equality of angles between corresponding sides of 2 similar triangles *)
Lemma trianglesSD_angles_cotes :
forall A B C M N P :PO,
trianglesSD A B C M N P->
exists x:R,
	cons_AV (vec M N)(vec A B) =image_angle x /\
	cons_AV (vec N P)(vec B C) =image_angle x /\
	cons_AV (vec P M)(vec C A) =image_angle x.
intros A B C M N P H.
expand_triangles_semblables.
elim (tout_angle_a_une_mesure (A:=N) (B:=P) (C:=B) (D:=C)); auto with geo.
intros x H13.
exists x;repeat split;auto.
rewrite <-(@Chasles M N P N A B);auto.
rewrite <-(@Chasles P N C B A B);auto.
rewrite (@plus_commutative
          (cons_AV (vec  P N)(vec C B)) (cons_AV(vec C B)(vec A B))).
rewrite plus_associative.
rewrite (@angle_oppu_oppv  B C B A);auto.
rewrite H2.
rewrite <-(@angle_oppu_oppv  N P N M);auto.
rewrite Chasles;auto.
rewrite (@angle_oppu_oppv  N P B C);auto.
rewrite <-H13.
rewrite <-angle_nul;auto.
rewrite plus_commutative.
rewrite plus_angle_zero;auto.

rewrite <-(@Chasles P M  P N C A  );auto.
rewrite <-(@Chasles P N C B C A);auto.
rewrite (@plus_commutative
          (cons_AV (vec  P N)(vec C B)) (cons_AV(vec C B)(vec C A))).
rewrite plus_associative.
rewrite <-H5.
rewrite Chasles;auto.
rewrite (@angle_oppu_oppv  N P B C);auto.
rewrite <-H13.
rewrite <-angle_nul;auto.
rewrite plus_commutative.
rewrite plus_angle_zero;auto.
Qed.


Lemma Thales_consequence :
forall A B C M N :PO,
triangle A B C -> triangle A M N -> alignes A M B -> alignes A N C ->
paralleles (droite M N) (droite B C)->
    exists k:R,
                     distance B C = k* distance M N  /\
                     distance A B = k* distance A M /\
                     distance A C = k * distance A N /\ k<>0.
intros A B C M N H0 H1 H2 H3 H.
deroule_triangle A B C.
deroule_triangle A M N.
halignes H2 k.
assert (vec A M = mult_PP (/k) (vec A B)).
apply (@inversion_colineaire k A M B H7 H12).
assert (k<>0).
red;intros.
rewrite H14 in H12.
unfold vec at 2 in H12 .
assert(mult_PP 0 (add_PP(cons(-1) A)(cons 1 M) ) = zero) by RingPP.
rewrite H15 in H12.
assert (A=B) by apply (@vecteur_nul_conf A B H12) .
elim H7;auto.
assert (/k<>0) by apply (@Rinv_neq_0_compat k H14).
assert (vec A N = mult_PP (/k) (vec A C)) by
      (apply (@Thales_concours (/k) A B C M N H0 H15 H13);auto with geo).
assert (vec A C = mult_PP (k) (vec A N)) .
elim (@Rinv_involutive k);auto.
apply (@inversion_colineaire (/k) A C N );auto.
assert (vec B C =mult_PP (k) (vec M N)).
rewrite <-(@Chasles_vec M A N).
rewrite <- distrib_mult_PP .
rewrite <-H17 .
assert ( vec B A = mult_PP (k) (vec M A)).
rewrite(@opp_vecteur A M ).
rewrite mult_mult_vec .
replace (k * -1) with (-1 * k).
rewrite <-mult_mult_vec .
rewrite <-H12.
apply opp_vecteur;auto.
ring.
rewrite <-H18.
rewrite  Chasles_vec;auto.
exists (Rabs(k)).
repeat split;
[apply colinearite_distance;auto |apply colinearite_distance;auto|
apply colinearite_distance;auto|apply Rabs_no_R0;auto].

Qed.


Lemma  imageZeroPi_paralelles:
forall A B C D: PO,
A<>B->C<>D->
(cons_AV(vec A B)(vec C D) = image_angle 0)
  \/(cons_AV(vec A B)(vec C D) = image_angle pi) ->
paralleles (droite A B) (droite C D).
intros A B C D H H1 H2.
set (B' := translation A C B).
assert (H3:= refl_equal B'); unfold B' at 2 in H3.
assert (H4 : C =translation A C A) by (apply translation_trivial;auto).
assert (H5 :vec A B =vec C B') by (apply  (@translation_bipoint A C);auto).
rewrite H5 in H2.
assert (H6:C <>B').
red;intro H7.
rewrite H7 in H5.
rewrite <-(@mult_1_vec B' B') in H5.
rewrite <-vecteur_nul in H5.
assert (A = B) by (apply vecteur_nul_conf;auto).
elim H;auto.
apply (@paralleles_trans A B C B' C D);auto.
rewrite <-(@mult_1_vec C B') in H5.
apply (colineaires_paralleles (k:=1) );auto .
elim H2;intro H7.
elim (@angle_nul_positif_colineaire C B' D);auto.
intros x [H8 H9].
assert (paralleles (droite C D)(droite C B')) by (apply colineaires_paralleles with (k:=x);auto).
apply  paralleles_sym;assumption.
elim (@angle_pi_negatif_colineaire C B' D);auto.
intros x [H8 H9].
assert (paralleles (droite C D)(droite C B')) by (apply colineaires_paralleles with (k:=x);auto).
apply  paralleles_sym;assumption.
Qed.

(* Lemme related to proportionate sides of 2 direct similar triangles  *)
Lemma trianglesSD_proportion :
forall A B C A' B' C' :PO,
trianglesSD A B C A' B' C' ->
    exists k:R,
                      distance B C =k*distance B' C' /\
                      distance A B = k*distance A' B' /\
                      distance A C = k * distance A' C'/\ k<>0.

intros A B C A' B' C' H.
generalize H;intro H1.
destruct H1 as [H2 [H3 [H4 H5]]].
elim (@tout_angle_a_une_mesure A' B' A B);
  [intros |deroule_triangle A' B' C';auto|deroule_triangle A B C;auto].
set (M:=(rotation A' x B')).
assert (H6 := refl_equal M); unfold M at 2 in H6.
set (N:=(rotation A' x C')).
assert (H7 := refl_equal N); unfold N at 2 in H7.
assert (H8 : A' = rotation A' x A') by
   (apply rotation_def_centre;auto).
assert ( H9: trianglesSD A' B' C' A' M N)
   by ( apply triangle_rotation_trianglesSD  with (I := A') (a:=x);auto).
set (B'':=(translation A' A M)).
assert (H10 := refl_equal B''); unfold B'' at 2 in H10.
set (C'':=(translation A' A N)).
assert (H11:= refl_equal C''); unfold C'' at 2 in H11.
assert (H12 : A = translation A' A A') by
   (apply rec_translation_vecteur;auto).
assert ( H13: trianglesSD A' M N A B'' C'').
apply (@triangle_translation_trianglesSD  A' A);auto.
destruct H9 as [H' [H'' _]];intros;auto.
assert (H14 :trianglesSD A B C A B'' C'' ).
apply (@trianglesS_trans_DD A B C A' M N A B'' C'');auto.
apply (@trianglesS_trans_DD A B C A' B' C' A' M N);auto.
assert (H15 : distance B' C' = distance B'' C'').
rewrite <-(@rotation_isometrie A' B' C' M N x);auto.
rewrite <-(@translation_isometrie A' A M B'' N C'');auto.
assert (H16 :distance A' B' = distance A B'').
rewrite <-(@rotation_isometrie A' A' B' A' M x);auto.
rewrite <-(@translation_isometrie A' A A' A M B'');auto.
assert (H17:distance A' C' = distance A C'').
rewrite <-(@rotation_isometrie A' A' C' A' N x);auto.
rewrite <-(@translation_isometrie A' A A' A N C'');auto.
rewrite H15;rewrite H16;rewrite H17.
generalize H14;intros H80.
destruct H80 as [H' [H'' _]];intros;auto.
deroule_triangle A B C.
deroule_triangle A' B' C'.
deroule_triangle A B'' C''.
assert (cons_AV  (vec A' B') (vec A B'') = image_angle x).
rewrite  <-(@translation_bipoint A' A A' A M B'');auto.
elim (@rotation_def A' B' M x);auto with geo.
rewrite H0 in H27.
assert (cons_AV (vec A B'') (vec A B) =image_angle 0).
rewrite <-(@Chasles_diff A' B');auto.
rewrite H27.
rewrite def_opp;auto.
rewrite Chasles;auto.
rewrite <- (@angle_nul);auto.
elim  (@trianglesSD_angles_cotes A B C A B'' C'');auto;intros .
destruct H29 as [H81 [H82 H83]].
rewrite H81 in H28.
rewrite H28 in H81.
rewrite H28 in H82.
rewrite H28 in H83.
cut (alignes A B'' B);intros.
cut (alignes A C'' C); intros .
apply Thales_consequence;auto.
apply imageZeroPi_paralelles;auto.
assert (H84 :cons_AV(vec A C'') (vec A C) = cons_AV (vec C'' A)(vec C A)) by
(apply angle_oppu_oppv;auto).
rewrite H83 in H84.
elim (@angle_nul_positif_colineaire A C'' C);[ intros  k [_ H85]|auto|auto|auto].
unfold alignes;right.
apply colineaire_alignes1 with (k:=k);auto.
elim (@angle_nul_positif_colineaire A B'' B);[ intros  k [_ H86]|auto|auto|auto].
unfold alignes;right.
apply colineaire_alignes1 with (k:=k);auto.
Qed.

(* Lemme related to proportionate sides of 2 indirect similar triangles  *)
Lemma trianglesSI_proportion :
forall A B C A' B' C' :PO,
trianglesSI A B C A' B' C' ->
    exists k:R,
                      distance B C =k*distance B' C' /\
                      distance A B = k*distance A' B' /\
                      distance A C = k * distance A' C' /\ k<>0.
intros A B C A' B' C' H.
expand_triangles_semblables.
set (A'':=(reflexion B' C' A')).
assert (H20 := refl_equal A''); unfold A'' at 2 in H20.
assert (H21: B' = reflexion B' C' B') by (apply reflexion_axe;auto with geo).
assert (H22: C' = reflexion B' C' C') by (apply reflexion_axe;auto with geo).
assert (H23: trianglesSI A' B' C' A'' B' C')
by (apply (@triangle_reflexion_trianglesSI B' C');auto).
assert (H24 : distance A' B' = distance A'' B')
 by (apply (@reflexion_isometrie B' C');auto).
assert (H25 : distance A' C' = distance A'' C')
 by (apply (@reflexion_isometrie B' C');auto).
rewrite H24.
rewrite H25.
assert (H26: trianglesSD A B C A'' B' C')
by (apply (@trianglesS_trans_II A B C A' B' C' A'' B' C');auto).
apply trianglesSD_proportion;auto.
Qed.

(* Lemme related to proportionate sides of 2 similar triangles  *)
Lemma triangles_semblables_proportion :
forall A B C A' B' C' :PO,
triangles_semblables A B C A' B' C' ->
    exists k:R,
                      distance B C =k*distance B' C' /\
                      distance A B = k*distance A' B' /\
                      distance A C = k * distance A' C' /\ k<>0.
intros A B C A' B' C' H.
unfold triangles_semblables in H.
elim H;intros H1.
apply trianglesSD_proportion ;auto.
apply trianglesSI_proportion ;auto.
Qed.