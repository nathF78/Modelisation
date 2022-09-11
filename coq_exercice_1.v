Require Import Naturelle.
Section Session1_2021_Logique_Exercice_1.

Variable A B C : Prop.

Theorem Exercice_1_Naturelle :  ((A -> C) \/ (B -> C)) -> ((A /\ B) -> C).
Proof.
I_imp H1.
I_imp H2.
E_ou (A -> C) (B -> C).
Hyp H1.
I_imp H3.
E_imp A.
Hyp H3.
E_et_g B.
Hyp H2.
I_imp H4.
E_imp B.
Hyp H4.
E_et_d A.
Hyp H2.
Qed.

Theorem Exercice_1_Coq : ((A -> C) \/ (B -> C)) -> ((A /\ B) -> C).
Proof.
intro H1.
intro H2.
elim H1.
intro H3.
cut A.
exact H3.
cut (A /\ B).
intro H.
elim H.
intros HA HB.
exact HA.
exact H2.
intro H4.
cut B.
exact H4.
cut (A /\ B).
intro H.
elim H.
intros HA HB.
exact HB.
exact H2.
Qed.

End Session1_2021_Logique_Exercice_1.

