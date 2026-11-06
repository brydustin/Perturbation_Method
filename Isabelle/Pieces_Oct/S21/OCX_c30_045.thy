theory OCX_c30_045
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0720: "oc_sub oc_b30 720"
  by (oc_eval oc_c30_0720)

lemma oc_c30_0721: "oc_sub oc_b30 721"
  by (oc_eval oc_c30_0721)

lemma oc_c30_0722: "oc_sub oc_b30 722"
  by (oc_eval oc_c30_0722)

lemma oc_c30_0723: "oc_sub oc_b30 723"
  by (oc_eval oc_c30_0723)

lemma oc_c30_0724: "oc_sub oc_b30 724"
  by (oc_eval oc_c30_0724)

lemma oc_c30_0725: "oc_sub oc_b30 725"
  by (oc_eval oc_c30_0725)

lemma oc_c30_0726: "oc_sub oc_b30 726"
  by (oc_eval oc_c30_0726)

lemma oc_c30_0727: "oc_sub oc_b30 727"
  by (oc_eval oc_c30_0727)

lemma oc_c30_0728: "oc_sub oc_b30 728"
  by (oc_eval oc_c30_0728)

lemma oc_c30_0729: "oc_sub oc_b30 729"
  by (oc_eval oc_c30_0729)

lemma oc_c30_0730: "oc_sub oc_b30 730"
  by (oc_eval oc_c30_0730)

lemma oc_c30_0731: "oc_sub oc_b30 731"
  by (oc_eval oc_c30_0731)

lemma oc_c30_0732: "oc_sub oc_b30 732"
  by (oc_eval oc_c30_0732)

lemma oc_c30_0733: "oc_sub oc_b30 733"
  by (oc_eval oc_c30_0733)

lemma oc_c30_0734: "oc_sub oc_b30 734"
  by (oc_eval oc_c30_0734)

lemma oc_c30_0735: "oc_sub oc_b30 735"
  by (oc_eval oc_c30_0735)

lemma upt_c30_045: "[720..<736] = [720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735]"
  by (simp add: upt_rec)

lemma sec_c30_045: "\<forall>j\<in>{16 * 45..<16 * 45 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 45..<16 * 45 + 16}"
  then have "j \<in> set [720..<736]" unfolding set_upt by simp
  then have "j \<in> set [720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735]" unfolding upt_c30_045 .
  then show "oc_sub oc_b30 j" using oc_c30_0720 oc_c30_0721 oc_c30_0722 oc_c30_0723 oc_c30_0724 oc_c30_0725 oc_c30_0726 oc_c30_0727 oc_c30_0728 oc_c30_0729 oc_c30_0730 oc_c30_0731 oc_c30_0732 oc_c30_0733 oc_c30_0734 oc_c30_0735
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
