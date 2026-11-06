theory OCX_c30_170
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2720: "oc_sub oc_b30 2720"
  by (oc_eval oc_c30_2720)

lemma oc_c30_2721: "oc_sub oc_b30 2721"
  by (oc_eval oc_c30_2721)

lemma oc_c30_2722: "oc_sub oc_b30 2722"
  by (oc_eval oc_c30_2722)

lemma oc_c30_2723: "oc_sub oc_b30 2723"
  by (oc_eval oc_c30_2723)

lemma oc_c30_2724: "oc_sub oc_b30 2724"
  by (oc_eval oc_c30_2724)

lemma oc_c30_2725: "oc_sub oc_b30 2725"
  by (oc_eval oc_c30_2725)

lemma oc_c30_2726: "oc_sub oc_b30 2726"
  by (oc_eval oc_c30_2726)

lemma oc_c30_2727: "oc_sub oc_b30 2727"
  by (oc_eval oc_c30_2727)

lemma oc_c30_2728: "oc_sub oc_b30 2728"
  by (oc_eval oc_c30_2728)

lemma oc_c30_2729: "oc_sub oc_b30 2729"
  by (oc_eval oc_c30_2729)

lemma oc_c30_2730: "oc_sub oc_b30 2730"
  by (oc_eval oc_c30_2730)

lemma oc_c30_2731: "oc_sub oc_b30 2731"
  by (oc_eval oc_c30_2731)

lemma oc_c30_2732: "oc_sub oc_b30 2732"
  by (oc_eval oc_c30_2732)

lemma oc_c30_2733: "oc_sub oc_b30 2733"
  by (oc_eval oc_c30_2733)

lemma oc_c30_2734: "oc_sub oc_b30 2734"
  by (oc_eval oc_c30_2734)

lemma oc_c30_2735: "oc_sub oc_b30 2735"
  by (oc_eval oc_c30_2735)

lemma upt_c30_170: "[2720..<2736] = [2720, 2721, 2722, 2723, 2724, 2725, 2726, 2727, 2728, 2729, 2730, 2731, 2732, 2733, 2734, 2735]"
  by (simp add: upt_rec)

lemma sec_c30_170: "\<forall>j\<in>{16 * 170..<16 * 170 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 170..<16 * 170 + 16}"
  then have "j \<in> set [2720..<2736]" unfolding set_upt by simp
  then have "j \<in> set [2720, 2721, 2722, 2723, 2724, 2725, 2726, 2727, 2728, 2729, 2730, 2731, 2732, 2733, 2734, 2735]" unfolding upt_c30_170 .
  then show "oc_sub oc_b30 j" using oc_c30_2720 oc_c30_2721 oc_c30_2722 oc_c30_2723 oc_c30_2724 oc_c30_2725 oc_c30_2726 oc_c30_2727 oc_c30_2728 oc_c30_2729 oc_c30_2730 oc_c30_2731 oc_c30_2732 oc_c30_2733 oc_c30_2734 oc_c30_2735
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
