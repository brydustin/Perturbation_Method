theory DCX_c30_045
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0720: "dc_sub dc_b30 720"
  by (dc_eval dc_c30_0720)

lemma dc_c30_0721: "dc_sub dc_b30 721"
  by (dc_eval dc_c30_0721)

lemma dc_c30_0722: "dc_sub dc_b30 722"
  by (dc_eval dc_c30_0722)

lemma dc_c30_0723: "dc_sub dc_b30 723"
  by (dc_eval dc_c30_0723)

lemma dc_c30_0724: "dc_sub dc_b30 724"
  by (dc_eval dc_c30_0724)

lemma dc_c30_0725: "dc_sub dc_b30 725"
  by (dc_eval dc_c30_0725)

lemma dc_c30_0726: "dc_sub dc_b30 726"
  by (dc_eval dc_c30_0726)

lemma dc_c30_0727: "dc_sub dc_b30 727"
  by (dc_eval dc_c30_0727)

lemma dc_c30_0728: "dc_sub dc_b30 728"
  by (dc_eval dc_c30_0728)

lemma dc_c30_0729: "dc_sub dc_b30 729"
  by (dc_eval dc_c30_0729)

lemma dc_c30_0730: "dc_sub dc_b30 730"
  by (dc_eval dc_c30_0730)

lemma dc_c30_0731: "dc_sub dc_b30 731"
  by (dc_eval dc_c30_0731)

lemma dc_c30_0732: "dc_sub dc_b30 732"
  by (dc_eval dc_c30_0732)

lemma dc_c30_0733: "dc_sub dc_b30 733"
  by (dc_eval dc_c30_0733)

lemma dc_c30_0734: "dc_sub dc_b30 734"
  by (dc_eval dc_c30_0734)

lemma dc_c30_0735: "dc_sub dc_b30 735"
  by (dc_eval dc_c30_0735)

lemma upt_c30_045: "[720..<736] = [720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735]"
  by (simp add: upt_rec)

lemma sec_c30_045: "\<forall>j\<in>{16 * 45..<16 * 45 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 45..<16 * 45 + 16}"
  then have "j \<in> set [720..<736]" unfolding set_upt by simp
  then have "j \<in> set [720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735]" unfolding upt_c30_045 .
  then show "dc_sub dc_b30 j" using dc_c30_0720 dc_c30_0721 dc_c30_0722 dc_c30_0723 dc_c30_0724 dc_c30_0725 dc_c30_0726 dc_c30_0727 dc_c30_0728 dc_c30_0729 dc_c30_0730 dc_c30_0731 dc_c30_0732 dc_c30_0733 dc_c30_0734 dc_c30_0735
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
