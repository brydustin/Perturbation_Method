theory OCX_nc_045
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0720: "oc_sub None 720"
  by (oc_eval oc_nc_0720)

lemma oc_nc_0721: "oc_sub None 721"
  by (oc_eval oc_nc_0721)

lemma oc_nc_0722: "oc_sub None 722"
  by (oc_eval oc_nc_0722)

lemma oc_nc_0723: "oc_sub None 723"
  by (oc_eval oc_nc_0723)

lemma oc_nc_0724: "oc_sub None 724"
  by (oc_eval oc_nc_0724)

lemma oc_nc_0725: "oc_sub None 725"
  by (oc_eval oc_nc_0725)

lemma oc_nc_0726: "oc_sub None 726"
  by (oc_eval oc_nc_0726)

lemma oc_nc_0727: "oc_sub None 727"
  by (oc_eval oc_nc_0727)

lemma oc_nc_0728: "oc_sub None 728"
  by (oc_eval oc_nc_0728)

lemma oc_nc_0729: "oc_sub None 729"
  by (oc_eval oc_nc_0729)

lemma oc_nc_0730: "oc_sub None 730"
  by (oc_eval oc_nc_0730)

lemma oc_nc_0731: "oc_sub None 731"
  by (oc_eval oc_nc_0731)

lemma oc_nc_0732: "oc_sub None 732"
  by (oc_eval oc_nc_0732)

lemma oc_nc_0733: "oc_sub None 733"
  by (oc_eval oc_nc_0733)

lemma oc_nc_0734: "oc_sub None 734"
  by (oc_eval oc_nc_0734)

lemma oc_nc_0735: "oc_sub None 735"
  by (oc_eval oc_nc_0735)

lemma upt_nc_045: "[720..<736] = [720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735]"
  by (simp add: upt_rec)

lemma sec_nc_045: "\<forall>j\<in>{16 * 45..<16 * 45 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 45..<16 * 45 + 16}"
  then have "j \<in> set [720..<736]" unfolding set_upt by simp
  then have "j \<in> set [720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735]" unfolding upt_nc_045 .
  then show "oc_sub None j" using oc_nc_0720 oc_nc_0721 oc_nc_0722 oc_nc_0723 oc_nc_0724 oc_nc_0725 oc_nc_0726 oc_nc_0727 oc_nc_0728 oc_nc_0729 oc_nc_0730 oc_nc_0731 oc_nc_0732 oc_nc_0733 oc_nc_0734 oc_nc_0735
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
