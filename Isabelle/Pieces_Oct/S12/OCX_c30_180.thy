theory OCX_c30_180
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2880: "oc_sub oc_b30 2880"
  by (oc_eval oc_c30_2880)

lemma oc_c30_2881: "oc_sub oc_b30 2881"
  by (oc_eval oc_c30_2881)

lemma oc_c30_2882: "oc_sub oc_b30 2882"
  by (oc_eval oc_c30_2882)

lemma oc_c30_2883: "oc_sub oc_b30 2883"
  by (oc_eval oc_c30_2883)

lemma oc_c30_2884: "oc_sub oc_b30 2884"
  by (oc_eval oc_c30_2884)

lemma oc_c30_2885: "oc_sub oc_b30 2885"
  by (oc_eval oc_c30_2885)

lemma oc_c30_2886: "oc_sub oc_b30 2886"
  by (oc_eval oc_c30_2886)

lemma oc_c30_2887: "oc_sub oc_b30 2887"
  by (oc_eval oc_c30_2887)

lemma oc_c30_2888: "oc_sub oc_b30 2888"
  by (oc_eval oc_c30_2888)

lemma oc_c30_2889: "oc_sub oc_b30 2889"
  by (oc_eval oc_c30_2889)

lemma oc_c30_2890: "oc_sub oc_b30 2890"
  by (oc_eval oc_c30_2890)

lemma oc_c30_2891: "oc_sub oc_b30 2891"
  by (oc_eval oc_c30_2891)

lemma oc_c30_2892: "oc_sub oc_b30 2892"
  by (oc_eval oc_c30_2892)

lemma oc_c30_2893: "oc_sub oc_b30 2893"
  by (oc_eval oc_c30_2893)

lemma oc_c30_2894: "oc_sub oc_b30 2894"
  by (oc_eval oc_c30_2894)

lemma oc_c30_2895: "oc_sub oc_b30 2895"
  by (oc_eval oc_c30_2895)

lemma upt_c30_180: "[2880..<2896] = [2880, 2881, 2882, 2883, 2884, 2885, 2886, 2887, 2888, 2889, 2890, 2891, 2892, 2893, 2894, 2895]"
  by (simp add: upt_rec)

lemma sec_c30_180: "\<forall>j\<in>{16 * 180..<16 * 180 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 180..<16 * 180 + 16}"
  then have "j \<in> set [2880..<2896]" unfolding set_upt by simp
  then have "j \<in> set [2880, 2881, 2882, 2883, 2884, 2885, 2886, 2887, 2888, 2889, 2890, 2891, 2892, 2893, 2894, 2895]" unfolding upt_c30_180 .
  then show "oc_sub oc_b30 j" using oc_c30_2880 oc_c30_2881 oc_c30_2882 oc_c30_2883 oc_c30_2884 oc_c30_2885 oc_c30_2886 oc_c30_2887 oc_c30_2888 oc_c30_2889 oc_c30_2890 oc_c30_2891 oc_c30_2892 oc_c30_2893 oc_c30_2894 oc_c30_2895
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
