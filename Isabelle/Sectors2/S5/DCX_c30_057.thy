theory DCX_c30_057
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0912: "dc_sub dc_b30 912"
  by (dc_eval dc_c30_0912)

lemma dc_c30_0913: "dc_sub dc_b30 913"
  by (dc_eval dc_c30_0913)

lemma dc_c30_0914: "dc_sub dc_b30 914"
  by (dc_eval dc_c30_0914)

lemma dc_c30_0915: "dc_sub dc_b30 915"
  by (dc_eval dc_c30_0915)

lemma dc_c30_0916: "dc_sub dc_b30 916"
  by (dc_eval dc_c30_0916)

lemma dc_c30_0917: "dc_sub dc_b30 917"
  by (dc_eval dc_c30_0917)

lemma dc_c30_0918: "dc_sub dc_b30 918"
  by (dc_eval dc_c30_0918)

lemma dc_c30_0919: "dc_sub dc_b30 919"
  by (dc_eval dc_c30_0919)

lemma dc_c30_0920: "dc_sub dc_b30 920"
  by (dc_eval dc_c30_0920)

lemma dc_c30_0921: "dc_sub dc_b30 921"
  by (dc_eval dc_c30_0921)

lemma dc_c30_0922: "dc_sub dc_b30 922"
  by (dc_eval dc_c30_0922)

lemma dc_c30_0923: "dc_sub dc_b30 923"
  by (dc_eval dc_c30_0923)

lemma dc_c30_0924: "dc_sub dc_b30 924"
  by (dc_eval dc_c30_0924)

lemma dc_c30_0925: "dc_sub dc_b30 925"
  by (dc_eval dc_c30_0925)

lemma dc_c30_0926: "dc_sub dc_b30 926"
  by (dc_eval dc_c30_0926)

lemma dc_c30_0927: "dc_sub dc_b30 927"
  by (dc_eval dc_c30_0927)

lemma upt_c30_057: "[912..<928] = [912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927]"
  by (simp add: upt_rec)

lemma sec_c30_057: "\<forall>j\<in>{16 * 57..<16 * 57 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 57..<16 * 57 + 16}"
  then have "j \<in> set [912..<928]" unfolding set_upt by simp
  then have "j \<in> set [912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927]" unfolding upt_c30_057 .
  then show "dc_sub dc_b30 j" using dc_c30_0912 dc_c30_0913 dc_c30_0914 dc_c30_0915 dc_c30_0916 dc_c30_0917 dc_c30_0918 dc_c30_0919 dc_c30_0920 dc_c30_0921 dc_c30_0922 dc_c30_0923 dc_c30_0924 dc_c30_0925 dc_c30_0926 dc_c30_0927
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
