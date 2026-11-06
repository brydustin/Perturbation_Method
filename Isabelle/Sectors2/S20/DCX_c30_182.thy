theory DCX_c30_182
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2912: "dc_sub dc_b30 2912"
  by (dc_eval dc_c30_2912)

lemma dc_c30_2913: "dc_sub dc_b30 2913"
  by (dc_eval dc_c30_2913)

lemma dc_c30_2914: "dc_sub dc_b30 2914"
  by (dc_eval dc_c30_2914)

lemma dc_c30_2915: "dc_sub dc_b30 2915"
  by (dc_eval dc_c30_2915)

lemma dc_c30_2916: "dc_sub dc_b30 2916"
  by (dc_eval dc_c30_2916)

lemma dc_c30_2917: "dc_sub dc_b30 2917"
  by (dc_eval dc_c30_2917)

lemma dc_c30_2918: "dc_sub dc_b30 2918"
  by (dc_eval dc_c30_2918)

lemma dc_c30_2919: "dc_sub dc_b30 2919"
  by (dc_eval dc_c30_2919)

lemma dc_c30_2920: "dc_sub dc_b30 2920"
  by (dc_eval dc_c30_2920)

lemma dc_c30_2921: "dc_sub dc_b30 2921"
  by (dc_eval dc_c30_2921)

lemma dc_c30_2922: "dc_sub dc_b30 2922"
  by (dc_eval dc_c30_2922)

lemma dc_c30_2923: "dc_sub dc_b30 2923"
  by (dc_eval dc_c30_2923)

lemma dc_c30_2924: "dc_sub dc_b30 2924"
  by (dc_eval dc_c30_2924)

lemma dc_c30_2925: "dc_sub dc_b30 2925"
  by (dc_eval dc_c30_2925)

lemma dc_c30_2926: "dc_sub dc_b30 2926"
  by (dc_eval dc_c30_2926)

lemma dc_c30_2927: "dc_sub dc_b30 2927"
  by (dc_eval dc_c30_2927)

lemma upt_c30_182: "[2912..<2928] = [2912, 2913, 2914, 2915, 2916, 2917, 2918, 2919, 2920, 2921, 2922, 2923, 2924, 2925, 2926, 2927]"
  by (simp add: upt_rec)

lemma sec_c30_182: "\<forall>j\<in>{16 * 182..<16 * 182 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 182..<16 * 182 + 16}"
  then have "j \<in> set [2912..<2928]" unfolding set_upt by simp
  then have "j \<in> set [2912, 2913, 2914, 2915, 2916, 2917, 2918, 2919, 2920, 2921, 2922, 2923, 2924, 2925, 2926, 2927]" unfolding upt_c30_182 .
  then show "dc_sub dc_b30 j" using dc_c30_2912 dc_c30_2913 dc_c30_2914 dc_c30_2915 dc_c30_2916 dc_c30_2917 dc_c30_2918 dc_c30_2919 dc_c30_2920 dc_c30_2921 dc_c30_2922 dc_c30_2923 dc_c30_2924 dc_c30_2925 dc_c30_2926 dc_c30_2927
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
