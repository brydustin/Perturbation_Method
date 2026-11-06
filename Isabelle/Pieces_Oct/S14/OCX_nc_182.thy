theory OCX_nc_182
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2912: "oc_sub None 2912"
  by (oc_eval oc_nc_2912)

lemma oc_nc_2913: "oc_sub None 2913"
  by (oc_eval oc_nc_2913)

lemma oc_nc_2914: "oc_sub None 2914"
  by (oc_eval oc_nc_2914)

lemma oc_nc_2915: "oc_sub None 2915"
  by (oc_eval oc_nc_2915)

lemma oc_nc_2916: "oc_sub None 2916"
  by (oc_eval oc_nc_2916)

lemma oc_nc_2917: "oc_sub None 2917"
  by (oc_eval oc_nc_2917)

lemma oc_nc_2918: "oc_sub None 2918"
  by (oc_eval oc_nc_2918)

lemma oc_nc_2919: "oc_sub None 2919"
  by (oc_eval oc_nc_2919)

lemma oc_nc_2920: "oc_sub None 2920"
  by (oc_eval oc_nc_2920)

lemma oc_nc_2921: "oc_sub None 2921"
  by (oc_eval oc_nc_2921)

lemma oc_nc_2922: "oc_sub None 2922"
  by (oc_eval oc_nc_2922)

lemma oc_nc_2923: "oc_sub None 2923"
  by (oc_eval oc_nc_2923)

lemma oc_nc_2924: "oc_sub None 2924"
  by (oc_eval oc_nc_2924)

lemma oc_nc_2925: "oc_sub None 2925"
  by (oc_eval oc_nc_2925)

lemma oc_nc_2926: "oc_sub None 2926"
  by (oc_eval oc_nc_2926)

lemma oc_nc_2927: "oc_sub None 2927"
  by (oc_eval oc_nc_2927)

lemma upt_nc_182: "[2912..<2928] = [2912, 2913, 2914, 2915, 2916, 2917, 2918, 2919, 2920, 2921, 2922, 2923, 2924, 2925, 2926, 2927]"
  by (simp add: upt_rec)

lemma sec_nc_182: "\<forall>j\<in>{16 * 182..<16 * 182 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 182..<16 * 182 + 16}"
  then have "j \<in> set [2912..<2928]" unfolding set_upt by simp
  then have "j \<in> set [2912, 2913, 2914, 2915, 2916, 2917, 2918, 2919, 2920, 2921, 2922, 2923, 2924, 2925, 2926, 2927]" unfolding upt_nc_182 .
  then show "oc_sub None j" using oc_nc_2912 oc_nc_2913 oc_nc_2914 oc_nc_2915 oc_nc_2916 oc_nc_2917 oc_nc_2918 oc_nc_2919 oc_nc_2920 oc_nc_2921 oc_nc_2922 oc_nc_2923 oc_nc_2924 oc_nc_2925 oc_nc_2926 oc_nc_2927
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
