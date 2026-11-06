theory OCX_nc_057
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0912: "oc_sub None 912"
  by (oc_eval oc_nc_0912)

lemma oc_nc_0913: "oc_sub None 913"
  by (oc_eval oc_nc_0913)

lemma oc_nc_0914: "oc_sub None 914"
  by (oc_eval oc_nc_0914)

lemma oc_nc_0915: "oc_sub None 915"
  by (oc_eval oc_nc_0915)

lemma oc_nc_0916: "oc_sub None 916"
  by (oc_eval oc_nc_0916)

lemma oc_nc_0917: "oc_sub None 917"
  by (oc_eval oc_nc_0917)

lemma oc_nc_0918: "oc_sub None 918"
  by (oc_eval oc_nc_0918)

lemma oc_nc_0919: "oc_sub None 919"
  by (oc_eval oc_nc_0919)

lemma oc_nc_0920: "oc_sub None 920"
  by (oc_eval oc_nc_0920)

lemma oc_nc_0921: "oc_sub None 921"
  by (oc_eval oc_nc_0921)

lemma oc_nc_0922: "oc_sub None 922"
  by (oc_eval oc_nc_0922)

lemma oc_nc_0923: "oc_sub None 923"
  by (oc_eval oc_nc_0923)

lemma oc_nc_0924: "oc_sub None 924"
  by (oc_eval oc_nc_0924)

lemma oc_nc_0925: "oc_sub None 925"
  by (oc_eval oc_nc_0925)

lemma oc_nc_0926: "oc_sub None 926"
  by (oc_eval oc_nc_0926)

lemma oc_nc_0927: "oc_sub None 927"
  by (oc_eval oc_nc_0927)

lemma upt_nc_057: "[912..<928] = [912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927]"
  by (simp add: upt_rec)

lemma sec_nc_057: "\<forall>j\<in>{16 * 57..<16 * 57 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 57..<16 * 57 + 16}"
  then have "j \<in> set [912..<928]" unfolding set_upt by simp
  then have "j \<in> set [912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927]" unfolding upt_nc_057 .
  then show "oc_sub None j" using oc_nc_0912 oc_nc_0913 oc_nc_0914 oc_nc_0915 oc_nc_0916 oc_nc_0917 oc_nc_0918 oc_nc_0919 oc_nc_0920 oc_nc_0921 oc_nc_0922 oc_nc_0923 oc_nc_0924 oc_nc_0925 oc_nc_0926 oc_nc_0927
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
