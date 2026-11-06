theory OCX_c30_057
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0912: "oc_sub oc_b30 912"
  by (oc_eval oc_c30_0912)

lemma oc_c30_0913: "oc_sub oc_b30 913"
  by (oc_eval oc_c30_0913)

lemma oc_c30_0914: "oc_sub oc_b30 914"
  by (oc_eval oc_c30_0914)

lemma oc_c30_0915: "oc_sub oc_b30 915"
  by (oc_eval oc_c30_0915)

lemma oc_c30_0916: "oc_sub oc_b30 916"
  by (oc_eval oc_c30_0916)

lemma oc_c30_0917: "oc_sub oc_b30 917"
  by (oc_eval oc_c30_0917)

lemma oc_c30_0918: "oc_sub oc_b30 918"
  by (oc_eval oc_c30_0918)

lemma oc_c30_0919: "oc_sub oc_b30 919"
  by (oc_eval oc_c30_0919)

lemma oc_c30_0920: "oc_sub oc_b30 920"
  by (oc_eval oc_c30_0920)

lemma oc_c30_0921: "oc_sub oc_b30 921"
  by (oc_eval oc_c30_0921)

lemma oc_c30_0922: "oc_sub oc_b30 922"
  by (oc_eval oc_c30_0922)

lemma oc_c30_0923: "oc_sub oc_b30 923"
  by (oc_eval oc_c30_0923)

lemma oc_c30_0924: "oc_sub oc_b30 924"
  by (oc_eval oc_c30_0924)

lemma oc_c30_0925: "oc_sub oc_b30 925"
  by (oc_eval oc_c30_0925)

lemma oc_c30_0926: "oc_sub oc_b30 926"
  by (oc_eval oc_c30_0926)

lemma oc_c30_0927: "oc_sub oc_b30 927"
  by (oc_eval oc_c30_0927)

lemma upt_c30_057: "[912..<928] = [912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927]"
  by (simp add: upt_rec)

lemma sec_c30_057: "\<forall>j\<in>{16 * 57..<16 * 57 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 57..<16 * 57 + 16}"
  then have "j \<in> set [912..<928]" unfolding set_upt by simp
  then have "j \<in> set [912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927]" unfolding upt_c30_057 .
  then show "oc_sub oc_b30 j" using oc_c30_0912 oc_c30_0913 oc_c30_0914 oc_c30_0915 oc_c30_0916 oc_c30_0917 oc_c30_0918 oc_c30_0919 oc_c30_0920 oc_c30_0921 oc_c30_0922 oc_c30_0923 oc_c30_0924 oc_c30_0925 oc_c30_0926 oc_c30_0927
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
