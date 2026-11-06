theory OCX_nc_177
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2832: "oc_sub None 2832"
  by (oc_eval oc_nc_2832)

lemma oc_nc_2833: "oc_sub None 2833"
  by (oc_eval oc_nc_2833)

lemma oc_nc_2834: "oc_sub None 2834"
  by (oc_eval oc_nc_2834)

lemma oc_nc_2835: "oc_sub None 2835"
  by (oc_eval oc_nc_2835)

lemma oc_nc_2836: "oc_sub None 2836"
  by (oc_eval oc_nc_2836)

lemma oc_nc_2837: "oc_sub None 2837"
  by (oc_eval oc_nc_2837)

lemma oc_nc_2838: "oc_sub None 2838"
  by (oc_eval oc_nc_2838)

lemma oc_nc_2839: "oc_sub None 2839"
  by (oc_eval oc_nc_2839)

lemma oc_nc_2840: "oc_sub None 2840"
  by (oc_eval oc_nc_2840)

lemma oc_nc_2841: "oc_sub None 2841"
  by (oc_eval oc_nc_2841)

lemma oc_nc_2842: "oc_sub None 2842"
  by (oc_eval oc_nc_2842)

lemma oc_nc_2843: "oc_sub None 2843"
  by (oc_eval oc_nc_2843)

lemma oc_nc_2844: "oc_sub None 2844"
  by (oc_eval oc_nc_2844)

lemma oc_nc_2845: "oc_sub None 2845"
  by (oc_eval oc_nc_2845)

lemma oc_nc_2846: "oc_sub None 2846"
  by (oc_eval oc_nc_2846)

lemma oc_nc_2847: "oc_sub None 2847"
  by (oc_eval oc_nc_2847)

lemma upt_nc_177: "[2832..<2848] = [2832, 2833, 2834, 2835, 2836, 2837, 2838, 2839, 2840, 2841, 2842, 2843, 2844, 2845, 2846, 2847]"
  by (simp add: upt_rec)

lemma sec_nc_177: "\<forall>j\<in>{16 * 177..<16 * 177 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 177..<16 * 177 + 16}"
  then have "j \<in> set [2832..<2848]" unfolding set_upt by simp
  then have "j \<in> set [2832, 2833, 2834, 2835, 2836, 2837, 2838, 2839, 2840, 2841, 2842, 2843, 2844, 2845, 2846, 2847]" unfolding upt_nc_177 .
  then show "oc_sub None j" using oc_nc_2832 oc_nc_2833 oc_nc_2834 oc_nc_2835 oc_nc_2836 oc_nc_2837 oc_nc_2838 oc_nc_2839 oc_nc_2840 oc_nc_2841 oc_nc_2842 oc_nc_2843 oc_nc_2844 oc_nc_2845 oc_nc_2846 oc_nc_2847
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
