theory DCX_c30_177
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2832: "dc_sub dc_b30 2832"
  by (dc_eval dc_c30_2832)

lemma dc_c30_2833: "dc_sub dc_b30 2833"
  by (dc_eval dc_c30_2833)

lemma dc_c30_2834: "dc_sub dc_b30 2834"
  by (dc_eval dc_c30_2834)

lemma dc_c30_2835: "dc_sub dc_b30 2835"
  by (dc_eval dc_c30_2835)

lemma dc_c30_2836: "dc_sub dc_b30 2836"
  by (dc_eval dc_c30_2836)

lemma dc_c30_2837: "dc_sub dc_b30 2837"
  by (dc_eval dc_c30_2837)

lemma dc_c30_2838: "dc_sub dc_b30 2838"
  by (dc_eval dc_c30_2838)

lemma dc_c30_2839: "dc_sub dc_b30 2839"
  by (dc_eval dc_c30_2839)

lemma dc_c30_2840: "dc_sub dc_b30 2840"
  by (dc_eval dc_c30_2840)

lemma dc_c30_2841: "dc_sub dc_b30 2841"
  by (dc_eval dc_c30_2841)

lemma dc_c30_2842: "dc_sub dc_b30 2842"
  by (dc_eval dc_c30_2842)

lemma dc_c30_2843: "dc_sub dc_b30 2843"
  by (dc_eval dc_c30_2843)

lemma dc_c30_2844: "dc_sub dc_b30 2844"
  by (dc_eval dc_c30_2844)

lemma dc_c30_2845: "dc_sub dc_b30 2845"
  by (dc_eval dc_c30_2845)

lemma dc_c30_2846: "dc_sub dc_b30 2846"
  by (dc_eval dc_c30_2846)

lemma dc_c30_2847: "dc_sub dc_b30 2847"
  by (dc_eval dc_c30_2847)

lemma upt_c30_177: "[2832..<2848] = [2832, 2833, 2834, 2835, 2836, 2837, 2838, 2839, 2840, 2841, 2842, 2843, 2844, 2845, 2846, 2847]"
  by (simp add: upt_rec)

lemma sec_c30_177: "\<forall>j\<in>{16 * 177..<16 * 177 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 177..<16 * 177 + 16}"
  then have "j \<in> set [2832..<2848]" unfolding set_upt by simp
  then have "j \<in> set [2832, 2833, 2834, 2835, 2836, 2837, 2838, 2839, 2840, 2841, 2842, 2843, 2844, 2845, 2846, 2847]" unfolding upt_c30_177 .
  then show "dc_sub dc_b30 j" using dc_c30_2832 dc_c30_2833 dc_c30_2834 dc_c30_2835 dc_c30_2836 dc_c30_2837 dc_c30_2838 dc_c30_2839 dc_c30_2840 dc_c30_2841 dc_c30_2842 dc_c30_2843 dc_c30_2844 dc_c30_2845 dc_c30_2846 dc_c30_2847
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
