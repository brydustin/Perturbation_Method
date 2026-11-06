theory OCX_c30_177
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2832: "oc_sub oc_b30 2832"
  by (oc_eval oc_c30_2832)

lemma oc_c30_2833: "oc_sub oc_b30 2833"
  by (oc_eval oc_c30_2833)

lemma oc_c30_2834: "oc_sub oc_b30 2834"
  by (oc_eval oc_c30_2834)

lemma oc_c30_2835: "oc_sub oc_b30 2835"
  by (oc_eval oc_c30_2835)

lemma oc_c30_2836: "oc_sub oc_b30 2836"
  by (oc_eval oc_c30_2836)

lemma oc_c30_2837: "oc_sub oc_b30 2837"
  by (oc_eval oc_c30_2837)

lemma oc_c30_2838: "oc_sub oc_b30 2838"
  by (oc_eval oc_c30_2838)

lemma oc_c30_2839: "oc_sub oc_b30 2839"
  by (oc_eval oc_c30_2839)

lemma oc_c30_2840: "oc_sub oc_b30 2840"
  by (oc_eval oc_c30_2840)

lemma oc_c30_2841: "oc_sub oc_b30 2841"
  by (oc_eval oc_c30_2841)

lemma oc_c30_2842: "oc_sub oc_b30 2842"
  by (oc_eval oc_c30_2842)

lemma oc_c30_2843: "oc_sub oc_b30 2843"
  by (oc_eval oc_c30_2843)

lemma oc_c30_2844: "oc_sub oc_b30 2844"
  by (oc_eval oc_c30_2844)

lemma oc_c30_2845: "oc_sub oc_b30 2845"
  by (oc_eval oc_c30_2845)

lemma oc_c30_2846: "oc_sub oc_b30 2846"
  by (oc_eval oc_c30_2846)

lemma oc_c30_2847: "oc_sub oc_b30 2847"
  by (oc_eval oc_c30_2847)

lemma upt_c30_177: "[2832..<2848] = [2832, 2833, 2834, 2835, 2836, 2837, 2838, 2839, 2840, 2841, 2842, 2843, 2844, 2845, 2846, 2847]"
  by (simp add: upt_rec)

lemma sec_c30_177: "\<forall>j\<in>{16 * 177..<16 * 177 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 177..<16 * 177 + 16}"
  then have "j \<in> set [2832..<2848]" unfolding set_upt by simp
  then have "j \<in> set [2832, 2833, 2834, 2835, 2836, 2837, 2838, 2839, 2840, 2841, 2842, 2843, 2844, 2845, 2846, 2847]" unfolding upt_c30_177 .
  then show "oc_sub oc_b30 j" using oc_c30_2832 oc_c30_2833 oc_c30_2834 oc_c30_2835 oc_c30_2836 oc_c30_2837 oc_c30_2838 oc_c30_2839 oc_c30_2840 oc_c30_2841 oc_c30_2842 oc_c30_2843 oc_c30_2844 oc_c30_2845 oc_c30_2846 oc_c30_2847
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
