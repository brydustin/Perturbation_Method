theory DCX_c30_181
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2896: "dc_sub dc_b30 2896"
  by (dc_eval dc_c30_2896)

lemma dc_c30_2897: "dc_sub dc_b30 2897"
  by (dc_eval dc_c30_2897)

lemma dc_c30_2898: "dc_sub dc_b30 2898"
  by (dc_eval dc_c30_2898)

lemma dc_c30_2899: "dc_sub dc_b30 2899"
  by (dc_eval dc_c30_2899)

lemma dc_c30_2900: "dc_sub dc_b30 2900"
  by (dc_eval dc_c30_2900)

lemma dc_c30_2901: "dc_sub dc_b30 2901"
  by (dc_eval dc_c30_2901)

lemma dc_c30_2902: "dc_sub dc_b30 2902"
  by (dc_eval dc_c30_2902)

lemma dc_c30_2903: "dc_sub dc_b30 2903"
  by (dc_eval dc_c30_2903)

lemma dc_c30_2904: "dc_sub dc_b30 2904"
  by (dc_eval dc_c30_2904)

lemma dc_c30_2905: "dc_sub dc_b30 2905"
  by (dc_eval dc_c30_2905)

lemma dc_c30_2906: "dc_sub dc_b30 2906"
  by (dc_eval dc_c30_2906)

lemma dc_c30_2907: "dc_sub dc_b30 2907"
  by (dc_eval dc_c30_2907)

lemma dc_c30_2908: "dc_sub dc_b30 2908"
  by (dc_eval dc_c30_2908)

lemma dc_c30_2909: "dc_sub dc_b30 2909"
  by (dc_eval dc_c30_2909)

lemma dc_c30_2910: "dc_sub dc_b30 2910"
  by (dc_eval dc_c30_2910)

lemma dc_c30_2911: "dc_sub dc_b30 2911"
  by (dc_eval dc_c30_2911)

lemma upt_c30_181: "[2896..<2912] = [2896, 2897, 2898, 2899, 2900, 2901, 2902, 2903, 2904, 2905, 2906, 2907, 2908, 2909, 2910, 2911]"
  by (simp add: upt_rec)

lemma sec_c30_181: "\<forall>j\<in>{16 * 181..<16 * 181 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 181..<16 * 181 + 16}"
  then have "j \<in> set [2896..<2912]" unfolding set_upt by simp
  then have "j \<in> set [2896, 2897, 2898, 2899, 2900, 2901, 2902, 2903, 2904, 2905, 2906, 2907, 2908, 2909, 2910, 2911]" unfolding upt_c30_181 .
  then show "dc_sub dc_b30 j" using dc_c30_2896 dc_c30_2897 dc_c30_2898 dc_c30_2899 dc_c30_2900 dc_c30_2901 dc_c30_2902 dc_c30_2903 dc_c30_2904 dc_c30_2905 dc_c30_2906 dc_c30_2907 dc_c30_2908 dc_c30_2909 dc_c30_2910 dc_c30_2911
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
