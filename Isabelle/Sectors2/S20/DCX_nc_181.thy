theory DCX_nc_181
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2896: "dc_sub None 2896"
  by (dc_eval dc_nc_2896)

lemma dc_nc_2897: "dc_sub None 2897"
  by (dc_eval dc_nc_2897)

lemma dc_nc_2898: "dc_sub None 2898"
  by (dc_eval dc_nc_2898)

lemma dc_nc_2899: "dc_sub None 2899"
  by (dc_eval dc_nc_2899)

lemma dc_nc_2900: "dc_sub None 2900"
  by (dc_eval dc_nc_2900)

lemma dc_nc_2901: "dc_sub None 2901"
  by (dc_eval dc_nc_2901)

lemma dc_nc_2902: "dc_sub None 2902"
  by (dc_eval dc_nc_2902)

lemma dc_nc_2903: "dc_sub None 2903"
  by (dc_eval dc_nc_2903)

lemma dc_nc_2904: "dc_sub None 2904"
  by (dc_eval dc_nc_2904)

lemma dc_nc_2905: "dc_sub None 2905"
  by (dc_eval dc_nc_2905)

lemma dc_nc_2906: "dc_sub None 2906"
  by (dc_eval dc_nc_2906)

lemma dc_nc_2907: "dc_sub None 2907"
  by (dc_eval dc_nc_2907)

lemma dc_nc_2908: "dc_sub None 2908"
  by (dc_eval dc_nc_2908)

lemma dc_nc_2909: "dc_sub None 2909"
  by (dc_eval dc_nc_2909)

lemma dc_nc_2910: "dc_sub None 2910"
  by (dc_eval dc_nc_2910)

lemma dc_nc_2911: "dc_sub None 2911"
  by (dc_eval dc_nc_2911)

lemma upt_nc_181: "[2896..<2912] = [2896, 2897, 2898, 2899, 2900, 2901, 2902, 2903, 2904, 2905, 2906, 2907, 2908, 2909, 2910, 2911]"
  by (simp add: upt_rec)

lemma sec_nc_181: "\<forall>j\<in>{16 * 181..<16 * 181 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 181..<16 * 181 + 16}"
  then have "j \<in> set [2896..<2912]" unfolding set_upt by simp
  then have "j \<in> set [2896, 2897, 2898, 2899, 2900, 2901, 2902, 2903, 2904, 2905, 2906, 2907, 2908, 2909, 2910, 2911]" unfolding upt_nc_181 .
  then show "dc_sub None j" using dc_nc_2896 dc_nc_2897 dc_nc_2898 dc_nc_2899 dc_nc_2900 dc_nc_2901 dc_nc_2902 dc_nc_2903 dc_nc_2904 dc_nc_2905 dc_nc_2906 dc_nc_2907 dc_nc_2908 dc_nc_2909 dc_nc_2910 dc_nc_2911
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
