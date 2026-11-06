theory OCX_nc_181
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2896: "oc_sub None 2896"
  by (oc_eval oc_nc_2896)

lemma oc_nc_2897: "oc_sub None 2897"
  by (oc_eval oc_nc_2897)

lemma oc_nc_2898: "oc_sub None 2898"
  by (oc_eval oc_nc_2898)

lemma oc_nc_2899: "oc_sub None 2899"
  by (oc_eval oc_nc_2899)

lemma oc_nc_2900: "oc_sub None 2900"
  by (oc_eval oc_nc_2900)

lemma oc_nc_2901: "oc_sub None 2901"
  by (oc_eval oc_nc_2901)

lemma oc_nc_2902: "oc_sub None 2902"
  by (oc_eval oc_nc_2902)

lemma oc_nc_2903: "oc_sub None 2903"
  by (oc_eval oc_nc_2903)

lemma oc_nc_2904: "oc_sub None 2904"
  by (oc_eval oc_nc_2904)

lemma oc_nc_2905: "oc_sub None 2905"
  by (oc_eval oc_nc_2905)

lemma oc_nc_2906: "oc_sub None 2906"
  by (oc_eval oc_nc_2906)

lemma oc_nc_2907: "oc_sub None 2907"
  by (oc_eval oc_nc_2907)

lemma oc_nc_2908: "oc_sub None 2908"
  by (oc_eval oc_nc_2908)

lemma oc_nc_2909: "oc_sub None 2909"
  by (oc_eval oc_nc_2909)

lemma oc_nc_2910: "oc_sub None 2910"
  by (oc_eval oc_nc_2910)

lemma oc_nc_2911: "oc_sub None 2911"
  by (oc_eval oc_nc_2911)

lemma upt_nc_181: "[2896..<2912] = [2896, 2897, 2898, 2899, 2900, 2901, 2902, 2903, 2904, 2905, 2906, 2907, 2908, 2909, 2910, 2911]"
  by (simp add: upt_rec)

lemma sec_nc_181: "\<forall>j\<in>{16 * 181..<16 * 181 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 181..<16 * 181 + 16}"
  then have "j \<in> set [2896..<2912]" unfolding set_upt by simp
  then have "j \<in> set [2896, 2897, 2898, 2899, 2900, 2901, 2902, 2903, 2904, 2905, 2906, 2907, 2908, 2909, 2910, 2911]" unfolding upt_nc_181 .
  then show "oc_sub None j" using oc_nc_2896 oc_nc_2897 oc_nc_2898 oc_nc_2899 oc_nc_2900 oc_nc_2901 oc_nc_2902 oc_nc_2903 oc_nc_2904 oc_nc_2905 oc_nc_2906 oc_nc_2907 oc_nc_2908 oc_nc_2909 oc_nc_2910 oc_nc_2911
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
