theory GDCX_nc_181
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2896: "gdc_sub None 2896"
  by (gdc_eval gdc_nc_2896)

lemma gdc_nc_2897: "gdc_sub None 2897"
  by (gdc_eval gdc_nc_2897)

lemma gdc_nc_2898: "gdc_sub None 2898"
  by (gdc_eval gdc_nc_2898)

lemma gdc_nc_2899: "gdc_sub None 2899"
  by (gdc_eval gdc_nc_2899)

lemma gdc_nc_2900: "gdc_sub None 2900"
  by (gdc_eval gdc_nc_2900)

lemma gdc_nc_2901: "gdc_sub None 2901"
  by (gdc_eval gdc_nc_2901)

lemma gdc_nc_2902: "gdc_sub None 2902"
  by (gdc_eval gdc_nc_2902)

lemma gdc_nc_2903: "gdc_sub None 2903"
  by (gdc_eval gdc_nc_2903)

lemma gdc_nc_2904: "gdc_sub None 2904"
  by (gdc_eval gdc_nc_2904)

lemma gdc_nc_2905: "gdc_sub None 2905"
  by (gdc_eval gdc_nc_2905)

lemma gdc_nc_2906: "gdc_sub None 2906"
  by (gdc_eval gdc_nc_2906)

lemma gdc_nc_2907: "gdc_sub None 2907"
  by (gdc_eval gdc_nc_2907)

lemma gdc_nc_2908: "gdc_sub None 2908"
  by (gdc_eval gdc_nc_2908)

lemma gdc_nc_2909: "gdc_sub None 2909"
  by (gdc_eval gdc_nc_2909)

lemma gdc_nc_2910: "gdc_sub None 2910"
  by (gdc_eval gdc_nc_2910)

lemma gdc_nc_2911: "gdc_sub None 2911"
  by (gdc_eval gdc_nc_2911)

lemma gupt_nc_181: "[2896..<2912] = [2896, 2897, 2898, 2899, 2900, 2901, 2902, 2903, 2904, 2905, 2906, 2907, 2908, 2909, 2910, 2911]"
  by (simp add: upt_rec)

lemma gsec_nc_181: "\<forall>j\<in>{16 * 181..<16 * 181 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 181..<16 * 181 + 16}"
  then have "j \<in> set [2896..<2912]" unfolding set_upt by simp
  then have "j \<in> set [2896, 2897, 2898, 2899, 2900, 2901, 2902, 2903, 2904, 2905, 2906, 2907, 2908, 2909, 2910, 2911]" unfolding gupt_nc_181 .
  then show "gdc_sub None j" using gdc_nc_2896 gdc_nc_2897 gdc_nc_2898 gdc_nc_2899 gdc_nc_2900 gdc_nc_2901 gdc_nc_2902 gdc_nc_2903 gdc_nc_2904 gdc_nc_2905 gdc_nc_2906 gdc_nc_2907 gdc_nc_2908 gdc_nc_2909 gdc_nc_2910 gdc_nc_2911
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
