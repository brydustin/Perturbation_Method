theory GOCX_nc_181
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2896: "goc_sub None 2896"
  by (goc_eval goc_nc_2896)

lemma goc_nc_2897: "goc_sub None 2897"
  by (goc_eval goc_nc_2897)

lemma goc_nc_2898: "goc_sub None 2898"
  by (goc_eval goc_nc_2898)

lemma goc_nc_2899: "goc_sub None 2899"
  by (goc_eval goc_nc_2899)

lemma goc_nc_2900: "goc_sub None 2900"
  by (goc_eval goc_nc_2900)

lemma goc_nc_2901: "goc_sub None 2901"
  by (goc_eval goc_nc_2901)

lemma goc_nc_2902: "goc_sub None 2902"
  by (goc_eval goc_nc_2902)

lemma goc_nc_2903: "goc_sub None 2903"
  by (goc_eval goc_nc_2903)

lemma goc_nc_2904: "goc_sub None 2904"
  by (goc_eval goc_nc_2904)

lemma goc_nc_2905: "goc_sub None 2905"
  by (goc_eval goc_nc_2905)

lemma goc_nc_2906: "goc_sub None 2906"
  by (goc_eval goc_nc_2906)

lemma goc_nc_2907: "goc_sub None 2907"
  by (goc_eval goc_nc_2907)

lemma goc_nc_2908: "goc_sub None 2908"
  by (goc_eval goc_nc_2908)

lemma goc_nc_2909: "goc_sub None 2909"
  by (goc_eval goc_nc_2909)

lemma goc_nc_2910: "goc_sub None 2910"
  by (goc_eval goc_nc_2910)

lemma goc_nc_2911: "goc_sub None 2911"
  by (goc_eval goc_nc_2911)

lemma gupt_nc_181: "[2896..<2912] = [2896, 2897, 2898, 2899, 2900, 2901, 2902, 2903, 2904, 2905, 2906, 2907, 2908, 2909, 2910, 2911]"
  by (simp add: upt_rec)

lemma gsec_nc_181: "\<forall>j\<in>{16 * 181..<16 * 181 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 181..<16 * 181 + 16}"
  then have "j \<in> set [2896..<2912]" unfolding set_upt by simp
  then have "j \<in> set [2896, 2897, 2898, 2899, 2900, 2901, 2902, 2903, 2904, 2905, 2906, 2907, 2908, 2909, 2910, 2911]" unfolding gupt_nc_181 .
  then show "goc_sub None j" using goc_nc_2896 goc_nc_2897 goc_nc_2898 goc_nc_2899 goc_nc_2900 goc_nc_2901 goc_nc_2902 goc_nc_2903 goc_nc_2904 goc_nc_2905 goc_nc_2906 goc_nc_2907 goc_nc_2908 goc_nc_2909 goc_nc_2910 goc_nc_2911
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
