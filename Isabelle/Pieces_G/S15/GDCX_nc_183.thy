theory GDCX_nc_183
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2928: "gdc_sub None 2928"
  by (gdc_eval gdc_nc_2928)

lemma gdc_nc_2929: "gdc_sub None 2929"
  by (gdc_eval gdc_nc_2929)

lemma gdc_nc_2930: "gdc_sub None 2930"
  by (gdc_eval gdc_nc_2930)

lemma gdc_nc_2931: "gdc_sub None 2931"
  by (gdc_eval gdc_nc_2931)

lemma gdc_nc_2932: "gdc_sub None 2932"
  by (gdc_eval gdc_nc_2932)

lemma gdc_nc_2933: "gdc_sub None 2933"
  by (gdc_eval gdc_nc_2933)

lemma gdc_nc_2934: "gdc_sub None 2934"
  by (gdc_eval gdc_nc_2934)

lemma gdc_nc_2935: "gdc_sub None 2935"
  by (gdc_eval gdc_nc_2935)

lemma gdc_nc_2936: "gdc_sub None 2936"
  by (gdc_eval gdc_nc_2936)

lemma gdc_nc_2937: "gdc_sub None 2937"
  by (gdc_eval gdc_nc_2937)

lemma gdc_nc_2938: "gdc_sub None 2938"
  by (gdc_eval gdc_nc_2938)

lemma gdc_nc_2939: "gdc_sub None 2939"
  by (gdc_eval gdc_nc_2939)

lemma gdc_nc_2940: "gdc_sub None 2940"
  by (gdc_eval gdc_nc_2940)

lemma gdc_nc_2941: "gdc_sub None 2941"
  by (gdc_eval gdc_nc_2941)

lemma gdc_nc_2942: "gdc_sub None 2942"
  by (gdc_eval gdc_nc_2942)

lemma gdc_nc_2943: "gdc_sub None 2943"
  by (gdc_eval gdc_nc_2943)

lemma gupt_nc_183: "[2928..<2944] = [2928, 2929, 2930, 2931, 2932, 2933, 2934, 2935, 2936, 2937, 2938, 2939, 2940, 2941, 2942, 2943]"
  by (simp add: upt_rec)

lemma gsec_nc_183: "\<forall>j\<in>{16 * 183..<16 * 183 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 183..<16 * 183 + 16}"
  then have "j \<in> set [2928..<2944]" unfolding set_upt by simp
  then have "j \<in> set [2928, 2929, 2930, 2931, 2932, 2933, 2934, 2935, 2936, 2937, 2938, 2939, 2940, 2941, 2942, 2943]" unfolding gupt_nc_183 .
  then show "gdc_sub None j" using gdc_nc_2928 gdc_nc_2929 gdc_nc_2930 gdc_nc_2931 gdc_nc_2932 gdc_nc_2933 gdc_nc_2934 gdc_nc_2935 gdc_nc_2936 gdc_nc_2937 gdc_nc_2938 gdc_nc_2939 gdc_nc_2940 gdc_nc_2941 gdc_nc_2942 gdc_nc_2943
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
