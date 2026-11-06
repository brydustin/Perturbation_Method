theory GOCX_nc_183
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2928: "goc_sub None 2928"
  by (goc_eval goc_nc_2928)

lemma goc_nc_2929: "goc_sub None 2929"
  by (goc_eval goc_nc_2929)

lemma goc_nc_2930: "goc_sub None 2930"
  by (goc_eval goc_nc_2930)

lemma goc_nc_2931: "goc_sub None 2931"
  by (goc_eval goc_nc_2931)

lemma goc_nc_2932: "goc_sub None 2932"
  by (goc_eval goc_nc_2932)

lemma goc_nc_2933: "goc_sub None 2933"
  by (goc_eval goc_nc_2933)

lemma goc_nc_2934: "goc_sub None 2934"
  by (goc_eval goc_nc_2934)

lemma goc_nc_2935: "goc_sub None 2935"
  by (goc_eval goc_nc_2935)

lemma goc_nc_2936: "goc_sub None 2936"
  by (goc_eval goc_nc_2936)

lemma goc_nc_2937: "goc_sub None 2937"
  by (goc_eval goc_nc_2937)

lemma goc_nc_2938: "goc_sub None 2938"
  by (goc_eval goc_nc_2938)

lemma goc_nc_2939: "goc_sub None 2939"
  by (goc_eval goc_nc_2939)

lemma goc_nc_2940: "goc_sub None 2940"
  by (goc_eval goc_nc_2940)

lemma goc_nc_2941: "goc_sub None 2941"
  by (goc_eval goc_nc_2941)

lemma goc_nc_2942: "goc_sub None 2942"
  by (goc_eval goc_nc_2942)

lemma goc_nc_2943: "goc_sub None 2943"
  by (goc_eval goc_nc_2943)

lemma gupt_nc_183: "[2928..<2944] = [2928, 2929, 2930, 2931, 2932, 2933, 2934, 2935, 2936, 2937, 2938, 2939, 2940, 2941, 2942, 2943]"
  by (simp add: upt_rec)

lemma gsec_nc_183: "\<forall>j\<in>{16 * 183..<16 * 183 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 183..<16 * 183 + 16}"
  then have "j \<in> set [2928..<2944]" unfolding set_upt by simp
  then have "j \<in> set [2928, 2929, 2930, 2931, 2932, 2933, 2934, 2935, 2936, 2937, 2938, 2939, 2940, 2941, 2942, 2943]" unfolding gupt_nc_183 .
  then show "goc_sub None j" using goc_nc_2928 goc_nc_2929 goc_nc_2930 goc_nc_2931 goc_nc_2932 goc_nc_2933 goc_nc_2934 goc_nc_2935 goc_nc_2936 goc_nc_2937 goc_nc_2938 goc_nc_2939 goc_nc_2940 goc_nc_2941 goc_nc_2942 goc_nc_2943
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
