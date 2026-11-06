theory OCX_nc_183
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2928: "oc_sub None 2928"
  by (oc_eval oc_nc_2928)

lemma oc_nc_2929: "oc_sub None 2929"
  by (oc_eval oc_nc_2929)

lemma oc_nc_2930: "oc_sub None 2930"
  by (oc_eval oc_nc_2930)

lemma oc_nc_2931: "oc_sub None 2931"
  by (oc_eval oc_nc_2931)

lemma oc_nc_2932: "oc_sub None 2932"
  by (oc_eval oc_nc_2932)

lemma oc_nc_2933: "oc_sub None 2933"
  by (oc_eval oc_nc_2933)

lemma oc_nc_2934: "oc_sub None 2934"
  by (oc_eval oc_nc_2934)

lemma oc_nc_2935: "oc_sub None 2935"
  by (oc_eval oc_nc_2935)

lemma oc_nc_2936: "oc_sub None 2936"
  by (oc_eval oc_nc_2936)

lemma oc_nc_2937: "oc_sub None 2937"
  by (oc_eval oc_nc_2937)

lemma oc_nc_2938: "oc_sub None 2938"
  by (oc_eval oc_nc_2938)

lemma oc_nc_2939: "oc_sub None 2939"
  by (oc_eval oc_nc_2939)

lemma oc_nc_2940: "oc_sub None 2940"
  by (oc_eval oc_nc_2940)

lemma oc_nc_2941: "oc_sub None 2941"
  by (oc_eval oc_nc_2941)

lemma oc_nc_2942: "oc_sub None 2942"
  by (oc_eval oc_nc_2942)

lemma oc_nc_2943: "oc_sub None 2943"
  by (oc_eval oc_nc_2943)

lemma upt_nc_183: "[2928..<2944] = [2928, 2929, 2930, 2931, 2932, 2933, 2934, 2935, 2936, 2937, 2938, 2939, 2940, 2941, 2942, 2943]"
  by (simp add: upt_rec)

lemma sec_nc_183: "\<forall>j\<in>{16 * 183..<16 * 183 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 183..<16 * 183 + 16}"
  then have "j \<in> set [2928..<2944]" unfolding set_upt by simp
  then have "j \<in> set [2928, 2929, 2930, 2931, 2932, 2933, 2934, 2935, 2936, 2937, 2938, 2939, 2940, 2941, 2942, 2943]" unfolding upt_nc_183 .
  then show "oc_sub None j" using oc_nc_2928 oc_nc_2929 oc_nc_2930 oc_nc_2931 oc_nc_2932 oc_nc_2933 oc_nc_2934 oc_nc_2935 oc_nc_2936 oc_nc_2937 oc_nc_2938 oc_nc_2939 oc_nc_2940 oc_nc_2941 oc_nc_2942 oc_nc_2943
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
