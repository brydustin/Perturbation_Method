theory DCX_c30_183
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2928: "dc_sub dc_b30 2928"
  by (dc_eval dc_c30_2928)

lemma dc_c30_2929: "dc_sub dc_b30 2929"
  by (dc_eval dc_c30_2929)

lemma dc_c30_2930: "dc_sub dc_b30 2930"
  by (dc_eval dc_c30_2930)

lemma dc_c30_2931: "dc_sub dc_b30 2931"
  by (dc_eval dc_c30_2931)

lemma dc_c30_2932: "dc_sub dc_b30 2932"
  by (dc_eval dc_c30_2932)

lemma dc_c30_2933: "dc_sub dc_b30 2933"
  by (dc_eval dc_c30_2933)

lemma dc_c30_2934: "dc_sub dc_b30 2934"
  by (dc_eval dc_c30_2934)

lemma dc_c30_2935: "dc_sub dc_b30 2935"
  by (dc_eval dc_c30_2935)

lemma dc_c30_2936: "dc_sub dc_b30 2936"
  by (dc_eval dc_c30_2936)

lemma dc_c30_2937: "dc_sub dc_b30 2937"
  by (dc_eval dc_c30_2937)

lemma dc_c30_2938: "dc_sub dc_b30 2938"
  by (dc_eval dc_c30_2938)

lemma dc_c30_2939: "dc_sub dc_b30 2939"
  by (dc_eval dc_c30_2939)

lemma dc_c30_2940: "dc_sub dc_b30 2940"
  by (dc_eval dc_c30_2940)

lemma dc_c30_2941: "dc_sub dc_b30 2941"
  by (dc_eval dc_c30_2941)

lemma dc_c30_2942: "dc_sub dc_b30 2942"
  by (dc_eval dc_c30_2942)

lemma dc_c30_2943: "dc_sub dc_b30 2943"
  by (dc_eval dc_c30_2943)

lemma upt_c30_183: "[2928..<2944] = [2928, 2929, 2930, 2931, 2932, 2933, 2934, 2935, 2936, 2937, 2938, 2939, 2940, 2941, 2942, 2943]"
  by (simp add: upt_rec)

lemma sec_c30_183: "\<forall>j\<in>{16 * 183..<16 * 183 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 183..<16 * 183 + 16}"
  then have "j \<in> set [2928..<2944]" unfolding set_upt by simp
  then have "j \<in> set [2928, 2929, 2930, 2931, 2932, 2933, 2934, 2935, 2936, 2937, 2938, 2939, 2940, 2941, 2942, 2943]" unfolding upt_c30_183 .
  then show "dc_sub dc_b30 j" using dc_c30_2928 dc_c30_2929 dc_c30_2930 dc_c30_2931 dc_c30_2932 dc_c30_2933 dc_c30_2934 dc_c30_2935 dc_c30_2936 dc_c30_2937 dc_c30_2938 dc_c30_2939 dc_c30_2940 dc_c30_2941 dc_c30_2942 dc_c30_2943
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
