theory OCX_c30_183
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2928: "oc_sub oc_b30 2928"
  by (oc_eval oc_c30_2928)

lemma oc_c30_2929: "oc_sub oc_b30 2929"
  by (oc_eval oc_c30_2929)

lemma oc_c30_2930: "oc_sub oc_b30 2930"
  by (oc_eval oc_c30_2930)

lemma oc_c30_2931: "oc_sub oc_b30 2931"
  by (oc_eval oc_c30_2931)

lemma oc_c30_2932: "oc_sub oc_b30 2932"
  by (oc_eval oc_c30_2932)

lemma oc_c30_2933: "oc_sub oc_b30 2933"
  by (oc_eval oc_c30_2933)

lemma oc_c30_2934: "oc_sub oc_b30 2934"
  by (oc_eval oc_c30_2934)

lemma oc_c30_2935: "oc_sub oc_b30 2935"
  by (oc_eval oc_c30_2935)

lemma oc_c30_2936: "oc_sub oc_b30 2936"
  by (oc_eval oc_c30_2936)

lemma oc_c30_2937: "oc_sub oc_b30 2937"
  by (oc_eval oc_c30_2937)

lemma oc_c30_2938: "oc_sub oc_b30 2938"
  by (oc_eval oc_c30_2938)

lemma oc_c30_2939: "oc_sub oc_b30 2939"
  by (oc_eval oc_c30_2939)

lemma oc_c30_2940: "oc_sub oc_b30 2940"
  by (oc_eval oc_c30_2940)

lemma oc_c30_2941: "oc_sub oc_b30 2941"
  by (oc_eval oc_c30_2941)

lemma oc_c30_2942: "oc_sub oc_b30 2942"
  by (oc_eval oc_c30_2942)

lemma oc_c30_2943: "oc_sub oc_b30 2943"
  by (oc_eval oc_c30_2943)

lemma upt_c30_183: "[2928..<2944] = [2928, 2929, 2930, 2931, 2932, 2933, 2934, 2935, 2936, 2937, 2938, 2939, 2940, 2941, 2942, 2943]"
  by (simp add: upt_rec)

lemma sec_c30_183: "\<forall>j\<in>{16 * 183..<16 * 183 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 183..<16 * 183 + 16}"
  then have "j \<in> set [2928..<2944]" unfolding set_upt by simp
  then have "j \<in> set [2928, 2929, 2930, 2931, 2932, 2933, 2934, 2935, 2936, 2937, 2938, 2939, 2940, 2941, 2942, 2943]" unfolding upt_c30_183 .
  then show "oc_sub oc_b30 j" using oc_c30_2928 oc_c30_2929 oc_c30_2930 oc_c30_2931 oc_c30_2932 oc_c30_2933 oc_c30_2934 oc_c30_2935 oc_c30_2936 oc_c30_2937 oc_c30_2938 oc_c30_2939 oc_c30_2940 oc_c30_2941 oc_c30_2942 oc_c30_2943
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
