theory OCX_c30_121
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1936: "oc_sub oc_b30 1936"
  by (oc_eval oc_c30_1936)

lemma oc_c30_1937: "oc_sub oc_b30 1937"
  by (oc_eval oc_c30_1937)

lemma oc_c30_1938: "oc_sub oc_b30 1938"
  by (oc_eval oc_c30_1938)

lemma oc_c30_1939: "oc_sub oc_b30 1939"
  by (oc_eval oc_c30_1939)

lemma oc_c30_1940: "oc_sub oc_b30 1940"
  by (oc_eval oc_c30_1940)

lemma oc_c30_1941: "oc_sub oc_b30 1941"
  by (oc_eval oc_c30_1941)

lemma oc_c30_1942: "oc_sub oc_b30 1942"
  by (oc_eval oc_c30_1942)

lemma oc_c30_1943: "oc_sub oc_b30 1943"
  by (oc_eval oc_c30_1943)

lemma oc_c30_1944: "oc_sub oc_b30 1944"
  by (oc_eval oc_c30_1944)

lemma oc_c30_1945: "oc_sub oc_b30 1945"
  by (oc_eval oc_c30_1945)

lemma oc_c30_1946: "oc_sub oc_b30 1946"
  by (oc_eval oc_c30_1946)

lemma oc_c30_1947: "oc_sub oc_b30 1947"
  by (oc_eval oc_c30_1947)

lemma oc_c30_1948: "oc_sub oc_b30 1948"
  by (oc_eval oc_c30_1948)

lemma oc_c30_1949: "oc_sub oc_b30 1949"
  by (oc_eval oc_c30_1949)

lemma oc_c30_1950: "oc_sub oc_b30 1950"
  by (oc_eval oc_c30_1950)

lemma oc_c30_1951: "oc_sub oc_b30 1951"
  by (oc_eval oc_c30_1951)

lemma upt_c30_121: "[1936..<1952] = [1936, 1937, 1938, 1939, 1940, 1941, 1942, 1943, 1944, 1945, 1946, 1947, 1948, 1949, 1950, 1951]"
  by (simp add: upt_rec)

lemma sec_c30_121: "\<forall>j\<in>{16 * 121..<16 * 121 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 121..<16 * 121 + 16}"
  then have "j \<in> set [1936..<1952]" unfolding set_upt by simp
  then have "j \<in> set [1936, 1937, 1938, 1939, 1940, 1941, 1942, 1943, 1944, 1945, 1946, 1947, 1948, 1949, 1950, 1951]" unfolding upt_c30_121 .
  then show "oc_sub oc_b30 j" using oc_c30_1936 oc_c30_1937 oc_c30_1938 oc_c30_1939 oc_c30_1940 oc_c30_1941 oc_c30_1942 oc_c30_1943 oc_c30_1944 oc_c30_1945 oc_c30_1946 oc_c30_1947 oc_c30_1948 oc_c30_1949 oc_c30_1950 oc_c30_1951
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
