theory DCX_nc_121
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1936: "dc_sub None 1936"
  by (dc_eval dc_nc_1936)

lemma dc_nc_1937: "dc_sub None 1937"
  by (dc_eval dc_nc_1937)

lemma dc_nc_1938: "dc_sub None 1938"
  by (dc_eval dc_nc_1938)

lemma dc_nc_1939: "dc_sub None 1939"
  by (dc_eval dc_nc_1939)

lemma dc_nc_1940: "dc_sub None 1940"
  by (dc_eval dc_nc_1940)

lemma dc_nc_1941: "dc_sub None 1941"
  by (dc_eval dc_nc_1941)

lemma dc_nc_1942: "dc_sub None 1942"
  by (dc_eval dc_nc_1942)

lemma dc_nc_1943: "dc_sub None 1943"
  by (dc_eval dc_nc_1943)

lemma dc_nc_1944: "dc_sub None 1944"
  by (dc_eval dc_nc_1944)

lemma dc_nc_1945: "dc_sub None 1945"
  by (dc_eval dc_nc_1945)

lemma dc_nc_1946: "dc_sub None 1946"
  by (dc_eval dc_nc_1946)

lemma dc_nc_1947: "dc_sub None 1947"
  by (dc_eval dc_nc_1947)

lemma dc_nc_1948: "dc_sub None 1948"
  by (dc_eval dc_nc_1948)

lemma dc_nc_1949: "dc_sub None 1949"
  by (dc_eval dc_nc_1949)

lemma dc_nc_1950: "dc_sub None 1950"
  by (dc_eval dc_nc_1950)

lemma dc_nc_1951: "dc_sub None 1951"
  by (dc_eval dc_nc_1951)

lemma upt_nc_121: "[1936..<1952] = [1936, 1937, 1938, 1939, 1940, 1941, 1942, 1943, 1944, 1945, 1946, 1947, 1948, 1949, 1950, 1951]"
  by (simp add: upt_rec)

lemma sec_nc_121: "\<forall>j\<in>{16 * 121..<16 * 121 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 121..<16 * 121 + 16}"
  then have "j \<in> set [1936..<1952]" unfolding set_upt by simp
  then have "j \<in> set [1936, 1937, 1938, 1939, 1940, 1941, 1942, 1943, 1944, 1945, 1946, 1947, 1948, 1949, 1950, 1951]" unfolding upt_nc_121 .
  then show "dc_sub None j" using dc_nc_1936 dc_nc_1937 dc_nc_1938 dc_nc_1939 dc_nc_1940 dc_nc_1941 dc_nc_1942 dc_nc_1943 dc_nc_1944 dc_nc_1945 dc_nc_1946 dc_nc_1947 dc_nc_1948 dc_nc_1949 dc_nc_1950 dc_nc_1951
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
