theory GOCX_nc_121
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1936: "goc_sub None 1936"
  by (goc_eval goc_nc_1936)

lemma goc_nc_1937: "goc_sub None 1937"
  by (goc_eval goc_nc_1937)

lemma goc_nc_1938: "goc_sub None 1938"
  by (goc_eval goc_nc_1938)

lemma goc_nc_1939: "goc_sub None 1939"
  by (goc_eval goc_nc_1939)

lemma goc_nc_1940: "goc_sub None 1940"
  by (goc_eval goc_nc_1940)

lemma goc_nc_1941: "goc_sub None 1941"
  by (goc_eval goc_nc_1941)

lemma goc_nc_1942: "goc_sub None 1942"
  by (goc_eval goc_nc_1942)

lemma goc_nc_1943: "goc_sub None 1943"
  by (goc_eval goc_nc_1943)

lemma goc_nc_1944: "goc_sub None 1944"
  by (goc_eval goc_nc_1944)

lemma goc_nc_1945: "goc_sub None 1945"
  by (goc_eval goc_nc_1945)

lemma goc_nc_1946: "goc_sub None 1946"
  by (goc_eval goc_nc_1946)

lemma goc_nc_1947: "goc_sub None 1947"
  by (goc_eval goc_nc_1947)

lemma goc_nc_1948: "goc_sub None 1948"
  by (goc_eval goc_nc_1948)

lemma goc_nc_1949: "goc_sub None 1949"
  by (goc_eval goc_nc_1949)

lemma goc_nc_1950: "goc_sub None 1950"
  by (goc_eval goc_nc_1950)

lemma goc_nc_1951: "goc_sub None 1951"
  by (goc_eval goc_nc_1951)

lemma gupt_nc_121: "[1936..<1952] = [1936, 1937, 1938, 1939, 1940, 1941, 1942, 1943, 1944, 1945, 1946, 1947, 1948, 1949, 1950, 1951]"
  by (simp add: upt_rec)

lemma gsec_nc_121: "\<forall>j\<in>{16 * 121..<16 * 121 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 121..<16 * 121 + 16}"
  then have "j \<in> set [1936..<1952]" unfolding set_upt by simp
  then have "j \<in> set [1936, 1937, 1938, 1939, 1940, 1941, 1942, 1943, 1944, 1945, 1946, 1947, 1948, 1949, 1950, 1951]" unfolding gupt_nc_121 .
  then show "goc_sub None j" using goc_nc_1936 goc_nc_1937 goc_nc_1938 goc_nc_1939 goc_nc_1940 goc_nc_1941 goc_nc_1942 goc_nc_1943 goc_nc_1944 goc_nc_1945 goc_nc_1946 goc_nc_1947 goc_nc_1948 goc_nc_1949 goc_nc_1950 goc_nc_1951
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
