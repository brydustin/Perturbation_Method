theory GDCX_nc_121
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1936: "gdc_sub None 1936"
  by (gdc_eval gdc_nc_1936)

lemma gdc_nc_1937: "gdc_sub None 1937"
  by (gdc_eval gdc_nc_1937)

lemma gdc_nc_1938: "gdc_sub None 1938"
  by (gdc_eval gdc_nc_1938)

lemma gdc_nc_1939: "gdc_sub None 1939"
  by (gdc_eval gdc_nc_1939)

lemma gdc_nc_1940: "gdc_sub None 1940"
  by (gdc_eval gdc_nc_1940)

lemma gdc_nc_1941: "gdc_sub None 1941"
  by (gdc_eval gdc_nc_1941)

lemma gdc_nc_1942: "gdc_sub None 1942"
  by (gdc_eval gdc_nc_1942)

lemma gdc_nc_1943: "gdc_sub None 1943"
  by (gdc_eval gdc_nc_1943)

lemma gdc_nc_1944: "gdc_sub None 1944"
  by (gdc_eval gdc_nc_1944)

lemma gdc_nc_1945: "gdc_sub None 1945"
  by (gdc_eval gdc_nc_1945)

lemma gdc_nc_1946: "gdc_sub None 1946"
  by (gdc_eval gdc_nc_1946)

lemma gdc_nc_1947: "gdc_sub None 1947"
  by (gdc_eval gdc_nc_1947)

lemma gdc_nc_1948: "gdc_sub None 1948"
  by (gdc_eval gdc_nc_1948)

lemma gdc_nc_1949: "gdc_sub None 1949"
  by (gdc_eval gdc_nc_1949)

lemma gdc_nc_1950: "gdc_sub None 1950"
  by (gdc_eval gdc_nc_1950)

lemma gdc_nc_1951: "gdc_sub None 1951"
  by (gdc_eval gdc_nc_1951)

lemma gupt_nc_121: "[1936..<1952] = [1936, 1937, 1938, 1939, 1940, 1941, 1942, 1943, 1944, 1945, 1946, 1947, 1948, 1949, 1950, 1951]"
  by (simp add: upt_rec)

lemma gsec_nc_121: "\<forall>j\<in>{16 * 121..<16 * 121 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 121..<16 * 121 + 16}"
  then have "j \<in> set [1936..<1952]" unfolding set_upt by simp
  then have "j \<in> set [1936, 1937, 1938, 1939, 1940, 1941, 1942, 1943, 1944, 1945, 1946, 1947, 1948, 1949, 1950, 1951]" unfolding gupt_nc_121 .
  then show "gdc_sub None j" using gdc_nc_1936 gdc_nc_1937 gdc_nc_1938 gdc_nc_1939 gdc_nc_1940 gdc_nc_1941 gdc_nc_1942 gdc_nc_1943 gdc_nc_1944 gdc_nc_1945 gdc_nc_1946 gdc_nc_1947 gdc_nc_1948 gdc_nc_1949 gdc_nc_1950 gdc_nc_1951
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
