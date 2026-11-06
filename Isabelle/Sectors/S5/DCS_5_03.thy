theory DCS_5_03
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_092: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 92) (-8)) (Float (int 92 + 1) (-8))"
  by eval

lemma dc_nc_092: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 92) (-8)) (Float (int 92 + 1) (-8))"
  by eval

lemma dc_c30_093: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 93) (-8)) (Float (int 93 + 1) (-8))"
  by eval

lemma dc_nc_093: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 93) (-8)) (Float (int 93 + 1) (-8))"
  by eval

lemma dc_c30_094: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 94) (-8)) (Float (int 94 + 1) (-8))"
  by eval

lemma dc_nc_094: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 94) (-8)) (Float (int 94 + 1) (-8))"
  by eval

lemma dc_c30_095: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 95) (-8)) (Float (int 95 + 1) (-8))"
  by eval

lemma dc_nc_095: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 95) (-8)) (Float (int 95 + 1) (-8))"
  by eval

end
