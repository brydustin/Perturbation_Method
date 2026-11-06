theory DCS_4_02
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_072: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 72) (-8)) (Float (int 72 + 1) (-8))"
  by eval

lemma dc_nc_072: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 72) (-8)) (Float (int 72 + 1) (-8))"
  by eval

lemma dc_c30_073: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 73) (-8)) (Float (int 73 + 1) (-8))"
  by eval

lemma dc_nc_073: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 73) (-8)) (Float (int 73 + 1) (-8))"
  by eval

lemma dc_c30_074: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 74) (-8)) (Float (int 74 + 1) (-8))"
  by eval

lemma dc_nc_074: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 74) (-8)) (Float (int 74 + 1) (-8))"
  by eval

lemma dc_c30_075: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 75) (-8)) (Float (int 75 + 1) (-8))"
  by eval

lemma dc_nc_075: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 75) (-8)) (Float (int 75 + 1) (-8))"
  by eval

end
