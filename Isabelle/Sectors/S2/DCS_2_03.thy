theory DCS_2_03
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_044: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 44) (-8)) (Float (int 44 + 1) (-8))"
  by eval

lemma dc_nc_044: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 44) (-8)) (Float (int 44 + 1) (-8))"
  by eval

lemma dc_c30_045: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 45) (-8)) (Float (int 45 + 1) (-8))"
  by eval

lemma dc_nc_045: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 45) (-8)) (Float (int 45 + 1) (-8))"
  by eval

lemma dc_c30_046: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 46) (-8)) (Float (int 46 + 1) (-8))"
  by eval

lemma dc_nc_046: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 46) (-8)) (Float (int 46 + 1) (-8))"
  by eval

lemma dc_c30_047: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 47) (-8)) (Float (int 47 + 1) (-8))"
  by eval

lemma dc_nc_047: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 47) (-8)) (Float (int 47 + 1) (-8))"
  by eval

end
