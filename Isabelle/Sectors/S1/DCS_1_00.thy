theory DCS_1_00
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_016: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 16) (-8)) (Float (int 16 + 1) (-8))"
  by eval

lemma dc_nc_016: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 16) (-8)) (Float (int 16 + 1) (-8))"
  by eval

lemma dc_c30_017: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 17) (-8)) (Float (int 17 + 1) (-8))"
  by eval

lemma dc_nc_017: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 17) (-8)) (Float (int 17 + 1) (-8))"
  by eval

lemma dc_c30_018: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 18) (-8)) (Float (int 18 + 1) (-8))"
  by eval

lemma dc_nc_018: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 18) (-8)) (Float (int 18 + 1) (-8))"
  by eval

lemma dc_c30_019: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 19) (-8)) (Float (int 19 + 1) (-8))"
  by eval

lemma dc_nc_019: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 19) (-8)) (Float (int 19 + 1) (-8))"
  by eval

end
