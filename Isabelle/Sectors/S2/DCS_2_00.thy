theory DCS_2_00
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_032: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 32) (-8)) (Float (int 32 + 1) (-8))"
  by eval

lemma dc_nc_032: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 32) (-8)) (Float (int 32 + 1) (-8))"
  by eval

lemma dc_c30_033: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 33) (-8)) (Float (int 33 + 1) (-8))"
  by eval

lemma dc_nc_033: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 33) (-8)) (Float (int 33 + 1) (-8))"
  by eval

lemma dc_c30_034: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 34) (-8)) (Float (int 34 + 1) (-8))"
  by eval

lemma dc_nc_034: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 34) (-8)) (Float (int 34 + 1) (-8))"
  by eval

lemma dc_c30_035: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 35) (-8)) (Float (int 35 + 1) (-8))"
  by eval

lemma dc_nc_035: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 35) (-8)) (Float (int 35 + 1) (-8))"
  by eval

end
