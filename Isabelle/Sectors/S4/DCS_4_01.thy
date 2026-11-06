theory DCS_4_01
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_068: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 68) (-8)) (Float (int 68 + 1) (-8))"
  by eval

lemma dc_nc_068: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 68) (-8)) (Float (int 68 + 1) (-8))"
  by eval

lemma dc_c30_069: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 69) (-8)) (Float (int 69 + 1) (-8))"
  by eval

lemma dc_nc_069: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 69) (-8)) (Float (int 69 + 1) (-8))"
  by eval

lemma dc_c30_070: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 70) (-8)) (Float (int 70 + 1) (-8))"
  by eval

lemma dc_nc_070: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 70) (-8)) (Float (int 70 + 1) (-8))"
  by eval

lemma dc_c30_071: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 71) (-8)) (Float (int 71 + 1) (-8))"
  by eval

lemma dc_nc_071: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 71) (-8)) (Float (int 71 + 1) (-8))"
  by eval

end
