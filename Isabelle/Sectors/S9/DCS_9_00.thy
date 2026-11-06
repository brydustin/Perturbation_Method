theory DCS_9_00
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_144: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 144) (-8)) (Float (int 144 + 1) (-8))"
  by eval

lemma dc_nc_144: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 144) (-8)) (Float (int 144 + 1) (-8))"
  by eval

lemma dc_c30_145: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 145) (-8)) (Float (int 145 + 1) (-8))"
  by eval

lemma dc_nc_145: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 145) (-8)) (Float (int 145 + 1) (-8))"
  by eval

lemma dc_c30_146: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 146) (-8)) (Float (int 146 + 1) (-8))"
  by eval

lemma dc_nc_146: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 146) (-8)) (Float (int 146 + 1) (-8))"
  by eval

lemma dc_c30_147: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 147) (-8)) (Float (int 147 + 1) (-8))"
  by eval

lemma dc_nc_147: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 147) (-8)) (Float (int 147 + 1) (-8))"
  by eval

end
