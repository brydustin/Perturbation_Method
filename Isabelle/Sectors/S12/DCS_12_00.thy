theory DCS_12_00
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_192: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 192) (-8)) (Float (int 192 + 1) (-8))"
  by eval

lemma dc_nc_192: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 192) (-8)) (Float (int 192 + 1) (-8))"
  by eval

lemma dc_c30_193: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 193) (-8)) (Float (int 193 + 1) (-8))"
  by eval

lemma dc_nc_193: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 193) (-8)) (Float (int 193 + 1) (-8))"
  by eval

lemma dc_c30_194: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 194) (-8)) (Float (int 194 + 1) (-8))"
  by eval

lemma dc_nc_194: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 194) (-8)) (Float (int 194 + 1) (-8))"
  by eval

lemma dc_c30_195: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 195) (-8)) (Float (int 195 + 1) (-8))"
  by eval

lemma dc_nc_195: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 195) (-8)) (Float (int 195 + 1) (-8))"
  by eval

end
