theory DCS_10_01
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_164: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 164) (-8)) (Float (int 164 + 1) (-8))"
  by eval

lemma dc_nc_164: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 164) (-8)) (Float (int 164 + 1) (-8))"
  by eval

lemma dc_c30_165: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 165) (-8)) (Float (int 165 + 1) (-8))"
  by eval

lemma dc_nc_165: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 165) (-8)) (Float (int 165 + 1) (-8))"
  by eval

lemma dc_c30_166: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 166) (-8)) (Float (int 166 + 1) (-8))"
  by eval

lemma dc_nc_166: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 166) (-8)) (Float (int 166 + 1) (-8))"
  by eval

lemma dc_c30_167: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 167) (-8)) (Float (int 167 + 1) (-8))"
  by eval

lemma dc_nc_167: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 167) (-8)) (Float (int 167 + 1) (-8))"
  by eval

end
