theory Testing
  imports Complex_Main

begin

definition nondecreasing_on :: "real set \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> bool"
  where "nondecreasing_on S f \<longleftrightarrow> (\<forall>x\<in>S. \<forall>y\<in>S. x \<le> y \<longrightarrow> f x \<le> f y)"

(* definition id :: "'a \<Rightarrow> 'a" where "id = (\<lambda>x. x)" *)

lemma id_nondecreasing: "nondecreasing_on {1,2,3} id"
proof-
{ assume "x \<in> {1,2,3}"
  then have "id x = x" by auto
  

lemma sum_square: "(a + b)^2 = a^2 + (2::real)*a*b + b^2"
  apply (simp add:power2_eq_square)
  apply (simp add:algebra_simps)
done

lemma nonneg_quadratic: "x^2 + (6::real)*x + 9 \<ge> 0"
proof-
  have aux: "x^2 + (6::real)*x + 9 = (x + 3)^2"
    using sum_square [of x 3] by auto
  have "(x + 3)^2 \<ge> 0"
    using zero_le_square [of "x+3"] by auto
   from this show ?thesis using aux by auto
qed


end