theory Testing
  imports "HOL-Analysis.Multivariate_Analysis"

begin

lemma interior_ball: "(x \<in> interior S) \<longleftrightarrow> (\<exists> e. 0 < e & (ball x e) \<subseteq> S)"
proof-
  { assume "x \<in> interior S"
    from this obtain T where T_def: "open T & x \<in> T & T \<subseteq> S" using interior_def by auto
    hence "\<exists> e. 0 < e & (ball x e) \<subseteq> T" using open_contains_ball by auto
    hence "\<exists> e. 0 < e & (ball x e) \<subseteq> S" using T_def by auto
  } note imp1 = this
  { assume "(\<exists> e. 0 < e & (ball x e) \<subseteq> S)"
    from this obtain e where e_def: "0 < e & (ball x e) \<subseteq> S" by auto
    obtain T where T_def: "T = ball x e" by auto
    then have "open T & x \<in> T & T \<subseteq> S" using open_ball e_def by auto
    hence "x \<in> interior S" using interior_def by auto
  } from this show ?thesis using imp1 by auto
qed
end