theory PigeonholeWorking
  imports Complex_Main HOL.Finite_Set

begin

lemma distinct2:
  fixes A :: "'a set"
  assumes assms:
          "finite A"
          "card A \<ge> 2"
  obtains x y where "x \<in> A \<and> y \<in> A \<and> x \<noteq> y"
proof-
  obtain x A' where "x \<in> A \<and> x \<notin> A' \<and> card A' = card A - 1 \<and> A' \<subseteq> A"
      using assms(2) card_eq_SucD [of "A" "card A - 1"] by auto
  hence x: "x \<in> A" "x \<notin> A'" "card A' = card A - 1" "A' \<subseteq> A" by auto
  hence A'_card: "card A' = card A - 1" by auto
  also have "... \<ge> 1" using assms(2) by auto
  finally have "card A' \<ge> 1" by auto
  then obtain y where y: "y \<in> A'" using card_eq_SucD [of "A'" "card A' - 1"] by auto
  from that show ?thesis using x y by auto
qed

theorem pigeonhole:
  fixes f :: "'a \<Rightarrow> 'b"
  shows "\<And>A B. \<forall>a \<in> A. \<exists>b \<in> B. f a = b
         \<Longrightarrow> m = card B - 1
         \<Longrightarrow> finite A
         \<Longrightarrow> finite B
         \<Longrightarrow> card B < card A
         \<Longrightarrow> card B > 0
         \<Longrightarrow> (\<exists>x y. x \<noteq> y \<and> f x = f y)"
proof(induction m rule: nat.induct)
  case zero
  then have B_card: "card B = 1" using zero.prems by auto
  then have A_card: "card A \<ge> 2" using zero.prems by auto

  obtain b where "B = {b}" using B_card card_1_singletonE by auto
  then have "\<forall>x \<in> A. f x = b" using zero.prems by auto
  moreover obtain x y where "x \<in> A \<and> y \<in> A \<and> x \<noteq> y" using A_card zero.prems distinct2[of "A"] by auto
  moreover have "f x = b" using calculation by auto
  moreover have "f y = b" using calculation by auto
  ultimately have "x \<noteq> y \<and> f x = f y" by auto
  hence "\<exists>y. x \<noteq> y \<and> f x = f y" by (rule exI)
  thus ?case by (rule exI)
next
  case (Suc m)
  have "card A > 0" using Suc.prems by auto
  from this obtain a where a: "a \<in> A" using card_eq_SucD[of "A" "card A - 1"] by auto
  then have fa_in_B: "f a \<in> B" using Suc.prems by auto
  show ?case
  proof(cases "\<exists>y. a \<noteq> y \<and> f a = f y")
    case True
    thus ?thesis by (rule exI)
  next
    case False
    then have fa_unique: "\<forall>y. a \<noteq> y \<longrightarrow> f a \<noteq> f y" by auto

    define A' where "A' = A - {a}"
    define B' where "B' = B - {f a}"
    have A'_card: "card A' = card A - 1" using a A'_def card_Diff_singleton[of "a" "A'"] by auto
    have B'_card: "card B' = card B - 1" using fa_in_B B'_def card_Diff_singleton[of "f a" "B'"] by auto

    have "A' \<subseteq> A" using A'_def by auto
    moreover from this have "\<forall>x \<in> A'. f x \<in> B" using Suc.prems by auto
    moreover have "\<forall>x \<in> A'. f x \<noteq> f a" using fa_unique A'_def by auto
    moreover from this have "\<forall>x \<in> A'. f x \<notin> {f a}" using A'_def B'_def fa_unique by auto
    ultimately have "\<forall>x \<in> A'. f x \<in> B \<and> f x \<notin> {f a}" by auto
    
    then have "\<forall>x \<in> A'. f x \<in> B'" using B'_def by auto
    then have "\<forall>x \<in> A'. \<exists>b \<in> B'. f x = b" by auto
    moreover have "finite A'" using Suc.prems A'_def by auto
    moreover have "finite B'" using Suc.prems B'_def by auto
    moreover have "card B' > 0" using Suc.prems B'_card by auto
    moreover from this have "card B' < card A'" using Suc.prems by (auto simp: A'_card B'_card)
    moreover have "card B' - 1 = m" using Suc.prems B'_card by auto
    ultimately show ?thesis using Suc.IH[of "A'" "B'"] by auto
  qed
qed

(*Better formatted and stuff*)
theorem pigeonhole2:
  fixes f :: "'a \<Rightarrow> 'b"
  fixes m :: "nat"
  assumes "\<forall>a \<in> A. \<exists>b \<in> B. f a = b"
  assumes "finite A"
  assumes "finite B"
  assumes "card B < card A"
  assumes "card B > 0"
  shows "\<exists>x y. x \<noteq> y \<and> f x = f y"
  using assms
proof(induction "card B - 1" arbitrary: "A" "B" rule: nat.induct)
  case zero
  then have B_card: "card B = 1" using zero.prems by auto
  then have A_card: "card A \<ge> 2" using zero.prems by auto

  obtain b where "B = {b}" using B_card card_1_singletonE by auto
  then have "\<forall>x \<in> A. f x = b" using zero.prems by auto
  moreover obtain x y where "x \<in> A \<and> y \<in> A \<and> x \<noteq> y" using A_card zero.prems distinct2[of "A"] by auto
  moreover have "f x = b" using calculation by auto
  moreover have "f y = b" using calculation by auto
  ultimately have "x \<noteq> y \<and> f x = f y" by auto
  hence "\<exists>y. x \<noteq> y \<and> f x = f y" by (rule exI)
  thus ?case by (rule exI)
next
  case (Suc m)
  have "card A > 0" using Suc.prems by auto
  from this obtain a where a: "a \<in> A" using card_eq_SucD[of "A" "card A - 1"] by auto
  then have fa_in_B: "f a \<in> B" using Suc.prems by auto
  show ?case
  proof(cases "\<exists>y. a \<noteq> y \<and> f a = f y")
    case True
    thus ?thesis by (rule exI)
  next
    case False
    then have fa_unique: "\<forall>y. a \<noteq> y \<longrightarrow> f a \<noteq> f y" by auto

    let ?A' = "A - {a}"
    let ?B' = "B - {f a}"
    have A'_card: "card ?A' = card A - 1" using a card_Diff_singleton[of "a" "?A'"] by auto
    have B'_card: "card ?B' = card B - 1" using fa_in_B card_Diff_singleton[of "f a" "?B'"] by auto

    have "?A' \<subseteq> A" by auto
    moreover from this have "\<forall>x \<in> ?A'. f x \<in> B" using Suc.prems by auto
    moreover have "\<forall>x \<in> ?A'. f x \<noteq> f a" using fa_unique by auto
    moreover from this have "\<forall>x \<in> ?A'. f x \<notin> {f a}" using fa_unique by auto
    ultimately have "\<forall>x \<in> ?A'. f x \<in> B \<and> f x \<notin> {f a}" by auto
    
    then have "\<forall>x \<in> ?A'. f x \<in> ?B'" by auto
    then have "\<forall>x \<in> ?A'. \<exists>b \<in> ?B'. f x = b" by auto
    moreover have "finite ?A'" using Suc.prems by auto
    moreover have "finite ?B'" using Suc.prems by auto
    moreover have "card ?B' > 0" using B'_card Suc.hyps(2) by linarith 
    moreover from this have "card ?B' < card ?A'"
      by (simp add: A'_card B'_card Suc.prems(4) diff_less_mono) 
    moreover have "card ?B' - 1 = m"
      by (metis B'_card Suc.hyps(2) diff_Suc_1) 
    ultimately show ?thesis using Suc.hyps(1)[of "?B'" "?A'"] by auto
  qed
qed


theorem pigeonhole_obtain:
  fixes f :: "'a \<Rightarrow> 'b" and
        A :: "'a set" and
        B :: "'b set"
  assumes "finite A" and
          "finite B" and
          "card A > card B" and
          "\<forall>x \<in> A. f x \<in> B"
  obtains x y where "f x = f y" using pigeonhole by auto

theorem pigeonhole_app:
  fixes f :: "nat \<Rightarrow> nat" and
        A :: "nat set" and
        B :: "nat set"
  assumes "finite A" and
          "finite B" and
          "card A > card B" and
          "\<forall>x \<in> A. f x \<in> B"
  shows "\<exists>x y. f x = f y" using assms pigeonhole by auto
end