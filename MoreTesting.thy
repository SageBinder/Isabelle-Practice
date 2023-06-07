theory MoreTesting
  imports Main

begin
  lemma functional_increasing:
    fixes f :: "nat \<Rightarrow> nat"
    assumes asm: "\<forall>n. f(f n) < f(n + 1)"
    shows "n \<le> m \<Longrightarrow> f n \<le> f m"
  sorry

  lemma functional_leq:
    fixes f :: "nat \<Rightarrow> nat"
    assumes asm: "\<forall>n. f(f n) < f(n + 1)"
    shows "n \<le> f n"
  proof(induct "n")
    case 0
    show ?case by auto
  next
    case (Suc n)
    fix n
    show "n \<le> f n \<Longrightarrow> Suc n \<le> f (Suc n)"
    proof-
      assume IH: "n \<le> f n"
      hence "f n \<le> f(f n)" using functional_increasing [of "f" "n" "f n"] asm by auto
      hence ineq1: "n \<le> f(f n)" using IH by auto
      have ineq2: "f(f n) < f(n + 1)" using asm by auto
      hence "n < f(n + 1)" using ineq1 ineq2 by auto
      thus "Suc n \<le> f(Suc n)" by auto
    qed
  qed
end
