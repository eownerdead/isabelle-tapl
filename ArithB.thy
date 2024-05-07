theory ArithB
  imports Main
begin

datatype tm =
  T
| F
| If tm tm tm

definition is_val[simp]: "is_val s \<longleftrightarrow> s = T \<or> s = F"

inductive step :: "tm \<Rightarrow> tm \<Rightarrow> bool" (infix "\<rightarrow>" 55) where
  IfTrue: "If T t e \<rightarrow> t"
| IfFalse: "If F t e \<rightarrow> e"
| If: "c \<rightarrow> c' \<Longrightarrow> If c t e \<rightarrow> If c' t e"

inductive_cases TE[elim!]: "T \<rightarrow> s"
inductive_cases FE[elim!]: "F \<rightarrow> s"
inductive_cases ZeroE[elim!]: "Zero \<rightarrow> s"

lemma IfTrueE[elim!]:
  assumes "If T t e \<rightarrow> s"
  obtains "s = t"
  using assms TE step.cases by blast

lemma IfFalseE[elim!]:
  assumes "If F t e \<rightarrow> s"
  obtains "s = e"
  using assms FE step.cases by blast

inductive_cases IfE[elim!]: "If c t e \<rightarrow> s"

theorem step_determinacy:
  assumes "s \<rightarrow> s\<^sub>1" "s \<rightarrow> s\<^sub>2"
  shows "s\<^sub>1 = s\<^sub>2"
  using assms
proof (induct s s\<^sub>1 arbitrary: s\<^sub>2 rule: step.induct)
  fix t e t\<^sub>2 assume "If T t e \<rightarrow> t\<^sub>2"
  then show "t = t\<^sub>2" by auto
next
  fix c c' t e t\<^sub>2
  assume IH: "If c t e \<rightarrow> t\<^sub>2" "c \<rightarrow> c'" "\<And>c''. c \<rightarrow> c'' \<Longrightarrow> c' = c''"
  moreover from `c \<rightarrow> c'` have "c \<noteq> T" "c \<noteq> F" by auto
  ultimately show "If c' t e = t\<^sub>2" using IfE by metis
qed auto

definition nf[simp]: "nf s \<equiv> \<nexists>s'. s \<rightarrow> s'"

lemma if_not_nf: "\<not> nf (If c t e)"
  apply (induct c arbitrary: t e)
  using IfTrue apply auto[1]
  using IfFalse apply auto[1]
  using If nf by meson

theorem val_nf: "nf s \<longleftrightarrow> is_val s"
proof
  show "nf s \<Longrightarrow> is_val s"
  apply (rule tm.exhaust[of s])
      apply auto
    using if_not_nf nf by blast
next
  show "is_val s \<Longrightarrow> nf s" by auto
qed

lemma not_val_if:
  assumes "\<not> is_val s"
  obtains c t e where "s = If c t e"
  using assms
  by (cases s) auto

abbreviation steps (infix "\<rightarrow>\<^sup>*" 55) where
  "steps \<equiv> step\<^sup>*\<^sup>*"

lemma steps_If:
  assumes "c \<rightarrow>\<^sup>* c'"
  shows "If c t e \<rightarrow>\<^sup>* If c' t e"
  using assms
proof (induct rule: rtranclp_induct)
  case base
  then show ?case ..
next
  case (step y z)
  have "tm.If y t e \<rightarrow> tm.If z t e" by (simp add: If step.hyps(2))
  then show ?case using step.hyps(3) by auto
qed

lemma nf_exists:
  "\<exists>s'. s \<rightarrow>\<^sup>* s' \<and> nf s'"
proof (induct s)
  case (If c t e)
  then obtain c' where "If c t e \<rightarrow>\<^sup>* If c' t e" "nf c'" using steps_If by blast
  moreover then have "If c' t e \<rightarrow> t \<or> If c' t e \<rightarrow> e" by (metis IfE if_not_nf nf)  
  ultimately show "\<exists>s'. If c t e \<rightarrow>\<^sup>* s' \<and> nf s'" using If.hyps
    by (metis rtranclp.rtrancl_into_rtrancl rtranclp_trans)
qed auto

theorem nf_determinacy:
  assumes "nf s\<^sub>1" "nf s\<^sub>2" "s \<rightarrow>\<^sup>* s\<^sub>1" "s \<rightarrow>\<^sup>* s\<^sub>2"
  shows "s\<^sub>1 = s\<^sub>2"
  oops

end