(*<*)
(* Author: Kyndylan Nienhuis *)
(* Author: Thomas Bauereiss *)
theory Proof_methods
  imports Hoare_Extras "HOL-Eisbach.Eisbach_Tools"
begin
(*>*)

section \<open>Helper lemmas\<close>

subsection \<open>Split laws\<close>

lemmas case_split =
  Option.option.split
  List.list.split
  Product_Type.prod.split
  bool.split
  result.split
  ex.split

lemma let_split:
  fixes P
  shows "P (let x = y in f x) = (\<forall>x. x = y \<longrightarrow> P (f x))"
  by simp

lemmas all_split = 
  if_splits(1)
  let_split
  case_split

subsection \<open>Congruences\<close>

lemmas default_weak_cong = 
  if_weak_cong
  let_weak_cong
  option.case_cong_weak
  list.case_cong_weak
  prod.case_cong_weak
  sum.case_cong_weak
  result.case_cong_weak
  ex.case_cong_weak

lemmas default_cong =
  if_cong
  let_cong
  all_cong
  ball_cong
  imp_cong
  (*conj_cong
  disj_cong*)
  option.case_cong
  list.case_cong
  prod.case_cong
  sum.case_cong
  result.case_cong
  ex.case_cong
  bindS_cong
  iff_allI

subsection \<open>Strong congruence simplifier\<close>

method strong_cong_simp uses add del cong =
  (simp
     add: add
     del: del
     split del: if_splits(1)
     cong del: default_weak_cong
     cong add: default_cong cong)

method strong_cong_simp_all uses add del = 
  (simp_all
     add: add
     del: del
     split del: if_splits(1)
     cong del: default_weak_cong
     cong add: default_cong)

method strong_cong_simp_only uses simp = 
  (simp 
     only: simp
     cong add: default_cong)

lemmas prod_if_distribs[simp] = if_distrib[where f = snd] if_distrib[where f = fst]
lemmas app_if_distrib = if_distrib[where f = "\<lambda>i. i x" for x]

lemma liftState_let_distrib[liftState_simp]: "liftState r (let x = y in m x) = (let x = y in liftState r (m x))"
  by simp

lemmas liftState_prod_distrib[liftState_simp] = prod.case_distrib[where h = "liftState r" for r]

method liftS uses add = (strong_cong_simp_only simp: add liftState_simp comp_def)

subsection \<open>Proving Hoare triples\<close>

text \<open>Tactics that iteratively apply Hoare proof rules and simplify goals, using both the proof
rules in the default collection and any additional rules provided as a parameter.\<close>

method repeat_all_new methods m =
  (m; repeat_all_new \<open>m\<close>)?

lemma PrePostE_if_branch_simp:
  assumes f: "b \<Longrightarrow> PrePostE Pf f Q E" and g: "\<not>b \<Longrightarrow> PrePostE Pg g Q E"
    and P: "\<And>s. P s = (if b then Pf s else Pg s)"
  shows "PrePostE P (if b then f else g) Q E"
  using f g unfolding P by auto

lemmas PrePost_casesI = 
  all_split[where P="\<lambda>x. PrePost p x q", THEN iffD2] for p q

lemmas PrePostE_casesI = 
  all_split[where P="\<lambda>x. PrePostE p x q e", THEN iffD2] for p q e

method PrePost_cases =
  rule PrePost_casesI PrePostE_casesI;
  (intro conjI impI allI)?;
  PrePost_cases?

method ComputePreAuto uses simp intro cong =
  auto simp: simp
       intro: intro
       cong del: default_weak_cong cong: default_cong cong
       split: option.splits

lemmas PrePost_weakest_pre_cases_arity_1 =
  PrePost_let PrePostE_let
  PrePost_prod_cases PrePostE_prod_cases_split PrePostE_prod_cases

lemmas PrePost_weakest_pre_cases_arity_1_simp =
  PrePost_if_then PrePostE_if_then
  PrePost_if_else PrePostE_if_else
  PrePostE_let_simp

lemmas PrePost_weakest_pre_cases_arity_2 =
  PrePost_bindS_unit PrePostE_bindS_unit
  PrePost_bindS_ignore PrePostE_bindS_ignore
  PrePost_if_branch PrePostE_if_branch
  PrePost_option_cases PrePostE_option_cases
  PrePost_and_boolS PrePostE_and_boolS
  PrePost_or_boolS PrePostE_or_boolS

lemmas PrePost_weakest_pre_cases_arity_2_simp =
  PrePostE_if_branch_simp

lemmas PrePost_weakest_pre_cases =
  PrePost_weakest_pre_cases_arity_1
  PrePost_weakest_pre_cases_arity_2
  PrePostE_bindS_any_simp PrePost_bindS

method ComputePre methods composite atom_simp final uses atomI =
  (composite,
     ComputePre composite atom_simp final atomI: atomI) |
  (rule PrePost_weakest_pre_cases_arity_1_simp,
     solves \<open>atom_simp\<close>,
     ComputePre composite atom_simp final atomI: atomI) |
  (rule PrePost_weakest_pre_cases_arity_2_simp PrePost_weakest_pre_cases
        PrePost_compositeI PrePostE_compositeI,
     ComputePre composite atom_simp final atomI: atomI) |
  (rule atomI PrePost_atomI PrePostE_atomI,
     ComputePre composite atom_simp final atomI: atomI) |
  (solves \<open>atom_simp\<close>, (ComputePre composite atom_simp final atomI: atomI)?) |
  final

text \<open>The following method corresponds to @\<open>method ComputePre\<close> without any recursive calls. The
purpose is to step through the method when debugging.\<close>

method ComputePre_debug_step methods composite atom_simp uses atomI constI bindI intro =
  (rule constI[THEN PrePostE_bindS_left_const] TrueI) |
  (composite) |
  (rule bindI TrueI) |
  (rule PrePost_weakest_pre_cases_arity_1_simp,
     solves \<open>atom_simp\<close>) |
  (rule PrePost_weakest_pre_cases_arity_2_simp PrePost_weakest_pre_cases) |
  (rule PrePost_compositeI PrePostE_compositeI) |
  (rule atomI TrueI) |
  (rule PrePost_atomI PrePostE_atomI) |
  solves \<open>atom_simp\<close>

method ParametricPrePost methods composite atom_simp final uses atomI simp =
  (*PrePost_cases?;*)
  (liftS add: simp)?,
  rule PrePost_strengthen_pre PrePostE_strengthen_pre,
  ComputePre composite atom_simp final atomI: atomI (*,
  (strong_cong_simp add: simp)?*)

method PrePost uses compositeI atomI simp =
  ParametricPrePost \<open>rule compositeI TrueI\<close> \<open>strong_cong_simp add: simp\<close> - atomI: atomI

method PrePostAuto uses compositeI atomI simp intro =
  ParametricPrePost \<open>rule compositeI TrueI\<close> \<open>ComputePreAuto simp: simp intro: intro\<close> \<open>ComputePreAuto simp: simp intro: intro\<close> atomI: atomI

lemma PrePostE_if_pre_then_True:
  assumes "PrePostE (\<lambda>_. True) f Q E"
    and "(*\<not>c \<Longrightarrow>*) PrePostE P g Q E"
  shows "PrePostE P (if c then f else g) Q E"
  by (PrePost atomI: assms)

lemma PrePostE_if_pre_else_True:
  assumes "PrePostE (\<lambda>_. True) g Q E"
    and "(*c \<Longrightarrow>*) PrePostE P f Q E"
  shows "PrePostE P (if c then f else g) Q E"
  by (PrePost atomI: assms)

thm PrePostE_if_then PrePostE_if_else

method ComputePre_if_heuristic =
  (rule PrePostE_if_then, solves \<open>strong_cong_simp\<close>) |
  (rule PrePostE_if_else, solves \<open>strong_cong_simp\<close>) |
  (rule PrePostE_if_pre_then_True, solves \<open>rule PrePostE_strengthen_pre, (rule PrePostE_compositeI PrePostE_atomI)+, strong_cong_simp\<close>) |
  (rule PrePostE_if_pre_else_True, solves \<open>rule PrePostE_strengthen_pre, (rule PrePostE_compositeI PrePostE_atomI)+, strong_cong_simp\<close>) |
  (rule PrePostE_if_branch_simp)

end
