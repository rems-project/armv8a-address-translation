(*<*)
(* Author: Thomas Bauereiss *)
theory Hoare_Extras
  imports
    Sail.Hoare
    "HOL-Eisbach.Eisbach"
begin
(*>*)

text \<open>Various Hoare proof rules that are useful for this model, e.g. for directly splitting
tuples with many elements.\<close>

lemma PrePostE_PrePost:
  assumes "PrePostE P m (\<lambda>r s. Q (Value r) s) (\<lambda>e s. Q (Ex e) s)"
  shows "PrePost P m Q"
  using assms unfolding PrePostE_def by auto

lemma PrePostE_chooseS_any: "\<lbrace>\<lambda>s. \<forall>x. Q x s\<rbrace> (chooseS xs) \<lbrace>Q \<bar> E\<rbrace>"
  by (intro PrePostE_I) (auto simp: chooseS_def)

lemmas PrePostE_readS_const =  PrePostE_readS[where Q = "\<lambda>r s. r = a \<and> Q a s" for Q a]
lemmas PrePostE_readS_pred =  PrePostE_readS[where Q = "\<lambda>r s. C r \<and> Q r s" for Q C]

lemma PrePostE_pre_conj_constI:
  fixes R :: bool
  assumes "R \<Longrightarrow> PrePostE P m Q E"
  shows "PrePostE (\<lambda>s. R \<and> P s) m Q E"
    and "PrePostE (\<lambda>s. P s \<and> R) m Q E"
  using assms by (auto simp: PrePost_defs)

lemma PrePostE_bindS_any:
  assumes f: "\<And>a. PrePostE (R a) (f a) Q E"
    and m: "PrePostE P m R E"
  shows "PrePostE P (bindS m f) Q E"
  using assms by (intro PrePostE_bindS)

lemma PrePostE_bindS_any_simp:
  assumes f: "\<And>a. PrePostE (R a) (f a) Q E"
    and R': "\<And>b s. R' b s = R b s"
    and m: "PrePostE P m R' E"
  shows "PrePostE P (bindS m f) Q E"
  using f m unfolding R' by (intro PrePostE_bindS)

lemma PrePost_bindS_any_simp:
  assumes f: "\<And>a. PrePost (R (Value a)) (f a) Q"
    and R': "\<And>b s. R' b s = R b s"
    and m: "PrePost P m (\<lambda>r. case r of Value a \<Rightarrow> R' (Value a) | Ex e \<Rightarrow> Q (Ex e))"
  shows "PrePost P (bindS m f) Q"
  using f m unfolding R' by (intro PrePost_bindS) auto

lemma PrePostE_returnS_simp:
  assumes "x' = x"
  shows "PrePostE (Q x') (returnS x) Q E"
  using assms by simp

lemma PrePostE_bindS_prod2:
  assumes "\<And>x1 x2. PrePostE (R x1 x2) (f (x1, x2)) Q E"
    and "PrePostE P m (\<lambda>r. case r of (x1, x2) \<Rightarrow> R x1 x2) E"
  shows "PrePostE P (bindS m f) Q E"
  using assms by (intro PrePostE_bindS) auto

lemma PrePostE_bindS_prod3:
  assumes "\<And>x1 x2 x3. PrePostE (R x1 x2 x3) (f (x1, x2, x3)) Q E"
    and "PrePostE P m (\<lambda>r. case r of (x1, x2, x3) \<Rightarrow> R x1 x2 x3) E"
  shows "PrePostE P (bindS m f) Q E"
  using assms by (intro PrePostE_bindS) auto

lemma PrePostE_bindS_prod4:
  assumes "\<And>x1 x2 x3 x4. PrePostE (R x1 x2 x3 x4) (f (x1, x2, x3, x4)) Q E"
    and "PrePostE P m (\<lambda>r. case r of (x1, x2, x3, x4) \<Rightarrow> R x1 x2 x3 x4) E"
  shows "PrePostE P (bindS m f) Q E"
  using assms by (intro PrePostE_bindS) auto

lemma PrePostE_bindS_prod5:
  assumes "\<And>x1 x2 x3 x4 x5. PrePostE (R x1 x2 x3 x4 x5) (f (x1, x2, x3, x4, x5)) Q E"
    and "PrePostE P m (\<lambda>r. case r of (x1, x2, x3, x4, x5) \<Rightarrow> R x1 x2 x3 x4 x5) E"
  shows "PrePostE P (bindS m f) Q E"
  using assms by (intro PrePostE_bindS) auto

lemma PrePostE_bindS_prod6:
  assumes "\<And>x1 x2 x3 x4 x5 x6. PrePostE (R x1 x2 x3 x4 x5 x6) (f (x1, x2, x3, x4, x5, x6)) Q E"
    and "PrePostE P m (\<lambda>r. case r of (x1, x2, x3, x4, x5, x6) \<Rightarrow> R x1 x2 x3 x4 x5 x6) E"
  shows "PrePostE P (bindS m f) Q E"
  using assms by (intro PrePostE_bindS) auto

lemma PrePostE_bindS_prod7:
  assumes "\<And>x1 x2 x3 x4 x5 x6 x7. PrePostE (R x1 x2 x3 x4 x5 x6 x7) (f (x1, x2, x3, x4, x5, x6, x7)) Q E"
    and "PrePostE P m (\<lambda>r. case r of (x1, x2, x3, x4, x5, x6, x7) \<Rightarrow> R x1 x2 x3 x4 x5 x6 x7) E"
  shows "PrePostE P (bindS m f) Q E"
  using assms by (intro PrePostE_bindS) auto

lemma PrePostE_bindS_prod8:
  assumes "\<And>x1 x2 x3 x4 x5 x6 x7 x8. PrePostE (R x1 x2 x3 x4 x5 x6 x7 x8) (f (x1, x2, x3, x4, x5, x6, x7, x8)) Q E"
    and "PrePostE P m (\<lambda>r. case r of (x1, x2, x3, x4, x5, x6, x7, x8) \<Rightarrow> R x1 x2 x3 x4 x5 x6 x7 x8) E"
  shows "PrePostE P (bindS m f) Q E"
  using assms by (intro PrePostE_bindS) auto

lemma PrePostE_bindS_prod9:
  assumes "\<And>x1 x2 x3 x4 x5 x6 x7 x8 x9. PrePostE (R x1 x2 x3 x4 x5 x6 x7 x8 x9) (f (x1, x2, x3, x4, x5, x6, x7, x8, x9)) Q E"
    and "PrePostE P m (\<lambda>r. case r of (x1, x2, x3, x4, x5, x6, x7, x8, x9) \<Rightarrow> R x1 x2 x3 x4 x5 x6 x7 x8 x9) E"
  shows "PrePostE P (bindS m f) Q E"
  using assms by (intro PrePostE_bindS) auto

lemma PrePostE_bindS_prod10:
  assumes "\<And>x1 x2 x3 x4 x5 x6 x7 x8 x9 x10. PrePostE (R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (f (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10)) Q E"
    and "PrePostE P m (\<lambda>r. case r of (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) \<Rightarrow> R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) E"
  shows "PrePostE P (bindS m f) Q E"
  using assms by (intro PrePostE_bindS) auto

lemma PrePostE_bindS_prod11:
  assumes "\<And>x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11. PrePostE (R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (f (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11)) Q E"
    and "PrePostE P m (\<lambda>r. case r of (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11) \<Rightarrow> R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) E"
  shows "PrePostE P (bindS m f) Q E"
  using assms by (intro PrePostE_bindS) auto

lemma PrePostE_bindS_prod12:
  assumes "\<And>x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12. PrePostE (R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) (f (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12)) Q E"
    and "PrePostE P m (\<lambda>r. case r of (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) \<Rightarrow> R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) E"
  shows "PrePostE P (bindS m f) Q E"
  using assms by (intro PrePostE_bindS) auto

lemma PrePostE_bindS_prod13:
  assumes "\<And>x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13. PrePostE (R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) (f (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13)) Q E"
    and "PrePostE P m (\<lambda>r. case r of (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13) \<Rightarrow> R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) E"
  shows "PrePostE P (bindS m f) Q E"
  using assms by (intro PrePostE_bindS) auto

lemma PrePostE_bindS_prod14:
  assumes "\<And>x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14. PrePostE (R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) (f (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14)) Q E"
    and "PrePostE P m (\<lambda>r. case r of (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14) \<Rightarrow> R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) E"
  shows "PrePostE P (bindS m f) Q E"
  using assms by (intro PrePostE_bindS) auto

lemma PrePostE_bindS_prod15:
  assumes "\<And>x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15. PrePostE (R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) (f (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15)) Q E"
    and "PrePostE P m (\<lambda>r. case r of (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15) \<Rightarrow> R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) E"
  shows "PrePostE P (bindS m f) Q E"
  using assms by (intro PrePostE_bindS) auto

lemma PrePostE_bindS_prod16:
  assumes "\<And>x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16. PrePostE (R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) (f (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16)) Q E"
    and "PrePostE P m (\<lambda>r. case r of (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16) \<Rightarrow> R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) E"
  shows "PrePostE P (bindS m f) Q E"
  using assms by (intro PrePostE_bindS) auto

lemma PrePostE_bindS_prod17:
  assumes "\<And>x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17. PrePostE (R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17) (f (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17)) Q E"
    and "PrePostE P m (\<lambda>r. case r of (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17) \<Rightarrow> R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17) E"
  shows "PrePostE P (bindS m f) Q E"
  using assms by (intro PrePostE_bindS) auto

lemma PrePostE_bindS_prod18:
  assumes "\<And>x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18. PrePostE (R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18) (f (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18)) Q E"
    and "PrePostE P m (\<lambda>r. case r of (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18) \<Rightarrow> R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18) E"
  shows "PrePostE P (bindS m f) Q E"
  using assms by (intro PrePostE_bindS) auto

lemma PrePostE_bindS_prod19:
  assumes "\<And>x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19. PrePostE (R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19) (f (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19)) Q E"
    and "PrePostE P m (\<lambda>r. case r of (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19) \<Rightarrow> R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19) E"
  shows "PrePostE P (bindS m f) Q E"
  using assms by (intro PrePostE_bindS) auto

lemma PrePostE_bindS_prod20:
  assumes "\<And>x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20. PrePostE (R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20) (f (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20)) Q E"
    and "PrePostE P m (\<lambda>r. case r of (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20) \<Rightarrow> R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20) E"
  shows "PrePostE P (bindS m f) Q E"
  using assms by (intro PrePostE_bindS) auto

lemmas PrePostE_bindS_prods = PrePostE_bindS_prod20 PrePostE_bindS_prod19 PrePostE_bindS_prod18
  PrePostE_bindS_prod17 PrePostE_bindS_prod16 PrePostE_bindS_prod15 PrePostE_bindS_prod14
  PrePostE_bindS_prod13 PrePostE_bindS_prod12 PrePostE_bindS_prod11 PrePostE_bindS_prod10
  PrePostE_bindS_prod9 PrePostE_bindS_prod8 PrePostE_bindS_prod7 PrePostE_bindS_prod6
  PrePostE_bindS_prod5 PrePostE_bindS_prod4 PrePostE_bindS_prod3 PrePostE_bindS_prod2

lemma PrePostE_prod_cases2:
  assumes "PrePostE P (f x1 x2) Q E"
  shows "PrePostE P (case (x1, x2) of (x1, x2) \<Rightarrow> f x1 x2) Q E"
  using assms by (auto split: prod.splits)

lemma PrePostE_prod_cases3:
  assumes "PrePostE P (f x1 x2 x3) Q E"
  shows "PrePostE P (case (x1, x2, x3) of (x1, x2, x3) \<Rightarrow> f x1 x2 x3) Q E"
  using assms by (auto split: prod.splits)

lemma PrePostE_prod_cases4:
  assumes "PrePostE P (f x1 x2 x3 x4) Q E"
  shows "PrePostE P (case (x1, x2, x3, x4) of (x1, x2, x3, x4) \<Rightarrow> f x1 x2 x3 x4) Q E"
  using assms by (auto split: prod.splits)

lemma PrePostE_prod_cases5:
  assumes "PrePostE P (f x1 x2 x3 x4 x5) Q E"
  shows "PrePostE P (case (x1, x2, x3, x4, x5) of (x1, x2, x3, x4, x5) \<Rightarrow> f x1 x2 x3 x4 x5) Q E"
  using assms by (auto split: prod.splits)

lemma PrePostE_prod_cases6:
  assumes "PrePostE P (f x1 x2 x3 x4 x5 x6) Q E"
  shows "PrePostE P (case (x1, x2, x3, x4, x5, x6) of (x1, x2, x3, x4, x5, x6) \<Rightarrow> f x1 x2 x3 x4 x5 x6) Q E"
  using assms by (auto split: prod.splits)

lemma PrePostE_prod_cases7:
  assumes "PrePostE P (f x1 x2 x3 x4 x5 x6 x7) Q E"
  shows "PrePostE P (case (x1, x2, x3, x4, x5, x6, x7) of (x1, x2, x3, x4, x5, x6, x7) \<Rightarrow> f x1 x2 x3 x4 x5 x6 x7) Q E"
  using assms by (auto split: prod.splits)

lemma PrePostE_prod_cases8:
  assumes "PrePostE P (f x1 x2 x3 x4 x5 x6 x7 x8) Q E"
  shows "PrePostE P (case (x1, x2, x3, x4, x5, x6, x7, x8) of (x1, x2, x3, x4, x5, x6, x7, x8) \<Rightarrow> f x1 x2 x3 x4 x5 x6 x7 x8) Q E"
  using assms by (auto split: prod.splits)

lemma PrePostE_prod_cases9:
  assumes "PrePostE P (f x1 x2 x3 x4 x5 x6 x7 x8 x9) Q E"
  shows "PrePostE P (case (x1, x2, x3, x4, x5, x6, x7, x8, x9) of (x1, x2, x3, x4, x5, x6, x7, x8, x9) \<Rightarrow> f x1 x2 x3 x4 x5 x6 x7 x8 x9) Q E"
  using assms by (auto split: prod.splits)

lemma PrePostE_prod_cases10:
  assumes "PrePostE P (f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) Q E"
  shows "PrePostE P (case (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) of (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) \<Rightarrow> f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) Q E"
  using assms by (auto split: prod.splits)

lemma PrePostE_prod_cases11:
  assumes "PrePostE P (f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) Q E"
  shows "PrePostE P (case (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11) of (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11) \<Rightarrow> f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) Q E"
  using assms by (auto split: prod.splits)

lemma PrePostE_prod_cases12:
  assumes "PrePostE P (f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) Q E"
  shows "PrePostE P (case (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) of (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) \<Rightarrow> f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) Q E"
  using assms by (auto split: prod.splits)

lemma PrePostE_prod_cases13:
  assumes "PrePostE P (f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) Q E"
  shows "PrePostE P (case (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13) of (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13) \<Rightarrow> f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) Q E"
  using assms by (auto split: prod.splits)

lemma PrePostE_prod_cases14:
  assumes "PrePostE P (f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) Q E"
  shows "PrePostE P (case (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14) of (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14) \<Rightarrow> f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) Q E"
  using assms by (auto split: prod.splits)

lemma PrePostE_prod_cases15:
  assumes "PrePostE P (f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) Q E"
  shows "PrePostE P (case (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15) of (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15) \<Rightarrow> f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) Q E"
  using assms by (auto split: prod.splits)

lemma PrePostE_prod_cases16:
  assumes "PrePostE P (f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) Q E"
  shows "PrePostE P (case (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16) of (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16) \<Rightarrow> f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) Q E"
  using assms by (auto split: prod.splits)

lemma PrePostE_prod_cases17:
  assumes "PrePostE P (f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17) Q E"
  shows "PrePostE P (case (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17) of (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17) \<Rightarrow> f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17) Q E"
  using assms by (auto split: prod.splits)

lemma PrePostE_prod_cases18:
  assumes "PrePostE P (f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18) Q E"
  shows "PrePostE P (case (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18) of (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18) \<Rightarrow> f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18) Q E"
  using assms by (auto split: prod.splits)

lemma PrePostE_prod_cases19:
  assumes "PrePostE P (f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19) Q E"
  shows "PrePostE P (case (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19) of (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19) \<Rightarrow> f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19) Q E"
  using assms by (auto split: prod.splits)

lemma PrePostE_prod_cases20:
  assumes "PrePostE P (f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20) Q E"
  shows "PrePostE P (case (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20) of (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20) \<Rightarrow> f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20) Q E"
  using assms by (auto split: prod.splits)

lemmas PrePostE_prod_cases_split = PrePostE_prod_cases20 PrePostE_prod_cases19
  PrePostE_prod_cases18 PrePostE_prod_cases17 PrePostE_prod_cases16 PrePostE_prod_cases15
  PrePostE_prod_cases14 PrePostE_prod_cases13 PrePostE_prod_cases12 PrePostE_prod_cases11
  PrePostE_prod_cases10 PrePostE_prod_cases9 PrePostE_prod_cases8 PrePostE_prod_cases7
  PrePostE_prod_cases6 PrePostE_prod_cases5 PrePostE_prod_cases4 PrePostE_prod_cases3
  PrePostE_prod_cases2

lemma PrePostE_bindS_left:
  assumes "\<And>R. PrePostE (P R) m R E"
    and "\<And>s a s'. (Value a, s') \<in> m s \<Longrightarrow> PrePostE (R a) (f a) Q E"
  shows "PrePostE (P R) (bindS m f) Q E"
  using assms by (blast intro: PrePostE_strengthen_pre)

lemma PrePostE_bindS_left_const:
  assumes "PrePostE P m (\<lambda>r s'. r = a \<and> R s') E"
    and "PrePostE R (f a) Q E"
  shows "PrePostE P (bindS m f) Q E"
  using assms unfolding PrePostE_def PrePost_def by (fastforce elim!: bindS_cases)

lemma PrePostE_bindS_left_const_simp:
  assumes "PrePostE P m (\<lambda>r s'. r = a \<and> R s') E"
    and "f' = f a"
    and "PrePostE R f' Q E"
  shows "PrePostE P (bindS m f) Q E"
  using assms unfolding PrePostE_def PrePost_def by (fastforce elim!: bindS_cases)

lemma PrePostE_bindS_left_pred:
  assumes m: "PrePostE P m (\<lambda>a s'. C a \<and> R a s') E"
    and f: "\<And>a. C a \<Longrightarrow> PrePostE (R a) (f a) Q E"
  shows "PrePostE P (bindS m f) Q E"
  unfolding PrePostE_def using assms
  by (intro PrePostI; elim bindS_cases; auto elim: bindS_cases PrePostE_elim)

lemma PrePostE_bindS_left_pred_simp:
  assumes "PrePostE P m (\<lambda>a s'. C a \<and> R a s') E"
    and "\<And>a. C a \<Longrightarrow> f' a = f a"
    and "\<And>a. PrePostE (R a) (f' a) Q E"
  shows "PrePostE P (bindS m f) Q E"
  unfolding PrePostE_def using assms
  by (intro PrePostI; elim bindS_cases; fastforce elim: PrePostE_elim)

lemma PrePostE_bindS_left_inv:
  assumes m: "\<And>a. PrePostE R m (\<lambda>_. R) E"
    and f: "\<And>a. PrePostE R (f a) Q E"
  shows "PrePostE R (bindS m f) Q E"
  unfolding PrePostE_def
proof (intro PrePostI)
  fix s r s'
  assume "(r, s') \<in> bindS m f s" and R: "R s"
  then show "(case r of Value a \<Rightarrow> Q a | result.Ex e \<Rightarrow> E e) s'"
  proof (cases rule: bindS_cases)
    case (Value a a' s'')
    then have "R s''" using R m by (auto elim!: PrePostE_elim)
    then show ?thesis using f Value by (auto elim!: PrePostE_elim)
  next
    case (Ex_Left e)
    then show ?thesis using R m by (auto elim!: PrePostE_elim)
  next
    case (Ex_Right e a s'')
    then have "R s''" using R m by (auto elim!: PrePostE_elim)
    then show ?thesis using f Ex_Right by (auto elim!: PrePostE_elim)
  qed
qed

lemma PrePostE_let_simp:
  assumes "y' = y"
    and "PrePostE P (m y') Q E"
  shows "PrePostE P (let x = y in m x) Q E"
  using assms by auto

lemma PrePostE_if_app[PrePostE_atomI]:
  assumes "PrePostE P (if b then f else g) Q E"
  shows "PrePostE P (\<lambda>s. if b then f s else g s) Q E"
  using assms by (auto split: if_splits)

lemma PrePostE_let_app[PrePostE_atomI]:
  assumes "PrePostE P (let x = y in f x) Q E"
  shows "PrePostE P (\<lambda>s. let x = y in f x s) Q E"
  using assms by auto

end
