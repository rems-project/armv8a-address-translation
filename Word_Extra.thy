theory Word_Extra

imports 
  Main
  "HOL-Word.Word"
  "HOL-Lattice.Lattice"
  "HOL-Eisbach.Eisbach_Tools"
begin

(*>*)
section \<open>Library for machine words\<close>

text \<open>We first prove lemmas about integers, then about definitions that create words (such as
@{const mask} and @{const max_word}), then about definitions that manipulate words of the same size
(such as \<open>NOT\<close>, \<open>AND\<close>, \ldots), then about definitions that manipulate words of different sizes
(such as @{const ucast}, @{const slice}) and finally we define a bit-wise order over words.\<close>

subsection \<open>Integers\<close>

text \<open>We start by proving lemmas about integers that can later be lifted to machine words.\<close>

subsubsection \<open>Power of two difference\<close>

lemma mod_power_self:
  fixes x :: "'a::euclidean_semiring_cancel"
  shows "x ^ n mod x = (if n = 0 then 1 mod x else 0)"
by (induct n) simp_all

lemma bin_last_power_of_two_minus_one [simp]:
  shows "bin_last (2 ^ n - 1) = (0 < n)"
unfolding bin_last_def mod_diff_left_eq[where a="2 ^ n", THEN sym] mod_power_self
by simp

lemma bin_last_Suc_power_of_two_minus_one [simp]:
  shows "bin_last (2 * 2 ^ n - 1)"
using bin_last_power_of_two_minus_one[where n="Suc n"]
by simp

lemma bin_rest_power_of_two_minus_one [simp]:
  shows "bin_rest (2 ^ n - 1) = (case n of 0 \<Rightarrow> 0 | Suc m \<Rightarrow> 2 ^ m - 1)"
unfolding bin_rest_def
by (induct n) simp_all

lemma bin_rest_Suc_power_of_two_minus_one [simp]:
  shows "bin_rest (2 * 2 ^ n - 1) =  2 ^ n - 1"
using bin_rest_power_of_two_minus_one[where n="Suc n"]
by simp

lemma int_power_of_two_difference:
  assumes "n \<le> m"
  shows "(2 ^ m - 1) AND NOT (2 ^ n - 1) = (2::int) ^ m - 2 ^ n"
using assms
proof (induct m arbitrary: n)
  case 0
  thus ?case by simp
next
  case (Suc m)
  show ?case
    proof (cases "n = 0")
      case True
      thus ?thesis by simp
    next
      case False
      then obtain n' where [simp]: "n = Suc n'"
        by (metis Suc.prems le_SucE le_zero_eq zero_induct)
      have [simp]: "\<not> 2 * x = 1" for x :: int
        proof
          assume "2 * x = 1"
          from arg_cong[where f=even, OF this]
          show False by simp
        qed
      have "(2::int) ^ Suc m - 2 ^ n = 2 * (2 ^ m - 2 ^ n')"
        by simp
      also have "... = 2 * (2 ^ m - 1 AND NOT (2 ^ n' - 1))"
        using Suc by auto
      also have "... = 2 ^ Suc m - 1 AND NOT (2 ^ n - 1)"
        unfolding bitAND_int.simps[where x="2 ^ Suc m - 1"]
        by (simp add: Bit_B0_2t)
      finally show ?thesis by simp
    qed
qed

subsubsection \<open>Nth bit of products, divisions and remainders\<close>

lemma bin_nth_prod:
  shows "bin_nth (2 ^ n * m) k = (bin_nth m (k - n) \<and> n \<le> k)"
proof (induct n arbitrary: k)
  case 0
  thus ?case 
    by simp
next
  case (Suc n)
  have "bin_nth (2 ^ Suc n * m) k = bin_nth ((2 ^ n * m) BIT False) k"
    by (simp add: Bit_B0_2t mult.assoc)
  also have "... = (bin_nth (2 ^ n * m) (k - 1) \<and> 1 \<le> k)"
    by (induct k) simp_all
  also have "... = (bin_nth m (k - Suc n) \<and> Suc n \<le> k)"
    unfolding Suc[where k="k - 1"]
    by auto    
  finally show ?case .
qed

lemma bin_nth_div:
  shows "bin_nth (m div 2 ^ n) k = bin_nth m (k + n)"
proof (induct n arbitrary: k)
  case 0
  thus ?case 
    by simp
next
  case (Suc n)
  have "bin_nth (m div 2 ^ Suc n) k = bin_nth (m div 2 ^ n div 2) k"
    using zdiv_zmult2_eq
    by (auto simp: mult.commute)
  also have "... = bin_nth (m div 2 ^ n) (Suc k)"
    by (induct k) (simp_all add: bin_rest_def)
  also have "... = bin_nth m (k + Suc n)"
    using Suc[where k="Suc k"]
    by auto    
  finally show ?case .
qed

lemma bin_nth_mod:
  shows "bin_nth (m mod 2 ^ n) k = (bin_nth m k \<and> k < n)"
proof (induct k arbitrary: m n)
  case 0
  thus ?case
    proof (cases "n = 0")
      case True
      thus ?thesis by simp
    next
      case False
      define n' where "n' \<equiv> n - 1"
      hence [simp]: "n = Suc n'"
        using False by auto
      have "(2::int) dvd (2 * 2 ^ n')" by arith
      note [simp] = mod_mod_cancel[OF this]
      show ?thesis
        by (auto simp: bin_last_def)
    qed
next
  case (Suc k)
  thus ?case
    proof (cases "n = 0")
      case True
      thus ?thesis by simp
    next
      case False
      define n' where "n' \<equiv> n - 1"
      hence [simp]: "n = Suc n'"
        using False by auto
      have [simp]: "bin_rest (m mod (2 * 2 ^ n')) = bin_rest m mod (2 ^ n')"
        unfolding bin_rest_def
        using zmod_zmult2_eq
        by simp
      show ?thesis
        using Suc by auto
    qed      
qed

subsection \<open>Words to and from integers\<close>

lemma uint_less [simp]:
  fixes x :: "'a::len0 word"
  shows "uint x \<le> 2 ^ LENGTH('a)"
using uint_lt[where w=x, THEN order.strict_implies_order] .

text \<open>A useful technique to prove equality over words is to compare the words bit by bit.\<close>

lemma test_bit_nat:
  shows "(of_nat n::'a::len word) !! m = (m < LENGTH('a) \<and> bin_nth (int n) m)"
unfolding word_of_nat test_bit_wi ..

subsection \<open>Exhaustive enumeration of small words\<close>

lemma exhaustive_1_word:
  fixes x :: "1 word"
  obtains "x = 0"
        | "x = 1"
proof -
  obtain n where x: "x = of_nat n" and "n < 2"
    by (cases x) auto
  hence "n = 0 \<or> n = 1" by auto
  thus ?thesis using x that by auto
qed

lemma exhaustive_2_word:
  fixes x :: "2 word"
  obtains "x = 0"
        | "x = 1"
        | "x = 2"
        | "x = 3"
proof -
  obtain n where x: "x = of_nat n" and "n < 4"
    by (cases x) auto
  hence "n = 0 \<or> n = 1 \<or> n = 2 \<or> n = 3" by auto
  thus ?thesis using x that by auto
qed

lemma exhaustive_3_word:
  fixes x :: "3 word"
  obtains "x = 0"
        | "x = 1"
        | "x = 2"
        | "x = 3"
        | "x = 4"
        | "x = 5"
        | "x = 6"
        | "x = 7"
proof -
  obtain n where x: "x = of_nat n" and "n < 8"
    by (cases x) auto
  hence "n = 0 \<or> n = 1 \<or> n = 2 \<or> n = 3 \<or> n = 4 \<or> n = 5 \<or> n = 6 \<or> n = 7" 
    by auto
  thus ?thesis using x that by auto
qed

lemma exhaustive_4_word:
  fixes x :: "4 word"
  obtains "x = 0" | "x = 1" | "x = 2" | "x = 3" | "x = 4" | "x = 5" | "x = 6" | "x = 7" | "x = 8"
    | "x = 9" | "x = 10" | "x = 11" | "x = 12" | "x = 13" | "x = 14" | "x = 15"
proof -
  have upt_16: "[0..<16] = [0, Suc 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]"
    by (auto simp: upt_conv_Cons)
  obtain n where x: "x = of_nat n" and "n \<in> set [0..<16]"
    by (cases x) auto
  then have "n = 0 \<or> n = 1 \<or> n = 2 \<or> n = 3 \<or> n = 4 \<or> n = 5 \<or> n = 6 \<or> n = 7 \<or> n = 8 \<or> n = 9 \<or> n = 10 \<or>
             n = 11 \<or> n = 12 \<or> n = 13 \<or> n = 14 \<or> n = 15"
    unfolding upt_16 by auto
  thus ?thesis using x that by auto
qed

lemma word1_eq_1_neq_0:
  fixes w :: "1 word"
  shows "(w = 1) \<longleftrightarrow> \<not>(w = 0)"
  by (cases w rule: exhaustive_1_word) auto

lemma of_bl_eq_1_word[simp]:
  "of_bl [b] = (1 :: 1 word) \<longleftrightarrow> b"
  "of_bl [b] = (0 :: 1 word) \<longleftrightarrow> \<not>b"
  by (cases b) auto

subsection \<open>Masks\<close>

text \<open>We see @{const max_word} as a special case of @{const mask}.\<close>

lemma mask_zero [simp]:
  shows "mask 0 = 0"
unfolding mask_def shiftl_1
by simp

lemma mask_max_word [simp]:
  assumes "LENGTH('a) \<le> n"
  shows "(mask n::'a::len word) = max_word"
using assms
by (intro word_eqI) (simp add: word_size)

lemma max_word_alt_def:
  shows "(max_word::'a::len word) = mask LENGTH('a)"
by simp

lemma mask_plus_one:
  shows "(mask n::'a::len word) + 1 = 2 ^ n"
unfolding mask_def 
by (auto simp: wi_hom_syms)

lemma uint_mask:
  shows "uint (mask n::'a::len word) = 2 ^ (min n LENGTH('a)) - 1"
proof -
  have "uint (mask n::'a word) = uint (word_of_int (2 ^ n - 1)::'a word)"
    unfolding mask_def shiftl_1 word_size wi_hom_syms word_of_int_power_hom[THEN sym]
    by simp
  also have "... = 2 ^ (min n LENGTH('a)) - 1"
    proof (cases "n \<le> LENGTH('a)")
      case True
      hence [simp]: "min n LENGTH('a) = n"
        by auto
      have "(2::int) ^ n \<le> 2 ^ LENGTH('a)"
        using True by auto
      hence "(2::int) ^ n - 1 < 2 ^ LENGTH('a)"
        by arith
      hence [simp]: "((2::int) ^ n - 1) mod 2 ^ LENGTH('a) = 2 ^ n - 1"
        using int_mod_eq' by auto
      show ?thesis 
        unfolding int_word_uint
        by simp 
    next
      case False
      hence [simp]: "min n LENGTH('a) = LENGTH('a)"
        by auto
      define n' where "n' \<equiv> n - LENGTH('a)"
      hence "n = LENGTH('a) + n'"
        using False by auto
      hence [simp]: "(2::int) ^ n = 2 ^ LENGTH('a) * 2 ^ n'"
        using power_add by auto
      have "((2::int) ^ n - 1) mod 2 ^ LENGTH('a) = - 1 mod 2 ^ LENGTH('a)"
        using mod_diff_left_eq[where a="(2::int) ^ n", THEN sym]
        by auto
      also have "... = 2 ^ LENGTH('a) - 1"
        using zmod_minus1 by auto
      finally show ?thesis 
        unfolding int_word_uint
        by simp 
    qed
  finally show ?thesis .
qed

corollary uint_max_word:
  shows "uint (max_word::'a::len word) = 2 ^ LENGTH('a) - 1"
unfolding max_word_alt_def uint_mask
by simp
(* Direct proof: 
unfolding max_word_def uint_word_of_int
using m1mod2k
by auto *)

lemma unat_mask:
  shows "unat (mask n::'a::len word) = 2 ^ (min n LENGTH('a)) - 1"
unfolding unat_def uint_mask
using nat_diff_distrib nat_power_eq
by simp

corollary unat_max_word:
  shows "unat (max_word::'a::len word) = 2 ^ LENGTH('a) - 1"
unfolding max_word_alt_def unat_mask
by simp

lemma min_uint_length:
  fixes x :: "'a::len word"
  shows "min (uint x) (2 ^ LENGTH('a) - 1) = uint x"
proof -
  have "uint x \<le> 2 ^ LENGTH('a) - 1" by simp
  from min_absorb1[OF this]
  show ?thesis .
qed

corollary min_length_uint:
  fixes x :: "'a::len word"
  shows "min (2 ^ LENGTH('a) - 1) (uint x) = uint x"
using min_uint_length[where x=x]
by simp

lemma min_unat_length:
  fixes x :: "'a::len word"
  shows "min (unat x) (2 ^ LENGTH('a) - 1) = unat x"
proof -
  have "unat x \<le> 2 ^ LENGTH('a) - 1"
    using word_le_nat_alt[THEN iffD1, OF max_word_max[where n=x]]
    unfolding unat_max_word
    by simp
  from min_absorb1[OF this]
  show ?thesis .
qed

corollary min_length_unat:
  fixes x :: "'a::len word"
  shows "min (2 ^ LENGTH('a) - 1) (unat x) = unat x"
using min_unat_length[where x=x]
by simp

subsection \<open>@{const max_word}\<close>

text \<open>These lemmas are not a corollary of a corresponding lemma about @{const mask}.\<close>

lemma max_word_le [simp]:
  shows "(max_word \<le> x) = (x = max_word)"
using antisym
by auto

lemma max_word_less [simp]:
  shows "(x < max_word) = (x \<noteq> max_word)"
    and "(max_word < x) = False"
unfolding not_le[THEN sym]
by simp_all

subsection \<open>Negation\<close>

lemma word_not_alt:
  fixes x :: "'a::len word"
  shows "NOT x = max_word - x"
unfolding word_not_def int_not_def
by (simp add: wi_hom_syms max_word_def word_of_int_2p_len)

lemma uminus_alt:
  fixes x :: "'a::len word"
  shows "- x = NOT x + 1"
unfolding word_not_alt max_word_minus
by simp

lemma uint_not:
  fixes x :: "'a::len word"
  shows "uint (NOT x) = uint (max_word::'a::len word) - uint x"
using uint_minus_simple_alt[THEN iffD1, OF max_word_max]
by (auto simp: word_not_alt)

corollary unat_not:
  fixes x :: "'a::len word"
  shows "unat (NOT x) = unat (max_word::'a::len word) - unat x"
unfolding unat_def uint_not 
using nat_diff_distrib' 
by auto

lemma uint_not_mask:
  shows "uint (NOT mask n::'a::len word) = 
         (if LENGTH('a) \<le> n then 0 else 2 ^ LENGTH('a) - 2 ^ n)"
by (auto simp: uint_not uint_max_word uint_mask)

corollary unat_not_mask:
  shows "unat (NOT mask n::'a::len word) = 
         (if LENGTH('a) \<le> n then 0 else 2 ^ LENGTH('a) - 2 ^ n)"
by (auto simp: unat_not unat_max_word unat_mask)

subsection \<open>Conjunction\<close>
        
lemma conj_outside_absorb [simp]:
  fixes x y :: "'a::len word"
  shows "x AND y AND x = x AND y"
by (simp add: word_bool_alg.conj.commute)

subsection \<open>XOR\<close>

lemma word_xor_mask [simp]:
  fixes x :: "'a::len word"
  assumes "LENGTH('a) \<le> n"
  shows "x XOR mask n = NOT x"
using assms
by (intro word_eqI) (auto simp: word_size word_ops_nth_size)

subsection \<open>Lower and upper bits\<close>

(* Perhaps we should create a definition for the lower and upper bits. The only annoying thing
is that I'd like the parameter for the upper bits to specify how many lower bits are cleared, 
while intuitively it specifies how many upper bits are retained.*)

lemma mask_and_mask [simp]:
  shows "mask n AND mask m = mask (min m n)"
by (intro word_eqI) (auto simp: word_size word_ops_nth_size)

lemma not_mask_and_not_mask [simp]:
  shows "NOT mask n AND NOT mask m = NOT mask (max m n)"
by (intro word_eqI) (auto simp: word_size word_ops_nth_size)

lemma mask_and_not_mask [simp]:
  assumes "n \<le> m"
  shows "mask n AND NOT mask m = 0"
using assms
by (intro word_eqI) (auto simp: word_size word_ops_nth_size)

corollary not_mask_and_mask [simp]:
  assumes "m \<le> n"
  shows "NOT mask n AND mask m = 0"
using assms 
unfolding word_bool_alg.conj.commute[where a="NOT _"]
by simp

lemma word_and_mask_and_word_and_not_mask [simp]:
  shows "(x AND mask n) AND (y AND NOT mask n) = 0"
unfolding word_bool_alg.conj.commute[where b="NOT _"]
unfolding word_bool_alg.conj.assoc[where b="mask _"]
   word_bool_alg.conj.assoc[where b="NOT mask _", THEN sym]
by simp

corollary word_and_not_mask_and_word_and_mask [simp]:
  shows "(x AND NOT mask n) AND (y AND mask n) = 0"
unfolding word_bool_alg.conj.commute[where a="_ AND NOT mask _"]
by simp

lemma word_and_not_mask_or_word_and_mask [simp]:
  shows "(x AND NOT mask n) OR (x AND mask n) = x"
by (intro word_eqI)
   (auto simp: word_size word_ops_nth_size)

corollary word_and_mask_or_word_and_not_mask [simp]:
  shows "(x AND mask n) OR (x AND NOT mask n) = x"
using trans[OF word_bool_alg.disj.commute 
               word_and_not_mask_or_word_and_mask] .

lemma word_and_not_mask_plus_word_and_mask [simp]:
  shows "(x AND NOT mask n) + (x AND mask n) = x"
using word_plus_and_or[where x="x AND NOT mask n" and y="x AND mask n"]
by simp

corollary word_and_mask_plus_word_and_not_mask [simp]:
  shows "(x AND mask n) + (x AND NOT mask n) = x"
using trans[OF ab_semigroup_add_class.add.commute
               word_and_not_mask_plus_word_and_mask] .

corollary word_minus_word_and_mask [simp]:
  shows "x - (x AND mask n) = (x AND NOT mask n)"
by (simp add: diff_eq_eq)

corollary word_minus_word_and_not_mask [simp]:
  shows "x - (x AND NOT mask n) = (x AND mask n)"
by (simp add: diff_eq_eq)

corollary word_and_mask_minus_word [simp]:
  shows "(x AND mask n) - x = - (x AND NOT mask n)"
by (simp add: diff_eq_eq)

corollary word_and_not_mask_minus_word [simp]:
  shows "(x AND NOT mask n) - x = - (x AND mask n)"
by (simp add: diff_eq_eq)

lemma uint_word_and_not_mask_plus_uint_word_and_mask [simp]:
  shows "uint (x AND NOT mask n) + uint (x AND mask n) = uint x"
proof -
  have "x AND NOT mask n \<le> (x AND NOT mask n) + (x AND mask n)"
    using word_and_le2
    by auto
  from uint_plus_simple[OF this]
  show ?thesis by simp
qed

corollary uint_word_and_mask_plus_uint_word_and_not_mask [simp]:
  shows "uint (x AND mask n) + uint (x AND NOT mask n) = uint x"
using trans[OF ab_semigroup_add_class.add.commute
               uint_word_and_not_mask_plus_uint_word_and_mask] .

corollary unat_word_and_not_mask_plus_unat_word_and_mask [simp]:
  shows "unat (x AND NOT mask n) + unat (x AND mask n) = unat x"
unfolding unat_def
by (simp add: nat_add_distrib[THEN sym])

corollary unat_word_and_mask_plus_unat_word_and_not_mask [simp]:
  shows "unat (x AND mask n) + unat (x AND NOT mask n) = unat x"
unfolding unat_def
by (simp add: nat_add_distrib[THEN sym])

lemma word_and_mask [simp]:
  fixes x :: "('a :: len) word"
  assumes "len_of TYPE('a) \<le> m"
  shows "(x AND mask m) = x"
proof (intro word_eqI impI, simp only: word_size)
  fix i
  assume len_of_'a: "i < len_of TYPE('a)"
  hence "i < m" using assms by simp
  thus "(x AND mask m) !! i = x !! i"
    using len_of_'a
    by (simp add: nth_ucast word_ao_nth word_size) 
qed

lemma uint_and_mask:
  fixes x :: "'a::len word"
  shows "uint (x AND mask n) = uint x mod 2 ^ (min n LENGTH('a))"
unfolding uint_and uint_mask AND_mod
by simp

lemma unat_and_mask:
  fixes x :: "'a::len word"
  shows "unat (x AND mask n) = unat x mod 2 ^ (min n LENGTH('a))"
unfolding unat_def uint_and_mask
using nat_mod_distrib nat_power_eq
by simp

lemma word_and_not_mask [simp]:
  fixes x :: "('a :: len) word"
  assumes "len_of TYPE('a) \<le> m"
  shows "(x AND NOT mask m) = 0"
using assms
by (intro word_eqI)
   (auto simp: word_size word_ops_nth_size)

lemma uint_and_not_mask:
  fixes x :: "'a::len word"
  shows "uint (x AND NOT mask n) = 
         (if LENGTH('a) \<le> n then 0 else 2 ^ n * (uint x div 2 ^ n))"
proof -
  have "uint (x AND NOT mask n) + uint (x AND mask n) = uint x"
    by simp
  hence "uint (x AND NOT mask n) = uint x - uint (x AND mask n)"
    by arith
  also have "... = uint x - uint x mod 2 ^ min n LENGTH('a)"
    by (simp add: uint_and_mask)
  also have "... = uint x mod 2 ^ min n LENGTH('a) + 
                   2 ^ min n LENGTH('a) * (uint x div 2 ^ min n LENGTH('a)) -
                   uint x mod 2 ^ min n LENGTH('a)"
    using mod_mult_div_eq[where a="uint x" and b="2 ^ min n LENGTH('a)"]
    by auto
  also have "... = 2 ^ min n LENGTH('a) * (uint x div 2 ^ min n LENGTH('a))"
    by arith
  also have "... = (if LENGTH('a) \<le> n then 0 else 2 ^ n * (uint x div 2 ^ n))"
    proof (cases "LENGTH('a) \<le> n")
      case True
      hence [simp]: "min n LENGTH('a) = LENGTH('a)"
        by simp
      have "uint x div 2 ^ LENGTH('a) = 0"
        using div_pos_pos_trivial[OF _ uint_lt[where w=x]]
        by auto
      thus ?thesis
        using True by simp
    qed auto
  finally show ?thesis .
qed

corollary unat_and_not_mask:
  fixes x :: "'a::len word"
  shows "unat (x AND NOT mask n) = 
         (if LENGTH('a) \<le> n then 0 else 2 ^ n * (unat x div 2 ^ n))"
unfolding unat_def uint_and_not_mask
by (simp add: nat_div_distrib nat_mult_distrib nat_power_eq)

lemma uint_and_mask_plus_uint_and_mask_less:
  fixes x y :: "'a::len word"
  assumes "n < LENGTH('a)"
  shows "uint (x AND mask n) + uint (y AND mask n) < 2 ^ (n + 1)"
proof -
  have [simp]: "min n LENGTH('a) = n"
    using assms by auto
  have "0 < (2::'a word) ^ n"
    by (simp add: assms word_2p_lem word_size)
  from uint_2p[OF this]
  have [simp]: "uint ((2::'a word) ^ n) = 2 ^ n" .
  show ?thesis
    using and_mask_less'[OF assms, where w=x]
    using and_mask_less'[OF assms, where w=y]
    unfolding word_less_def
    by simp
qed

corollary uint_and_mask_plus_uint_and_mask_less_size:
  fixes x y :: "'a::len word"
  assumes "n < LENGTH('a)"
  shows "uint (x AND mask n) + uint (y AND mask n) < 2 ^ LENGTH('a)"
proof -
  have "n + 1 \<le> LENGTH('a)"
    using assms by auto
  hence "(2::int) ^ (n + 1) \<le> 2 ^ LENGTH('a)"
    using one_le_numeral power_increasing by blast
  thus ?thesis
    using uint_and_mask_plus_uint_and_mask_less[where x=x and y=y, OF assms]
    by simp
qed

corollary plus_word_and_mask_no_wrap:
  fixes x y :: "'a::len word"
  assumes "n < LENGTH('a)"
  shows "(x AND mask n) \<le> (x AND mask n) + (y AND mask n)"
unfolding no_olen_add
using uint_and_mask_plus_uint_and_mask_less_size[OF assms]
by simp

corollary uint_plus_word_and_mask [simp]:
  fixes x y :: "'a::len word"
  assumes "n < LENGTH('a)"
  shows "uint ((x AND mask n) + (y AND mask n)) =  
         uint (x AND mask n) + uint (y AND mask n)"
using uint_and_mask_plus_uint_and_mask_less_size[OF assms]
unfolding uint_add_lem .

lemma uint_word_and_mask_plus_word_and_not_mask:
  shows "uint ((x AND mask n) + (y AND NOT mask n)) = 
         uint (x AND mask n) + uint (y AND NOT mask n)"
proof (cases "n \<le> LENGTH('a)")
  case True
  hence [simp]: "min n LENGTH('a) = n"
    by simp
  note [simp] = dvd_imp_mod_0[OF le_imp_power_dvd[where a="2::int", OF True]]
  have [simp]: "((2::int) ^ LENGTH('a) - 1) div 2 ^ n = 2 ^ LENGTH('a) div 2 ^ n - 1"
    using div_add1_eq[where a="2 ^ LENGTH('a)" and b="-1::int" and c="2 ^ n"]
    using zdiv_mult_self[where a="-1" and n=1 and m="2 ^ n"]
    using True
    by (auto simp: m1mod2k div_eq_minus1)
  have x: "uint (x AND mask n) < 2 ^ n"
    unfolding uint_and_mask
    by simp
  have "uint y \<le> 2 ^ LENGTH('a) - 1"
    by auto
  from zdiv_mono1[where b="2 ^ n", OF this]
  have "uint (y AND NOT mask n) \<le> 2 ^ n * (2 ^ LENGTH('a) div 2 ^ n - 1)"
    unfolding uint_and_not_mask
    using True
    by auto
  also have "... = 2 ^ LENGTH('a) - 2 ^ n"
    unfolding right_diff_distrib zmde
    by simp
  finally have "uint (x AND mask n) + uint (y AND NOT mask n) < 2 ^ LENGTH('a)"
    using x by auto
  from uint_add_lem[THEN iffD1, OF this]
  show ?thesis .
qed simp

corollary uint_word_and_not_mask_plus_word_and_mask:
  shows "uint ((x AND NOT mask n) + (y AND mask n)) = 
         uint (x AND NOT mask n) + uint (y AND mask n)"
by (simp add: uint_word_and_mask_plus_word_and_not_mask add.commute)

corollary unat_word_and_mask_plus_word_and_not_mask:
  shows "unat ((x AND mask n) + (y AND NOT mask n)) = 
         unat (x AND mask n) + unat (y AND NOT mask n)"
unfolding unat_def uint_word_and_mask_plus_word_and_not_mask
using nat_add_distrib 
by auto

corollary unat_word_and_not_mask_plus_word_and_mask:
  shows "unat ((x AND NOT mask n) + (y AND mask n)) = 
         unat (x AND NOT mask n) + unat (y AND mask n)"
by (simp add: unat_word_and_mask_plus_word_and_not_mask add.commute)

lemma not_mask_eq_plus:
  shows "x + (y AND NOT mask n) AND NOT mask n = (x AND NOT mask n) + (y AND NOT mask n)"
proof -
  have "x + (y AND NOT mask n) AND NOT mask n = x + y - (y AND mask n) AND NOT mask n"
    by (simp add: add_diff_eq[THEN sym])
  also have "... = x + y - (y AND mask n) - ((x + y - (y AND mask n)) AND mask n)"
    by simp
  also have "... = x + y - (y AND mask n) - (x AND mask n)"
    unfolding mask_eqs
    by simp
  also have "... = x - (x AND mask n) + y - (y AND mask n)"
    by simp
  also have "... = (x AND NOT mask n) + (y AND NOT mask n)"
    by simp
  finally show ?thesis .
qed

corollary not_mask_eq_plus_commuted:
  shows "(x AND NOT mask n) + y AND NOT mask n = (x AND NOT mask n) + (y AND NOT mask n)"
using not_mask_eq_plus[where x=y and y=x]
by (simp add: add.commute)

lemma not_mask_eq_minus:
  shows "x - (y AND NOT mask n) AND NOT mask n = (x AND NOT mask n) - (y AND NOT mask n)"
proof -
  have "x - (y AND NOT mask n) AND NOT mask n = x - y + (y AND mask n) AND NOT mask n"
    by (simp add: diff_diff_eq2[THEN sym] diff_add_eq)
  also have "... = x - y + (y AND mask n) - (x - y + (y AND mask n) AND mask n)"
    by simp
  also have "... = x - y + (y AND mask n) - (x AND mask n)"
    unfolding mask_eqs
    by simp
  also have "... = (x AND NOT mask n) - (y AND NOT mask n)"
    by (simp add: diff_diff_eq2[THEN sym] diff_add_eq)
  finally show ?thesis .
qed

lemma word_plus_and_mask:
  fixes x y :: "'a::len word"
  assumes "(x AND mask n) + (y AND mask n) \<le> mask n"
  shows "x + y AND mask n = (x AND mask n) + (y AND mask n)"
proof (cases "n < LENGTH('a)")
  case True
  have [simp]: "min n LENGTH('a) = n"
    using True by auto
  have [simp]: "i mod 2 ^ LENGTH('a) mod 2 ^ n = i mod 2 ^ n" for i :: int
    using True bintrunc_bintrunc_min bintrunc_mod2p 
    by auto
  have *: "uint (x AND mask n) + uint (y AND mask n) < 2 ^ n"
    using assms True
    unfolding word_le_def
    by (simp add: uint_mask)
  have x_and_mask: "uint (x AND mask n) < 2 ^ n"
    by (rule le_less_trans[OF _ *]) auto
  have y_and_mask: "uint (y AND mask n) < 2 ^ n"
    by (rule le_less_trans[OF _ *]) auto
  have "x + y AND mask n = ((x AND mask n) + (y AND mask n)) AND mask n"
    unfolding mask_eqs ..
  also have "... = (x AND mask n) + (y AND mask n)"
    unfolding word_uint_eq_iff 
    using mod_add_if_z[OF x_and_mask y_and_mask] * True
    by (simp add: uint_and_mask)
  finally show ?thesis .
qed simp

corollary word_plus_and_not_mask:
  fixes x y :: "'a::len word"
  assumes "(x AND mask n) + (y AND mask n) \<le> mask n"
  shows "x + y AND NOT mask n = (x AND NOT mask n) + (y AND NOT mask n)"
proof -
  have "x + y AND NOT mask n = (x + y) - (x + y AND mask n)"
    by simp
  also have "... = (x + y) - ((x AND mask n) + (y AND mask n))"
    unfolding word_plus_and_mask[OF assms] ..
  also have "... = (x -  (x AND mask n)) + (y - (y AND mask n))"
    using add_diff_eq diff_add_eq diff_diff_add
    by (metis (no_types, hide_lams))
  also have "... = (x AND NOT mask n) + (y AND NOT mask n)"
    by simp
  finally show ?thesis .
qed

lemma mask_minus_word_and_mask [simp]:
  fixes x :: "'a::len word"
  shows "mask n - (x AND mask n) = NOT x AND mask n"
proof -
  have "mask n - (x AND mask n) = (mask n - (x AND mask n)) AND mask n"
    proof (cases "n < LENGTH('a)")
      case True
      have "mask n - (x AND mask n) < 2 ^ n"
        using word_sub_le[OF word_and_le1[where y=x and a="mask n"]]
        using and_mask_less'[where w=max_word, OF True]
        by simp
      from less_mask_eq[OF this]
      show ?thesis by simp
    qed simp
  also have "... = NOT x AND mask n"
    unfolding word_not_alt
    using mask_eqs(8)[where a="max_word" and b=x and n=n]
    by simp
  finally show ?thesis .
qed

lemma word_power_of_two_difference:
  assumes "n \<le> m"
      and "n \<le> LENGTH('a)"
  shows "(2::'a::len word) ^ m - 2 ^ n = mask m AND NOT mask n"
proof (cases "m \<le> LENGTH('a)")
  case True
  have "(2::'a::len word) ^ m - 2 ^ n = word_of_int (2 ^ m - 2 ^ n)"
    unfolding word_sub_wi word_of_int_2p[THEN sym] int_word_uint
    using mod_power_lem assms True
    by (auto simp: word_of_int_minus)
  also have "... = word_of_int ((2 ^ m - 1) AND NOT (2 ^ n - 1))"
    using assms int_power_of_two_difference
    by simp
  also have "... = word_of_int (2 ^ m - 1) AND NOT word_of_int (2 ^ n - 1)"
    unfolding word_and_def word_not_def wils1
    by simp
  also have "... = mask m AND NOT mask n"
    unfolding mask_def shiftl_1 word_sub_wi word_of_int_2p[THEN sym] int_word_uint 
    using mod_power_lem assms True
    by (auto simp: word_of_int_minus)
  finally show ?thesis by simp
next
  case False
  then obtain m' where m_def: "m = LENGTH('a) + m'"
    unfolding not_le using less_imp_add_positive by auto
  have [simp]: "(2::'a::len word) ^ m = 0"
    unfolding word_of_int_2p[THEN sym] m_def power_add word_of_int_2p_len
    by simp
  have "NOT (mask n::'a word) = - (2 ^ n)"
    unfolding mask_def shiftl_1 word_sub_wi bwsimps int_not_def 
    by (auto simp: wi_hom_syms)
  thus ?thesis 
    unfolding mask_def shiftl_1
    by simp
qed

lemma word_and_mask_xor_mask [simp]:
  shows "x AND mask n XOR mask n = (NOT x) AND mask n"
by (intro word_eqI) (auto simp: word_size word_ops_nth_size)

lemma word_and_mask_and_mask [simp]:
  shows "(x AND mask n) AND mask m = x AND mask (min n m)"
by (intro word_eqI) (auto simp: word_size word_ops_nth_size)

lemma and_shiftl_not_mask [simp]:
  assumes "m \<le> n"
  shows "(x << n) AND NOT mask m = x << n"
using assms
by (intro word_eqI)
   (auto simp: word_size word_ops_nth_size nth_shiftl)

lemma word_and_mask_shiftl_eq_shiftl[simp]:
  assumes "i + j \<ge> LENGTH('a)"
  shows "x AND (mask i :: 'a::len word) << j = x << j"
  using assms by (intro word_eqI) (auto simp: nth_shiftl word_ao_nth word_size)

lemma word_and_mask_0_iff_not_testbits: "(w AND mask n) = 0 \<longleftrightarrow> (\<forall>i < n. \<not>w !! i)"
  using test_bit_size[of w] by (auto simp: word_ao_nth word_eq_iff word_size)

subsection \<open>@{const slice}\<close>

text \<open>We see @{const ucast} as a special case of @{const slice}.\<close>

lemma slice_zero [simp]:
  shows "slice 0 x = ucast x"
by (intro word_eqI) (simp add: nth_slice nth_ucast word_size)

lemma slice_beyond_length [simp]:
  fixes x :: "'a::len0 word"
  assumes len: "LENGTH('a) \<le> n"
  shows "slice n x = 0"
proof (intro word_eqI impI notI, clarsimp simp: word_size)
  fix m
  assume "m < LENGTH('b)" "slice n x !! m"
  hence "x !! (m + n)"
    by (simp add: nth_slice)
  from test_bit_size[OF this]
  have "m + n < LENGTH('a)"
    by (simp add: word_size)
  thus False
    using len by auto
qed

lemma slice_not:
  fixes x :: "'a::len word"
  shows "(slice n (NOT x)::'b::len word) = NOT (slice n x) AND mask (LENGTH('a) - n)"
proof (intro word_eqI iffI impI, unfold word_size)
  fix i
  assume length: "i < LENGTH('b)"
  assume "(slice n (NOT x)::'b word) !! i"
  hence "(NOT x) !! (i + n)"
    by (simp add: nth_slice)
  with test_bit_size[OF this]
  show "(NOT (slice n x::'b word) AND mask (LENGTH('a) - n)) !! i"
    using length
    by (auto simp: word_size nth_slice word_ops_nth_size)
next
  fix i
  assume "i < LENGTH('b)"
     and "(NOT (slice n x::'b word) AND mask (LENGTH('a) - n)) !! i"
  thus "(slice n (NOT x)::'b word) !! i"
    by (auto simp: word_size nth_slice word_ops_nth_size)
qed

corollary ucast_not:
  fixes x :: "'a::len word"
  shows "(ucast (NOT x)::'b::len word) = NOT (ucast x) AND mask LENGTH('a)"
using slice_not[where n=0]
by simp

lemma slice_or:
  shows "slice n (x OR y) = slice n x OR slice n y"
by (intro word_eqI)
   (auto simp: word_size word_ao_nth nth_slice)
    
lemma ucast_or:
  shows "ucast (x OR y) = ucast x OR ucast y"
using slice_or[where n=0]
by simp
(* Direct proof: 
unfolding ucast_def uint_or bitOR_word.abs_eq[THEN sym] .. *)

lemma slice_and:
  shows "slice n (x AND y) = slice n x AND slice n y"
by (intro word_eqI)
   (auto simp: word_size word_ao_nth nth_slice)
    
lemma ucast_and:
  shows "ucast (x AND y) = ucast x AND ucast y"
using slice_and[where n=0]
by simp
(* Direct proof: 
unfolding ucast_def uint_and bitAND_word.abs_eq[THEN sym] .. *)

lemma slice_xor:
  fixes x y :: "'a::len0 word"
  shows "(slice n (x XOR y)::'b::len0 word) = slice n x XOR slice n y"
proof (intro word_eqI iffI impI, unfold word_size)
  fix m
  assume "m < LENGTH('b)" 
     and "slice n (x XOR y) !! m"
  hence "(x XOR y) !! (m + n)"
    by (simp add: nth_slice)
  with test_bit_size[OF this]
  have "x !! (m + n) \<noteq> y !! (m + n)"
    by (simp add: word_ops_nth_size word_size)
  thus "((slice n x XOR slice n y)::'b::len0 word) !! m"
    using `m < LENGTH('b)`
    by (simp add: nth_slice word_ops_nth_size word_size)
next
  fix m
  assume "m < LENGTH('b)" 
     and "((slice n x XOR slice n y)::'b::len0 word) !! m"
  hence *: "x !! (m + n) \<noteq> y !! (m + n)"
    by (simp add: nth_slice word_ops_nth_size word_size)
  hence "m + n < LENGTH('a)"
    by (cases "x !! n") 
       (auto dest: test_bit_size simp: word_size)
  thus "(slice n (x XOR y)::'b::len0 word) !! m"
    using * `m < LENGTH('b)`
    by (simp add: nth_slice word_ops_nth_size word_size)
qed

lemma ucast_xor:
  fixes x y :: "'a::len word"
  shows "(ucast (x XOR y)::'b::len word) = ucast x XOR ucast y"
using slice_xor[where n=0]
by simp

(* lemma slice_word_of_int:
  assumes "n + LENGTH('a) \<le> LENGTH('b)"
  shows "(slice n (word_of_int m::'b::len word)::'a::len word) = 
         word_of_int (m div 2 ^ n)"
using assms
by (intro word_eqI)
   (auto simp: word_size nth_slice word_of_int zdiv_int bin_nth_div) *)

lemma slice_word_of_int:
  shows "slice n (word_of_int m::'a::len word) = 
         word_of_int (m div 2 ^ n) AND mask (LENGTH('a) - n)"
by (intro word_eqI)
   (auto simp: word_size nth_slice word_ao_nth word_of_int zdiv_int bin_nth_div)
  
corollary ucast_word_of_int:
  shows "ucast (word_of_int m::'a::len word) = 
         word_of_int m AND mask LENGTH('a)"
using slice_word_of_int[where n=0] 
by simp

corollary slice_of_nat:
  shows "slice n (of_nat m::'a::len word) = 
         of_nat (m div 2 ^ n) AND mask (LENGTH('a) - n)"
using slice_word_of_int[where m="int m" and n=n]
using zdiv_int[where a=m and b="2 ^ n", THEN sym]
by (simp add: word_of_int[THEN sym])
  
corollary ucast_of_nat:
  shows "(ucast (of_nat m::'b::len word)::'a::len word) = 
         of_nat m AND mask LENGTH('b)"
using slice_of_nat[where n=0]
by simp

(* corollary
  fixes x :: "'a::len word"
  shows "slice n x = x div (2 ^ n)"
proof -
  have "slice n x = word_of_int (uint x div 2 ^ n) AND mask (LENGTH('a) - n)"
    using slice_word_of_int[where m="uint x" and n=n and 'a='a]
    by simp

  have "... = x div (2 ^ n)"
    unfolding word_div_def
    apply auto
oops *)

lemma slice_mask [simp]:
  shows "slice n (mask m::'a::len word) = mask (min m LENGTH('a) - n)"
by (intro word_eqI) (auto simp add: nth_slice word_size)
  
corollary ucast_mask [simp]:
  shows "ucast ((mask n)::'a::len word) = mask (min n LENGTH('a))"
unfolding slice_zero[THEN sym]
by (simp del: slice_zero)

lemma slice_of_slice [simp]:
  shows "slice n (slice m x::'a::len0 word) = 
         slice (n + m) x AND mask (LENGTH('a) - n)"
by (intro word_eqI)
   (auto simp add: word_size nth_slice word_ao_nth add.assoc)

corollary slice_ucast [simp]:
  shows "slice n (ucast x::'a::len0 word) = 
         (slice n x) AND mask (LENGTH('a) - n)"
unfolding slice_zero[THEN sym]
by (simp del: slice_zero)

corollary ucast_slice [simp]:
  shows "ucast (slice n x::'a::len0 word) = 
         (slice n x) AND mask LENGTH('a)"
unfolding slice_zero[THEN sym]
by (simp del: slice_zero)

corollary ucast_ucast [simp]:
  shows "ucast (ucast x::'b::len0 word) = 
         ucast x AND mask LENGTH('b)"
unfolding slice_zero[THEN sym]
by (simp del: slice_zero)

lemma slice_word_and_mask [simp]:
  fixes x :: "'a::len word"
  assumes "LENGTH('b) + n \<le> m"
  shows "(slice n (x AND mask m)::'b::len0 word) = slice n x"
proof (intro word_eqI impI, simp only: word_size)
  fix i
  assume len: "i < LENGTH('b)"
  hence "i + n < m" using assms by simp
  thus "(slice n (x AND mask m)::'b word) !! i = (slice n x::'b word) !! i"
    using len Word.test_bit_size[where w=x and n="i + n"]
    by (auto simp add: nth_slice word_ao_nth word_size) 
qed

corollary ucast_word_and_mask [simp]:
  fixes x :: "'a::len word"
  assumes "LENGTH('b) \<le> m"
  shows "(ucast (x AND mask m)::'b::len0 word) = ucast x"
using assms
unfolding slice_zero[THEN sym]
by (simp del: slice_zero)

subsection \<open>@{const ucast}\<close>

text \<open>These lemmas are not a corollary of a corresponding lemma about @{const slice}.\<close>

thm ucast_id
declare ucast_id [simp]

lemma zero_less_ucast [simp]:
  fixes x :: "'a::len0 word"
  assumes "LENGTH('a) \<le> LENGTH('b)"
  shows "(0 < (ucast x::'b::len0 word)) = (0 < x)"
unfolding ucast_def word_less_def word_ubin.eq_norm bintr_uint[OF assms]
by auto

lemma one_less_ucast [simp]:
  fixes x :: "'a::len word"
  assumes "LENGTH('a) \<le> LENGTH('b)"
  shows "(1 < (ucast x::'b::len word)) = (1 < x)"
unfolding ucast_def word_less_def word_ubin.eq_norm bintr_uint[OF assms]
by auto

lemma one_le_ucast [simp]:
  fixes x :: "'a::len word"
  assumes "LENGTH('a) \<le> LENGTH('b)"
  shows "(1 \<le> (ucast x::'b::len word)) = (1 \<le> x)"
unfolding ucast_def word_le_def word_ubin.eq_norm bintr_uint[OF assms]
by auto

lemma ucast_up_eq [simp]:
  fixes x y :: "'a::len0 word"
  assumes "LENGTH('a) \<le> LENGTH('b)"
  shows "((ucast x::'b::len0 word) = (ucast y)) = (x = y)"
proof 
  assume ucast: "(ucast x::'b word) = ucast y"
  show "x = y"
    proof (intro word_eqI impI, unfold word_size)
      fix n
      assume "n < LENGTH('a)"
      thus "x !! n = y !! n"
        using test_bit_cong[where x=n, OF ucast] assms
        by (auto simp: nth_ucast)
    qed
qed simp

lemma uint_ucast [simp]:
  fixes x :: "'a::len word"
  shows "uint (ucast x::'b::len0 word) = 
         uint (x AND mask LENGTH('b))"
proof (intro bin_nth_eq_iff[THEN iffD1] ext)
  fix i
  show "bin_nth (uint (ucast x::'b word)) i = 
        bin_nth (uint (x AND mask LENGTH('b))) i"
    using test_bit_size[where w=x and n=i]
    by (auto simp add: test_bit_def'[THEN sym] 
                       nth_ucast 
                       word_ao_nth 
                       word_size)
qed

corollary unat_ucast [simp]:
  fixes x :: "'a::len word"
  shows "unat ((ucast x :: ('b :: len0) word)) = 
         unat (x AND mask (len_of TYPE('b)))"
unfolding unat_def
by simp

lemma ucast_max_word [simp]:
  shows "ucast (max_word::'a::len word) = mask LENGTH('a)"
by (intro word_eqI) (simp add: word_size nth_ucast)

lemma and_ucast_mask [simp]:
  fixes x :: "'a::len word"
  assumes "LENGTH('a) \<le> n"
  shows "(ucast x::'b::len word) AND mask n = ucast x"
proof (intro word_eqI impI iffI, unfold word_size)
  fix m
  assume "m < LENGTH('b)" "(ucast x::'b word) !! m"
  hence "x !! m"
    by (simp add: nth_ucast)
  from test_bit_size[OF this]
  have "m < n"
    using assms 
    unfolding word_size 
    by simp
  thus "((ucast x::'b word) AND mask n) !! m"
    using `m < LENGTH('b)` `x !! m`
    by (simp add: word_size nth_ucast word_ao_nth)
qed (simp add: nth_ucast word_ao_nth)

(* lemma ucast_max_word [simp]:
  assumes "LENGTH('b) \<le> LENGTH('a)"
  shows "(ucast (max_word::'a::len word)::'b::len word) = max_word"
using assms
by (intro word_eqI) (simp add: word_size nth_ucast) *)

declare word_cat_id [simp]

lemma ucast_word_cat [simp]:
  assumes "LENGTH('a) \<le> LENGTH('b)"
  shows "(ucast (word_cat w w'::'b::len0 word)::'a::len0 word) = word_cat w w'"
unfolding ucast_def word_cat_def 
unfolding word_ubin.eq_norm 
using assms
by (simp add: wi_bintr)

lemma ucast_shiftr:
  shows "(ucast (x >> n) :: ('b :: len0) word) = slice n x"
by (intro word_eqI)
   (simp add: word_size nth_slice nth_ucast nth_shiftr)

lemma ucast_shiftl:
  fixes x :: "'a::len word"
  shows "ucast (x << n) = ucast (x AND mask (LENGTH('a) - n)) << n"
by (intro word_eqI) (auto simp: nth_ucast nth_shiftl word_ao_nth word_size)

lemma ucast_plus_down:
  fixes x y :: "'a ::len0 word"
  assumes "LENGTH('b) \<le> LENGTH('a)"
  shows "(ucast (x + y)::'b::len0 word) = ucast x + ucast y"
proof -
  have "(2::int) ^ LENGTH('b) dvd 2 ^ LENGTH('a)"
    using le_imp_power_dvd[OF assms, where a="2::int"] 
    by simp
  from mod_mod_cancel[OF this]
  show ?thesis
    using assms mod_mod_cancel
    unfolding ucast_def uint_word_ariths
    unfolding word_uint.norm_eq_iff[THEN sym] wi_hom_syms[THEN sym]
    by simp
qed

lemma ucast_plus_up:
  fixes x y :: "'a ::len0 word"
  assumes "LENGTH('a) < LENGTH('b)"
  shows "(ucast (x + y)::'b::len word) = (ucast x + ucast y) AND mask (LENGTH('a))"
proof -
  have "LENGTH('a) \<le> LENGTH('b)"
    using assms by simp
  from le_imp_power_dvd[OF this, where a="2::int"] 
  have "(2::int) ^ LENGTH('a) dvd 2 ^ LENGTH('b)"
    by simp
  from mod_mod_cancel[OF this]
  show ?thesis  
    unfolding ucast_def uint_word_ariths and_mask_mod_2p wi_hom_syms[THEN sym] uint_word_of_int
    unfolding word_uint.norm_eq_iff[THEN sym]  
    by auto
qed

lemma ucast_minus_down:
  fixes x y :: "'a ::len0 word"
  assumes "LENGTH('b) \<le> LENGTH('a)"
  shows "(ucast (x - y)::'b::len0 word) = ucast x - ucast y"
proof -
  have "(2::int) ^ LENGTH('b) dvd 2 ^ LENGTH('a)"
    using le_imp_power_dvd[OF assms, where a="2::int"] 
    by simp
  from mod_mod_cancel[OF this]
  show ?thesis
    using assms mod_mod_cancel
    unfolding ucast_def uint_word_ariths
    unfolding word_uint.norm_eq_iff[THEN sym] wi_hom_syms[THEN sym]
    by simp
qed

lemma ucast_minus_up:
  fixes x y :: "'a ::len0 word"
  assumes "LENGTH('a) < LENGTH('b)"
  shows "(ucast (x - y)::'b::len word) = (ucast x - ucast y) AND mask (LENGTH('a))"
proof -
  have "LENGTH('a) \<le> LENGTH('b)"
    using assms by simp
  from le_imp_power_dvd[OF this, where a="2::int"] 
  have "(2::int) ^ LENGTH('a) dvd 2 ^ LENGTH('b)"
    by simp
  from mod_mod_cancel[OF this]
  show ?thesis  
    unfolding ucast_def uint_word_ariths and_mask_mod_2p wi_hom_syms[THEN sym] uint_word_of_int
    unfolding word_uint.norm_eq_iff[THEN sym]  
    by auto
qed

lemma uint_ucast_plus_ucast [simp]:
  fixes x :: "'a::len word"
    and y :: "'b::len word"
  assumes "LENGTH('a) < LENGTH('c)"
      and "LENGTH('b) < LENGTH('c)"
  shows "uint ((ucast x :: 'c::len word) + ucast y) = uint x + uint y"
proof -
  have x: "uint x < 2 ^ (LENGTH('c) - 1)"
    using less_le_trans[OF uint_lt[where w=x]] assms
    by auto
  have y: "uint y < 2 ^ (LENGTH('c) - 1)"
    using less_le_trans[OF uint_lt[where w=y]] assms
    by auto
  have "(2::int) * 2 ^ (LENGTH('c) - 1) = 2 ^ (Suc (LENGTH('c) - 1))"
    by (rule power_Suc[THEN sym])
  also have "... = 2 ^ LENGTH('c)"
    by auto
  finally have "uint x + uint y < 2 ^ LENGTH('c)"
    using add_strict_mono[OF x y]
    by auto
  hence *: "uint (ucast x :: 'c word) + uint (ucast y :: 'c word) < 2 ^ LENGTH('c)"
    using assms by simp
  show ?thesis
    using uint_add_lem[THEN iffD1, OF *]
    using assms
    by simp
qed

lemma uint_ucast_plus_one [simp]:
  fixes x :: "'a::len word"
  assumes "LENGTH('a) < LENGTH('c)"
      and "1 < LENGTH('c)"
  shows "uint ((ucast x :: 'c::len word) + 1) = uint x + 1"
    and "uint (1 + (ucast x :: 'c::len word)) = 1 + uint x"
using assms 
using uint_ucast_plus_ucast[where x=x and y="(1::1 word)" and 'c='c]
using uint_ucast_plus_ucast[where x="(1::1 word)" and y=x and 'c='c]
by auto

corollary unat_ucast_plus_one [simp]:
  fixes x :: "'a::len word"
  assumes "LENGTH('a) < LENGTH('c)"
      and "1 < LENGTH('c)"
  shows "unat ((ucast x :: 'c::len word) + 1) = unat x + 1"
    and "unat (1 + (ucast x :: 'c::len word)) = 1 + unat x"
using assms
unfolding unat_def
by (simp_all add: Suc_nat_eq_nat_zadd1)

corollary ucast_ucast_plus_one [simp]:
  fixes x :: "'a::len word"
  assumes "LENGTH('a) < LENGTH('c)"
      and "1 < LENGTH('c)"
  shows "(ucast ((ucast x :: 'c::len word) + 1)::'b::len word) = ucast x + 1"
    and "(ucast (1 + (ucast x :: 'c::len word))::'b::len word) = 1 + ucast x"
using arg_cong[where f="\<lambda>x. (word_of_int x::'b word)", OF uint_ucast_plus_one(1)[OF assms, of x]]
using arg_cong[where f="\<lambda>x. (word_of_int x::'b word)", OF uint_ucast_plus_one(2)[OF assms, of x]]
unfolding ucast_def
by (auto simp: wi_hom_syms)

lemma uint_ucast_plus_ucast_plus_one [simp]:
  fixes x :: "'a::len word"
    and y :: "'b::len word"
  assumes "LENGTH('a) < LENGTH('c)"
      and "LENGTH('b) < LENGTH('c)"
  shows "uint ((ucast x :: 'c::len word) + ucast y + 1) = uint x + uint y + 1"
proof -
  have x: "uint x < 2 ^ (LENGTH('c) - 1)"
    using less_le_trans[OF uint_lt[where w=x]] assms
    by auto
  have y: "uint y < 2 ^ (LENGTH('c) - 1)"
    using less_le_trans[OF uint_lt[where w=y]] assms
    by auto
  have "(2::int) * 2 ^ (LENGTH('c) - 1) = 2 ^ (Suc (LENGTH('c) - 1))"
    by (rule power_Suc[THEN sym])
  also have "... = 2 ^ LENGTH('c)"
    by auto
  finally have "uint x + uint y + 1 < 2 ^ LENGTH('c)"
    using zle_diff1_eq[THEN iffD2, OF x]
    using zle_diff1_eq[THEN iffD2, OF y]
    by auto
  hence "uint ((ucast x::'c word) + ucast y) + uint (1::'c word) < 2 ^ LENGTH('c)"
    using assms by simp
  from uint_add_lem[THEN iffD1, OF this]
  show ?thesis
    using assms by simp
qed

subsection \<open>@{const word_cat}\<close>

lemma nth_word_cat:
  fixes x :: "'a::len0 word"
    and y :: "'b::len0 word"
  shows "((word_cat x y)::'c::len0 word) !! n = 
         (n < len_of TYPE('c) \<and> 
          (if n < len_of TYPE('b) then y !! n else x !! (n - len_of TYPE('b))))"
unfolding word_cat_def
by (simp add: bin_nth_cat word_test_bit_def[THEN sym])

lemma word_cat_zero [simp]:
  shows "(word_cat 0 x) = ucast x"
using test_bit_size
by (intro word_eqI)
   (auto simp add: nth_word_cat nth_ucast word_size)

lemma word_cat_slice_zero [simp]:
  fixes x :: "'a::len word"
  assumes "LENGTH('b) = n"
      and "LENGTH('c) = LENGTH('a) - n"
  shows "word_cat (slice n x::'c::len0 word) (0::'b::len0 word) = x AND NOT mask n"
using assms
by (intro word_eqI)
  (auto simp: word_size nth_word_cat nth_slice word_ops_nth_size)

lemma test_bit_len: "(x :: 'a::len word) !! n \<Longrightarrow> n < LENGTH('a)"
  by (auto simp: test_bit_bin)

lemma word_cat_shiftl_OR: "word_cat xs (ys :: 'y::len word) = (ucast xs << LENGTH('y)) OR ucast ys"
  using test_bit_len
  by (intro word_eqI) (auto simp: nth_word_cat word_ao_nth nth_shiftl nth_ucast)

subsection \<open>@{const shiftl}\<close>

lemma shiftl_zero [simp]:
  fixes x :: "'a::len0 word"
  assumes "LENGTH('a) \<le> n"
  shows "x << n = 0"
using assms
by (intro word_eqI) (simp add: word_size nth_shiftl)

subsection \<open>@{const scast}\<close>

lemma nth_scast:
  fixes w :: "'a::len word"
  shows "(scast w::'b::len word) !! n = 
         ((if n < LENGTH('a) - 1 then w !! n else w !! (LENGTH('a) - 1)) \<and> n < len_of TYPE('b))"
unfolding scast_def test_bit_def' word_ubin.eq_norm nth_bintr nth_sint
by auto

lemma scast_alt_def:
  fixes x :: "'a::len word"
  assumes "LENGTH('c) = LENGTH('a) + LENGTH('b)"
      and "m = LENGTH('a) - 1"
  shows "scast x = (word_cat (if x !! m then max_word else 0::'b::len word) x::'c::len word)"
  (is "?l = ?r")
proof (intro word_eqI impI, unfold word_size)
  fix n
  show "?l !! n = ?r !! n"
    by (cases "n = m")
       (auto simp: assms word_size nth_word_cat nth_scast 
             split: if_splits)
qed

lemma scast_scast_shiftl:
  fixes x :: "'a::len word"
  assumes "LENGTH('a) + n \<le> LENGTH('b)"
  shows "(scast ((scast x::'b::len word) << n)::'c::len word) = scast x << n"
  (is "?l = ?r")
proof (intro word_eqI impI, unfold word_size)
  fix k
  assume len: "k < LENGTH('c)"
  have "1 \<le> LENGTH('a)"
    using add_leD2 discrete by blast
  hence *: "n \<le> LENGTH('b) - Suc 0"
    using assms
    by auto
  consider "k < n" 
         | "n \<le> k" "k - n < LENGTH('a) - 1" 
         | "n \<le> k" "LENGTH('a) - 1 \<le> k - n" 
    by arith
  thus "?l !! k = ?r !! k"
    proof cases
      case 1
      hence "\<not> ?l !! k" "\<not> ?r !! k"
        unfolding nth_scast nth_shiftl
        by simp_all
      thus ?thesis by simp
    next
      case 2
      hence "?l !! k = x !! (k - n)" "?r !! k = x !! (k - n)"
        unfolding nth_scast nth_shiftl
        using assms len
        by auto
      thus ?thesis by simp
    next
      case 3
      hence "?l !! k = x !! (LENGTH('a) - 1)" "?r !! k = x !! (LENGTH('a) - 1)"
        unfolding nth_scast nth_shiftl
        using assms len *
        by auto
      thus ?thesis by simp
    qed
qed

subsection \<open>Upper bits and @{const slice}\<close>

lemma slice_eq_imp_and_not_mask_eq:
  fixes x y :: "'a::len word"
  assumes length: "LENGTH('a) \<le> LENGTH('b) + n"
      and slice: "(slice n x::'b::len0 word) = slice n y"
  shows "(x AND NOT mask n) = (y AND NOT mask n)"
proof (intro word_eqI impI, simp add: word_size)
  fix i
  assume "i < LENGTH('a)"
  thus "(x AND NOT mask n) !! i = (y AND NOT mask n) !! i"
    using length test_bit_cong[OF slice, where x="i - n"]
    by (auto simp: word_size nth_slice word_ops_nth_size)
qed

lemma and_not_mask_eq_imp_slice_eq:
  fixes x y :: "'a::len word"
  assumes length: "LENGTH('b) + n \<le> LENGTH('a)"
      and mask: "(x AND NOT mask n) = (y AND NOT mask n)"
  shows "(slice n x::'b::len0 word) = slice n y"
proof (intro word_eqI impI, simp add: word_size)
  fix i
  assume "i < LENGTH('b)"
  thus "(slice n x::'b::len0 word) !! i = (slice n y::'b::len0 word) !! i"
    using length test_bit_cong[OF mask, where x="i + n"]
    by (auto simp: word_size nth_slice word_ops_nth_size)
qed

lemma eq_slice_eq_and_not_mask:
  fixes x y :: "'a::len word"
  assumes "LENGTH('a) = LENGTH('b) + n"
  shows "((slice n x::'b::len0 word) = slice n y) = 
         ((x AND NOT mask n) = (y AND NOT mask n))"
using assms 
using slice_eq_imp_and_not_mask_eq[where 'b='b and x=x and y=y and n=n]
using and_not_mask_eq_imp_slice_eq[where 'b='b and x=x and y=y and n=n]
by auto

subsection \<open>Lower bits and @{const ucast}\<close>

lemma ucast_eq_imp_and_mask_eq:
  fixes x y :: "'a::len word"
  assumes length: "n \<le> LENGTH('b)"
      and ucast: "(ucast x::'b::len0 word) = ucast y"
  shows "(x AND mask n) = (y AND mask n)"
proof (intro word_eqI impI, simp add: word_size)
  fix i
  assume "i < LENGTH('a)"
  thus "(x AND mask n) !! i = (y AND mask n) !! i"
    using length test_bit_cong[OF ucast, where x=i]
    by (auto simp: word_size nth_ucast word_ops_nth_size)
qed

lemma and_mask_eq_imp_ucast_eq:
  fixes x y :: "'a::len word"
  assumes length: "LENGTH('b) \<le> n"
      and mask: "(x AND mask n) = (y AND mask n)"
  shows "(ucast x::'b::len0 word) = ucast y"
proof (intro word_eqI impI, simp add: word_size)
  fix i  
  show "(ucast x::'b::len0 word) !! i = (ucast y::'b::len0 word) !! i"
    using test_bit_size[where w=x and n=i]
    using test_bit_size[where w=y and n=i]
    using length test_bit_cong[OF mask, where x=i]
    by (auto simp: word_size nth_ucast word_ao_nth)
qed

lemma eq_ucast_eq_and_mask:
  fixes x y :: "'a::len word"
  assumes "n = LENGTH('b)"
  shows "((ucast x::'b::len0 word) = ucast y) = 
         ((x AND mask n) = (y AND mask n))"
using assms 
using ucast_eq_imp_and_mask_eq[where 'b='b and x=x and y=y and n=n]
using and_mask_eq_imp_ucast_eq[where 'b='b and x=x and y=y and n=n]
by auto

subsection \<open>Aligned inequalities\<close>

lemma le_and_not_mask:
  fixes x y :: "'a::len word"
  assumes "x \<le> y"
  shows "x AND NOT mask n \<le> y AND NOT mask n"
proof -
  have "uint x \<le> uint y"
    using assms unfolding word_le_def by simp
  from zdiv_mono1[OF this]
  have "uint x div 2 ^ n \<le> uint y div 2 ^ n"
    by auto
  thus ?thesis  
    unfolding word_le_def
    by (simp add: uint_and_not_mask not_le)
qed

lemma le_right_and_not_mask:
  assumes "(ucast x::'b::len0 word) = 0"
      and "n = LENGTH('b)"
  shows "(x \<le> y AND NOT mask n) = (x \<le> y)"
proof
  assume "x \<le> y AND NOT mask n"
  thus "x \<le> y"
    using word_and_le2[where a=y and y="NOT mask n"]
    by auto
next
  have [simp]: "x AND mask n = 0"
    using assms eq_ucast_eq_and_mask[where x=x and y=0]
    by auto
  have [simp]: "x AND NOT mask n = x"
    using word_and_not_mask_plus_word_and_mask[where x=x and n=n]
    by simp
  assume "x \<le> y"
  from le_and_not_mask[where n=n, OF this]
  show "x \<le> y AND NOT mask n"
    by simp
qed

corollary less_left_and_not_mask:
  assumes "(ucast y::'b::len0 word) = 0"
      and "n = LENGTH('b)"
  shows "(x AND NOT mask n < y) = (x < y)"
using le_right_and_not_mask[where x=y and y=x, OF assms]
by auto

lemma word_and_mask_and_not_mask_size:
  fixes x :: "'a::len word"
  assumes "n \<le> m"
      and "n \<le> LENGTH('a)"
  shows "(x AND mask m) AND NOT mask n \<le> 2 ^ m - 2 ^ n"
unfolding word_power_of_two_difference[OF assms]
using le_and_not_mask[OF word_and_le1[where y=x and a="mask m"]]
by simp

corollary word_and_not_mask_and_mask_size:
  fixes x :: "'a::len word"
  assumes "n \<le> m"
      and "n \<le> LENGTH('a)"
  shows "(x AND NOT mask n) AND mask m \<le> 2 ^ m - 2 ^ n"
using word_and_mask_and_not_mask_size[OF assms]
using word_bool_alg.conj.assoc word_bool_alg.conj.commute
by metis

subsection \<open>Complete lattice over words\<close>

text \<open>Because @{typ "'a word"} is already an instantiation of the type class @{class order}, we
cannot create a class instance of @{class lattice} using a different order. We can, however, create
an interpretation of @{class lattice} using a different order.\<close>

subsubsection \<open>Interpretation of @{class order}\<close>

definition bitwise_less_eq :: "'a::len0 word \<Rightarrow> 'a::len0 word \<Rightarrow> bool" where
  "bitwise_less_eq w w' = (\<forall>i < len_of TYPE('a). w !! i \<longrightarrow> w' !! i)"

abbreviation (out) bitwise_less :: "'a::len0 word \<Rightarrow> 'a::len0 word \<Rightarrow> bool" where
  "bitwise_less x y \<equiv> (bitwise_less_eq x y) \<and> \<not>(bitwise_less_eq y x)"

interpretation bitwise_order: 
  order bitwise_less_eq bitwise_less
proof standard
  fix x :: "'a word"
  show "bitwise_less_eq x x"
    unfolding bitwise_less_eq_def
    by simp
next
  fix x y z :: "'a word"
  assume "bitwise_less_eq x y"
     and "bitwise_less_eq y z"
  thus   "bitwise_less_eq x z"
    unfolding bitwise_less_eq_def
    by auto
next
  fix x y :: "'a word"
  assume "bitwise_less_eq x y"
     and "bitwise_less_eq y x"
  thus   "x = y"
    unfolding bitwise_less_eq_def
    by (intro word_eqI) (auto simp add: word_size)
qed simp

subsubsection \<open>Interpretation of @{class order_bot}\<close>

abbreviation (out) bitwise_bot :: "'a::len0 word" where
  "bitwise_bot \<equiv> 0"

interpretation bitwise_order_bot: 
  order_bot bitwise_bot bitwise_less_eq bitwise_less
proof standard
  fix a :: "'a word"
  show "bitwise_less_eq bitwise_bot a"
    unfolding bitwise_less_eq_def
    by simp
qed

subsubsection \<open>Interpretation of @{class order_top}\<close>

abbreviation (out) bitwise_top :: "'a::len word" where
  "bitwise_top \<equiv> max_word"

interpretation bitwise_order_top: 
  order_top bitwise_less_eq bitwise_less bitwise_top
proof standard
  fix a :: "'a word"
  show "bitwise_less_eq a bitwise_top"
    unfolding bitwise_less_eq_def
    by simp
qed

subsubsection \<open>Interpretation of @{class semilattice_inf}\<close>

abbreviation (out) bitwise_inf :: "'a::len0 word \<Rightarrow> 'a::len0 word \<Rightarrow> 'a::len0 word" where
  "bitwise_inf a b \<equiv> a AND b"

interpretation bitwise_semilattice_inf: 
  semilattice_inf bitwise_inf bitwise_less_eq bitwise_less
proof standard
  fix a b :: "'a word"
  show "bitwise_less_eq (bitwise_inf a b) a"
    unfolding bitwise_less_eq_def 
    by (simp add: word_ops_nth_size word_size)
next
  fix a b :: "'a word"
  show "bitwise_less_eq (bitwise_inf a b) b"
    unfolding bitwise_less_eq_def 
    by (simp add: word_ops_nth_size word_size)
next
  fix x y z :: "'a word"
  assume "bitwise_less_eq x y"
     and "bitwise_less_eq x z"
  thus   "bitwise_less_eq x (bitwise_inf y z)"
    unfolding bitwise_less_eq_def 
    by (simp add: word_ops_nth_size word_size)

(* I don't understand the warning *)
qed

subsubsection \<open>Interpretation of @{class semilattice_sup}\<close>

abbreviation (out) bitwise_sup :: "'a::len0 word \<Rightarrow> 'a::len0 word \<Rightarrow> 'a::len0 word" where
  "bitwise_sup a b \<equiv> a OR b"

interpretation bitwise_semilattice_sup: 
  semilattice_sup bitwise_sup bitwise_less_eq bitwise_less
proof standard
  fix a b :: "'a word"
  show "bitwise_less_eq a (bitwise_sup a b)"
    unfolding bitwise_less_eq_def 
    by (simp add: word_ops_nth_size word_size)
next
  fix a b :: "'a word"
  show "bitwise_less_eq b (bitwise_sup a b)"
    unfolding bitwise_less_eq_def 
    by (simp add: word_ops_nth_size word_size)
next
  fix x y z :: "'a word"
  assume "bitwise_less_eq y x"
     and "bitwise_less_eq z x"
  thus   "bitwise_less_eq (bitwise_sup y z) x"
    unfolding bitwise_less_eq_def 
    by (simp add: word_ops_nth_size word_size)

(* I don't understand the warning *)
qed

subsubsection \<open>Interpretation of @{class distrib_lattice}\<close>

interpretation bitwise_distrib_lattice: 
  distrib_lattice bitwise_inf bitwise_less_eq bitwise_less bitwise_sup
by standard (fact word_oa_dist2)

subsubsection \<open>Interpretation of @{class boolean_algebra}\<close>

abbreviation (out) bitwise_uminus :: "'a::len0 word \<Rightarrow> 'a::len0 word" where
  "bitwise_uminus a \<equiv> NOT a"

abbreviation (out) bitwise_minus :: "'a::len0 word \<Rightarrow> 'a::len0 word \<Rightarrow> 'a::len0 word" where
  "bitwise_minus a b \<equiv> bitwise_inf a (bitwise_uminus b)"

interpretation bitwise_boolean_algebra: 
  boolean_algebra 
    bitwise_minus bitwise_uminus bitwise_inf bitwise_less_eq 
    bitwise_less bitwise_sup bitwise_bot bitwise_top
by standard simp_all

subsubsection \<open>Interpretation of @{class complete_lattice}\<close>

(*
fun list_Inf :: "nat \<Rightarrow> ('a :: Inf) list set \<Rightarrow> 'a list" where
  "list_Inf 0       A = []" |
  "list_Inf (Suc n) A = (Inf (list.hd ` A)) # (list_Inf n (list.tl ` A))"

definition bitwise_Inf :: "('a::len0) word set \<Rightarrow> 'a word" where
  "bitwise_Inf A = of_bl (list_Inf (len_of TYPE('a)) (to_bl ` A))"

fun list_Sup :: "nat \<Rightarrow> ('a :: Sup) list set \<Rightarrow> 'a list" where
  "list_Sup 0       A = []" |
  "list_Sup (Suc n) A = (Sup (list.hd ` A)) # (list_Sup n (list.tl ` A))"

definition bitwise_Sup :: "('a::len0) word set \<Rightarrow> 'a word" where
  "bitwise_Sup A = of_bl (list_Sup (len_of TYPE('a)) (to_bl ` A))"
*)

definition bitwise_Inf  :: "('a::len0) word set \<Rightarrow> 'a word" where
  "bitwise_Inf A = (BITS i. \<forall>x\<in>A. x !! i)"

definition bitwise_Sup  :: "('a::len0) word set \<Rightarrow> 'a word" where
  "bitwise_Sup A = (BITS i. \<exists>x\<in>A. x !! i)"

lemma nth_bitwise_Inf:
  fixes A :: "'a ::len0 word set"
  shows "bitwise_Inf A !! i = ((\<forall>x\<in>A. x !! i) \<and> i < len_of TYPE('a))"
unfolding bitwise_Inf_def test_bit.eq_norm
by simp

lemma nth_bitwise_Sup:
  fixes A :: "'a ::len0 word set"
  shows "bitwise_Sup A !! i = ((\<exists>x\<in>A. x !! i) \<and> i < len_of TYPE('a))"
unfolding bitwise_Sup_def test_bit.eq_norm
by simp

lemma setbits_True [simp]:
  shows "(BITS i. True) = bitwise_top"
apply (intro word_eqI)
unfolding word_size test_bit.eq_norm
by simp

lemma setbits_False [simp]:
  shows "(BITS i. False) = bitwise_bot"
apply (intro word_eqI)
unfolding word_size test_bit.eq_norm
by simp

interpretation bitwise_complete_lattice: 
  complete_lattice 
    bitwise_Inf bitwise_Sup bitwise_inf bitwise_less_eq 
    bitwise_less bitwise_sup bitwise_bot bitwise_top
proof standard
  fix x :: "'a word" and A 
  assume "x \<in> A"
  thus   "bitwise_less_eq (bitwise_Inf A) x"
    unfolding bitwise_less_eq_def nth_bitwise_Inf
    by auto
next
  fix z :: "'a word" and A 
  assume "\<And>x. x \<in> A \<Longrightarrow> bitwise_less_eq z x"
  thus   "bitwise_less_eq z (bitwise_Inf A)"
    unfolding bitwise_less_eq_def nth_bitwise_Inf
    by auto
next
  fix x :: "'a word" and A 
  assume "x \<in> A"
  thus   "bitwise_less_eq x (bitwise_Sup A)"
    unfolding bitwise_less_eq_def nth_bitwise_Sup
    by auto
next
  fix z :: "'a word" and A 
  assume "\<And>x. x \<in> A \<Longrightarrow> bitwise_less_eq x z"
  thus   "bitwise_less_eq (bitwise_Sup A) z"
    unfolding bitwise_less_eq_def nth_bitwise_Sup
    by auto
next
  show "bitwise_Inf {} = bitwise_top"
    unfolding bitwise_Inf_def
    by simp
next
  show "bitwise_Sup {} = bitwise_bot"
    unfolding bitwise_Sup_def
    by simp
qed

(*subsubsection \<open>Interpretation of @{class complete_distrib_lattice}\<close>

interpretation bitwise_complete_distrib_lattice: 
  complete_distrib_lattice 
    bitwise_Inf bitwise_Sup bitwise_inf bitwise_less_eq 
    bitwise_less bitwise_sup bitwise_bot bitwise_top
proof standard
  fix a :: "'a word" and B
  show "bitwise_sup a (bitwise_Inf B) = bitwise_complete_lattice.INFIMUM B (bitwise_sup a)"
    apply (intro word_eqI)
    unfolding word_size 
    by (simp add: word_ao_nth nth_bitwise_Inf)
next
  fix a :: "'a word" and B
  show "bitwise_inf a (bitwise_Sup B) = bitwise_complete_lattice.SUPREMUM B (bitwise_inf a)"
    apply (intro word_eqI)
    unfolding word_size 
    by (simp add: word_ao_nth nth_bitwise_Sup)
qed

subsubsection \<open>Interpretation of @{class complete_boolean_algebra}\<close>

interpretation bitwise_complete_boolean_algebra: 
  complete_boolean_algebra 
    bitwise_Inf bitwise_Sup bitwise_inf bitwise_less_eq 
    bitwise_less bitwise_sup bitwise_bot bitwise_top
    bitwise_minus bitwise_uminus
by standard*)

(*<*)
end
(*>*)
