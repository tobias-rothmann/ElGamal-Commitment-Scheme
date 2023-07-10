theory ElGamal
  imports "CryptHOL.CryptHOL" "CryptHOL.Cyclic_Group" "Sigma_Commit_Crypto.Commitment_Schemes" "Berlekamp_Zassenhaus.Finite_Field_Factorization"
  "HOL-Number_Theory.Cong"   "Sigma_Commit_Crypto.Cyclic_Group_Ext" 
  "Sigma_Commit_Crypto.Number_Theory_Aux"
  "Sigma_Commit_Crypto.Uniform_Sampling"
  "HOL-Algebra.Coset"
begin

text \<open>I formalize the ElGamal Commitment Scheme and show its correctness and soundness wrt. 
it's hiding and binding property. 
Sigma_Commit_Crypto.Commitment_Schemes gives the basis which outlines how commitment 
schemes are formalized in Isabelle. On top of this template I define the relevant functions and show 
the game-based proofs of interest, namely correctness and the hiding and the binding property.\<close>

section \<open>Assumptions\<close>

subsection \<open>Decisional Diffie Hellmann Assumption (DDH)\<close>

locale DDH = G : Cyclic_Group.cyclic_group G
for G (structure)
begin

type_synonym 'grp adversary = "'grp * 'grp * 'grp \<Rightarrow> bool spmf"

definition game :: "'a adversary \<Rightarrow> bool spmf" where 
  "game \<A> = TRY do { 
    s \<leftarrow> sample_uniform (order G);
    y \<leftarrow> sample_uniform (order G);
    r \<leftarrow> sample_uniform (order G);
    b \<leftarrow> coin_spmf;
    b' \<leftarrow> \<A> (if b then (\<^bold>g [^] s, \<^bold>g [^] y, \<^bold>g [^] (s*y)) else (\<^bold>g [^] s,\<^bold>g [^] y,\<^bold>g [^] r));
    return_spmf (b=b') 
  } ELSE return_spmf False"


definition advantage :: "'a adversary \<Rightarrow> real"
  where "advantage \<A> = spmf (game \<A>) True - 1/2" \<comment>\<open>subtract Pr random pick\<close>

(* adapted proof from Sigma_Commit_Crypto.Commitment_Schemes bind_game_alt_def  *)
lemma game_alt_def:
  "game \<A> =  TRY do { 
    s \<leftarrow> sample_uniform (order G);
    y \<leftarrow> sample_uniform (order G);
    r \<leftarrow> sample_uniform (order G);
    b \<leftarrow> coin_spmf;
    b' \<leftarrow> \<A> (if b then (\<^bold>g [^] s, \<^bold>g [^] y, \<^bold>g [^] (s*y)) else (\<^bold>g [^] s,\<^bold>g [^] y,\<^bold>g [^] r));
    _::unit \<leftarrow> assert_spmf (b=b');
    return_spmf True 
  } ELSE return_spmf False"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = TRY do { 
    s \<leftarrow> sample_uniform (order G);
      TRY do { 
      y \<leftarrow> sample_uniform (order G);
        TRY do { 
        r \<leftarrow> sample_uniform (order G);
          TRY do { 
          b \<leftarrow> coin_spmf;
            TRY do { 
            b' \<leftarrow> \<A> (if b then (\<^bold>g [^] s, \<^bold>g [^] y, \<^bold>g [^] (s*y)) else (\<^bold>g [^] s,\<^bold>g [^] y,\<^bold>g [^] r));
            TRY do { 
            return_spmf (b=b') 
            } ELSE return_spmf False
          } ELSE return_spmf False
        } ELSE return_spmf False
      } ELSE return_spmf False
    } ELSE return_spmf False
  } ELSE return_spmf False"
    unfolding split_def game_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  also have "\<dots> = TRY do { 
    s \<leftarrow> sample_uniform (order G);
      TRY do { 
      y \<leftarrow> sample_uniform (order G);
        TRY do { 
        r \<leftarrow> sample_uniform (order G);
          TRY do { 
          b \<leftarrow> coin_spmf;
            TRY do { 
            b' \<leftarrow> \<A> (if b then (\<^bold>g [^] s, \<^bold>g [^] y, \<^bold>g [^] (s*y)) else (\<^bold>g [^] s,\<^bold>g [^] y,\<^bold>g [^] r));
            TRY do { 
            _ :: unit \<leftarrow>assert_spmf (b=b');
            return_spmf True 
            } ELSE return_spmf False
          } ELSE return_spmf False
        } ELSE return_spmf False
      } ELSE return_spmf False
    } ELSE return_spmf False
  } ELSE return_spmf False"
    by(auto simp add: try_bind_assert_spmf try_spmf_return_spmf1 intro!: try_spmf_cong bind_spmf_cong)
  also have "\<dots> = ?rhs"
    unfolding split_def Let_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  finally show ?thesis .
qed

end

section \<open>Commitment Functions\<close>

locale ElGamal_Commit_base =
  fixes G :: "'grp Cyclic_Group.cyclic_group" (structure)
assumes prime_order: "prime (order G)"
and G_cyclic: "Cyclic_Group.cyclic_group G"
begin

type_synonym ck = "nat" (*s is Zp*)
type_synonym 'grp' vk = "'grp'"
type_synonym 'grp' plain = "'grp'"
type_synonym 'grp' commit = "'grp' * 'grp'"
type_synonym "opening" = "nat * nat" (*s and y is Zp*)

definition key_gen :: "(ck \<times> 'grp vk) spmf"
where 
  "key_gen = do {
    s :: nat \<leftarrow> sample_uniform (order G);
    return_spmf (s, \<^bold>g [^] s) 
  }" 

definition commit :: "ck \<Rightarrow> 'grp plain \<Rightarrow> ('grp commit \<times> opening) spmf"
where 
  "commit ck m = do {
    y :: nat \<leftarrow> sample_uniform (order G);
    return_spmf ((\<^bold>g [^] y, m \<otimes> (\<^bold>g [^] (ck*y))), (ck,y)) 
  }"

definition verify :: "'grp vk \<Rightarrow> 'grp plain \<Rightarrow> 'grp commit \<Rightarrow> opening \<Rightarrow> bool"
where 
  "verify v_key m c d = (let (gy, gsy) = c; (s,y) = d in 
  (\<^bold>g [^] s = v_key \<and> gy = \<^bold>g [^] y \<and> m \<otimes> \<^bold>g [^] (s*y) = gsy)
)"                                                    

definition valid_msg :: "'grp plain \<Rightarrow> bool"
  where "valid_msg msg \<equiv> msg \<in> carrier G" (* m \<in> carrier G*)

sublocale elgamal_commit: abstract_commitment key_gen commit verify valid_msg .

sublocale DDH_asm: DDH G
  unfolding DDH_def using G_cyclic .

end

section \<open>Commitment Proofs\<close>

locale ElGamal_Commit = ElGamal_Commit_base + cyclic_group G
begin

subsection \<open>Correctness\<close>

lemma correct:
  shows "spmf (elgamal_commit.correct_game m) True = 1" 
  apply (simp add: abstract_commitment.correct_game_def commit_def verify_def key_gen_def)
  apply(simp add: Let_def bind_spmf_const lossless_weight_spmfD cong: bind_spmf_cong_simp)
  apply (simp add: DDH_asm.G.order_gt_0)
  done

theorem abstract_correct:
  shows "elgamal_commit.correct"
  unfolding abstract_commitment.correct_def using correct by blast

subsection \<open>Soundness wrt. binding (i.e. a commitment cannot be resolved to two different messages)\<close>

lemma g_pow_i_eq_i_eq: "\<^bold>g [^] (s'::nat) = \<^bold>g [^] s \<longleftrightarrow> s' mod order G = s mod order G"
proof -
  have "\<^bold>g [^] (s'::nat) = \<^bold>g [^] s \<longleftrightarrow> [s'=s] (mod order G)"
    by (rule  DDH_asm.G.pow_generator_eq_iff_cong) (simp add: DDH_asm.G.finite_carrier)
  then show ?thesis using cong_def by blast
qed

lemma assert_anding: "TRY do {
          _ :: unit \<leftarrow> assert_spmf (a);
            _ :: unit \<leftarrow> assert_spmf (b);
            return_spmf True
        } ELSE return_spmf False 
    = TRY do {
          _ :: unit \<leftarrow> assert_spmf (a \<and> b);
          return_spmf True
      } ELSE return_spmf False"
  by (simp add: try_bind_assert_spmf)

lemma helping_1: "( s' mod order G = s mod order G \<and> gy = \<^bold>g [^] y \<and> m \<otimes> \<^bold>g [^] (s'*y) = gsy 
      \<and> s'' mod order G = s mod order G \<and> gy = \<^bold>g [^] y' \<and> m' \<otimes> \<^bold>g [^] (s''*y') = gsy) 
= ( s' mod order G = s mod order G \<and> gy = \<^bold>g [^] y \<and> m \<otimes> \<^bold>g [^] (s'*y) = gsy 
                             \<and> s'' mod order G = s mod order G \<and> gy = \<^bold>g [^] y' \<and> m' \<otimes> \<^bold>g [^] (s''*y') = gsy
                             \<and> y mod order G =y' mod order G)"
  by (auto simp: g_pow_i_eq_i_eq)

lemma helping_2: "(s' mod order G = s mod order G \<and> gy = \<^bold>g [^] y \<and> m \<otimes> \<^bold>g [^] (s'*y) = gsy 
                 \<and> s'' mod order G = s mod order G \<and> gy = \<^bold>g [^] y' \<and> m' \<otimes> \<^bold>g [^] (s''*y') = gsy
                 \<and> y mod order G =y' mod order G)
                 = (s' mod order G = s mod order G \<and> gy = \<^bold>g [^] y \<and> m \<otimes> \<^bold>g [^] (s'*y) = gsy 
                  \<and> s'' mod order G = s mod order G \<and> gy = \<^bold>g [^] y' \<and> m' \<otimes> \<^bold>g [^] (s''*y') = gsy
                  \<and> y mod order G =y' mod order G \<and>  s' mod order G = s'' mod order G)"
  by linarith

lemma helping_3 : "(m \<noteq> m' \<and> valid_msg m \<and> valid_msg m' \<and> 
                                s' mod order G = s mod order G \<and> gy = \<^bold>g [^] y \<and> m \<otimes> \<^bold>g [^] (s'*y) = gsy 
                             \<and> s'' mod order G = s mod order G \<and> gy = \<^bold>g [^] y' \<and> m' \<otimes> \<^bold>g [^] (s''*y') = gsy
                             \<and> y mod order G =y' mod order G \<and>  s' mod order G = s'' mod order G) = False"
proof -
  have "(m \<noteq> m' \<and> valid_msg m \<and> valid_msg m' 
                \<and> m \<otimes> \<^bold>g [^] (s'*y) = gsy 
                \<and> m' \<otimes> \<^bold>g [^] (s''*y') = gsy
                \<and> y mod order G =y' mod order G \<and>  s' mod order G = s'' mod order G) 
                = False"
    by (metis (no_types, lifting) DDH_asm.G.generator_closed DDH_asm.G.nat_pow_closed DDH_asm.G.right_cancel g_pow_i_eq_i_eq mod_mult_cong valid_msg_def)
  then show ?thesis by blast
qed

theorem elgamal_bind: "elgamal_commit.bind_advantage \<A> = 0"
  including monad_normalisation
  unfolding abstract_commitment.bind_advantage_def
proof -
  have "elgamal_commit.bind_game \<A> = TRY do {
    (ck, vk) \<leftarrow> key_gen;
    (c, m, d, m', d') \<leftarrow> \<A> ck;
    _ :: unit \<leftarrow> assert_spmf (m \<noteq> m' \<and> valid_msg m \<and> valid_msg m');
    let b = verify vk m c d;
    let b' = verify vk m' c d';
    _ :: unit \<leftarrow> assert_spmf (b \<and> b'); 
    return_spmf True} ELSE return_spmf False
    "
    by (simp add: elgamal_commit.bind_game_alt_def)
  also have "\<dots>= TRY do {
    (ck, vk) \<leftarrow> key_gen;
    ((gy,gsy), m, (s,y), m', (s',y')) \<leftarrow> \<A> ck;
    _ :: unit \<leftarrow> assert_spmf (m \<noteq> m' \<and> valid_msg m \<and> valid_msg m');
    let b = verify vk m (gy,gsy) (s,y);
    let b' = verify vk m' (gy,gsy) (s',y');
    _ :: unit \<leftarrow> assert_spmf (b \<and> b'); 
    return_spmf True} ELSE return_spmf False
    "
    by (simp add: split_def)
  also have "\<dots> = TRY do {
    s :: nat \<leftarrow> sample_uniform (order G);
    ((gy,gsy), m, (s',y), m', (s'',y')) \<leftarrow> \<A> s;
    _ :: unit \<leftarrow> assert_spmf (m \<noteq> m' \<and> valid_msg m \<and> valid_msg m');
    _ :: unit \<leftarrow> assert_spmf (\<^bold>g [^] s' = (\<^bold>g [^] s) \<and> gy = \<^bold>g [^] y \<and> m \<otimes> \<^bold>g [^] (s'*y) = gsy 
                             \<and> \<^bold>g [^] s'' = (\<^bold>g [^] s) \<and> gy = \<^bold>g [^] y' \<and> m' \<otimes> \<^bold>g [^] (s''*y') = gsy); 
    return_spmf True} ELSE return_spmf False
    "
    by (simp add: verify_def key_gen_def)
  also have "\<dots> = TRY do {
     s :: nat \<leftarrow> sample_uniform (order G);
    TRY do {
      ((gy,gsy), m, (s', y), m', (s'', y')) \<leftarrow> \<A> s;
      TRY do {
        _ :: unit \<leftarrow> assert_spmf (m \<noteq> m' \<and> valid_msg m \<and> valid_msg m');
       _ :: unit \<leftarrow> assert_spmf (\<^bold>g [^] s' = (\<^bold>g [^] s) \<and> gy = \<^bold>g [^] y \<and> m \<otimes> \<^bold>g [^] (s'*y) = gsy 
                             \<and> \<^bold>g [^] s'' = (\<^bold>g [^] s) \<and> gy = \<^bold>g [^] y' \<and> m' \<otimes> \<^bold>g [^] (s''*y') = gsy); 
        return_spmf True} ELSE return_spmf False
      } ELSE return_spmf False
    } ELSE return_spmf False
    "
  unfolding split_def
  by(fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
  also have "\<dots> = TRY do {
    s :: nat \<leftarrow> sample_uniform (order G);
    TRY do {
      ((gy,gsy), m, (s', y), m', (s'', y')) \<leftarrow> \<A> s;
      TRY do {
        _ :: unit \<leftarrow> assert_spmf (m \<noteq> m' \<and> valid_msg m \<and> valid_msg m' \<and> 
                                (\<^bold>g [^] s' = (\<^bold>g [^] s) \<and> gy = \<^bold>g [^] y \<and> m \<otimes> \<^bold>g [^] (s'*y) = gsy 
                             \<and> \<^bold>g [^] s'' = (\<^bold>g [^] s) \<and> gy = \<^bold>g [^] y' \<and> m' \<otimes> \<^bold>g [^] (s''*y') = gsy)); 
        return_spmf True} ELSE return_spmf False
      } ELSE return_spmf False
    } ELSE return_spmf False
    "
    using assert_anding by presburger
  also have "\<dots> = TRY do {
    s :: nat \<leftarrow> sample_uniform (order G);
      ((gy,gsy), m, (s', y), m', (s'', y')) \<leftarrow> \<A> s;
        _ :: unit \<leftarrow> assert_spmf (m \<noteq> m' \<and> valid_msg m \<and> valid_msg m' \<and> 
                                (\<^bold>g [^] s' = \<^bold>g [^] s \<and> gy = \<^bold>g [^] y \<and> m \<otimes> \<^bold>g [^] (s'*y) = gsy 
                             \<and> \<^bold>g [^] s'' = \<^bold>g [^] s \<and> gy = \<^bold>g [^] y' \<and> m' \<otimes> \<^bold>g [^] (s''*y') = gsy)); 
        return_spmf True} ELSE return_spmf False
    "
   unfolding split_def Let_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  also have "\<dots> = TRY do {
    s :: nat \<leftarrow> sample_uniform (order G);
      ((gy,gsy), m, (s', y), m', (s'', y')) \<leftarrow> \<A> s;
        _ :: unit \<leftarrow> assert_spmf (m \<noteq> m' \<and> valid_msg m \<and> valid_msg m' \<and> 
                                s' mod order G = s mod order G \<and> gy = \<^bold>g [^] y \<and> m \<otimes> \<^bold>g [^] (s'*y) = gsy 
                             \<and> s'' mod order G = s mod order G \<and> gy = \<^bold>g [^] y' \<and> m' \<otimes> \<^bold>g [^] (s''*y') = gsy); 
        return_spmf True} ELSE return_spmf False
    " 
    using g_pow_i_eq_i_eq by simp
   also have "\<dots> = TRY do {
    s :: nat \<leftarrow> sample_uniform (order G);
      ((gy,gsy), m, (s', y), m', (s'', y')) \<leftarrow> \<A> s;
        _ :: unit \<leftarrow> assert_spmf (m \<noteq> m' \<and> valid_msg m \<and> valid_msg m' \<and> 
                                s' mod order G = s mod order G \<and> gy = \<^bold>g [^] y \<and> m \<otimes> \<^bold>g [^] (s'*y) = gsy 
                             \<and> s'' mod order G = s mod order G \<and> gy = \<^bold>g [^] y' \<and> m' \<otimes> \<^bold>g [^] (s''*y') = gsy
                             \<and> y mod order G =y' mod order G); 
        return_spmf True} ELSE return_spmf False
    " 
     using helping_1 by algebra
  also have "\<dots> = TRY do {
    s :: nat \<leftarrow> sample_uniform (order G);
      ((gy,gsy), m, (s', y), m', (s'', y')) \<leftarrow> \<A> s;
        _ :: unit \<leftarrow> assert_spmf (m \<noteq> m' \<and> valid_msg m \<and> valid_msg m' \<and> 
                                s' mod order G = s mod order G \<and> gy = \<^bold>g [^] y \<and> m \<otimes> \<^bold>g [^] (s'*y) = gsy 
                             \<and> s'' mod order G = s mod order G \<and> gy = \<^bold>g [^] y' \<and> m' \<otimes> \<^bold>g [^] (s''*y') = gsy
                             \<and> y mod order G =y' mod order G \<and>  s' mod order G = s'' mod order G); 
        return_spmf True} ELSE return_spmf False
    " 
    using helping_2 by algebra
  also have "\<dots> = TRY do {
    s :: nat \<leftarrow> sample_uniform (order G);
      ((gy,gsy), m, (s', y), m', (s'', y')) \<leftarrow> \<A> s;
        _ :: unit \<leftarrow> assert_spmf (False); 
        return_spmf True} ELSE return_spmf False
    " 
    by (simp add: helping_3)
  also have "\<dots>= TRY do {
    s :: nat \<leftarrow> sample_uniform (order G);
      ((gy,gsy), m, (s', y), m', (s'', y')) \<leftarrow> \<A> s; 
        return_pmf None} ELSE return_spmf False
    "
    by simp
 also have "\<dots>= return_spmf False
    "
   by (simp add: split_def)
  finally show "spmf (elgamal_commit.bind_game \<A>) True = 0" by fastforce
qed

subsection \<open>Soundness wrt. hiding (i.e. the adversary can propose two messages, of which one will be
committed to, and the adversary cannot determine to which one the commitment belongs with more than 
a 50/50 chance (coin flip))\<close>

thm  spmf.map_comp[symmetric]
thm o_def

(* 
Helping Lemma for hiding.
What I would need for this lemma is that ck (which is s) is also
from sample_uniform. This is the case for the hiding game, however since first the 
Adversary has to work on an input that depends on s, although s cannot change in that, I don't know 
how to lift the sample_uniform bind from s into a map_spmf for s...*)
lemma sample_uniform_one_time_pad_ext: 
  "map_spmf (\<lambda>y. (c', \<^bold>g [^] y, c \<otimes> (\<^bold>g [^] (ck*y)))) (sample_uniform (order G))
  = map_spmf (\<lambda>y. (c',\<^bold>g [^] y, (\<^bold>g [^] (ck*y)))) (sample_uniform (order G))"
  (is "?lhs = ?rhs")
proof -
  have triple_eq: "(\<lambda>y. (c', \<^bold>g [^] y, (\<^bold>g [^] y) [^] ck)) ` {..<order G} = {(c', x, x [^] ck) |x. x \<in> ([^]) \<^bold>g ` {..<order G}}"
    by blast
  have "?lhs = map_spmf (\<lambda>x. let (c',gy, gy') = x in (c',gy, c \<otimes> gy')) ?rhs"
    by (simp add: pmf.map_comp o_def option.map_comp DDH_asm.G.nat_pow_pow)
  also have "?rhs = spmf_of_set ((\<lambda>y. (c', \<^bold>g [^] y, \<^bold>g [^] (ck*y))) ` {..<order G})"
    apply (simp add: DDH_asm.G.carrier_conv_generator DDH_asm.G.inj_on_generator sample_uniform_def)
    apply (rule map_spmf_of_set_inj_on[of "(\<lambda>y. (c', \<^bold>g [^] y, \<^bold>g [^] (ck*y)))" "{..<order G}"])
    apply (simp add: inj_on_def)
    apply (metis inj_on_def DDH_asm.G.inj_on_generator)
    done
  also have "\<dots>= spmf_of_set ((\<lambda>y. (c', \<^bold>g [^] y, (\<^bold>g [^] y) [^] ck)) ` {..<order G})"
     by (simp add: DDH_asm.G.nat_pow_pow mult.commute)
  also have rhs: "\<dots>= spmf_of_set ({(c',x, x [^] ck) | x. x \<in> carrier G})"
    by (simp add: DDH_asm.G.carrier_conv_generator triple_eq) 
  also have "map_spmf (\<lambda>x. let (c',gy, gy') = x in (c',gy, c \<otimes> gy' [^] ck)) \<dots> 
  = spmf_of_set ((\<lambda>x. let (c',gy, gy') = x in (c',gy, c \<otimes> gy' [^] ck)) ` {(c',x, x [^] ck) | x. x \<in> carrier G})"
    apply(rule map_spmf_of_set_inj_on)
    apply (simp add: inj_on_def)
    done
  moreover have "(\<lambda>x. let (c',gy, gy') = x in (c',gy, c \<otimes> gy' [^] ck)) ` {(c',x, x [^] ck) | x. x \<in> carrier G} 
    = {(c',x, x [^] ck) | x. x \<in> carrier G}"
    apply (rule endo_inj_surj)
      apply (simp add: DDH_asm.G.finite_carrier)
     prefer 2
     apply (simp add: inj_on_def)
    apply (simp add: subset_eq)
    sorry
  ultimately show ?thesis sorry
qed

lemma if_in_carrier: "x \<in> carrier G \<Longrightarrow> y \<in> carrier G \<Longrightarrow> (if b then x else y) \<in> carrier G"
  by presburger

lemma sample_uniform_one_time_pad_preop:
  "map_spmf (\<lambda>y. (\<^bold>g [^] y, c \<otimes> (\<^bold>g [^] (ck*y)))) (sample_uniform (order G))
  = map_spmf (\<lambda>y. (\<^bold>g [^] y, (\<^bold>g [^] (y)))) (sample_uniform (order G))"
  using DDH_asm.G.sample_uniform_one_time_pad
  sorry

lemma perfect_hiding:
  shows "spmf (elgamal_commit.hiding_game_ind_cpa \<A>) True - 1/2 = 0"
  including monad_normalisation
proof -
  obtain \<A>1 \<A>2 where [simp]: "\<A> = (\<A>1, \<A>2)" by(cases \<A>)
  note [simp] = Let_def split_def 
  have "elgamal_commit.hiding_game_ind_cpa (\<A>1, \<A>2) = TRY do {
    (ck,vk) \<leftarrow> key_gen;
    ((m0, m1), \<sigma>) \<leftarrow> \<A>1 vk;
    _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
    b \<leftarrow> coin_spmf;  
    (c,d) \<leftarrow> commit ck (if b then m0 else m1);
    b' \<leftarrow> \<A>2 c \<sigma>;
    return_spmf (b' = b)} ELSE coin_spmf"
      by(simp add: abstract_commitment.hiding_game_ind_cpa_def valid_msg_def)
  also have "... = TRY do {
    s :: nat \<leftarrow> sample_uniform (order G);
    let (ck,vk) = (s, \<^bold>g [^] s);
    ((m0, m1), \<sigma>) \<leftarrow> \<A>1 vk;
    _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
     b \<leftarrow> coin_spmf; 
    y :: nat \<leftarrow> sample_uniform (order G);
    let c =(\<^bold>g [^] y, (if b then m0 else m1) \<otimes> (\<^bold>g [^] (ck*y)));
    b' \<leftarrow> \<A>2 c \<sigma>;
    return_spmf (b' = b)} ELSE coin_spmf"
      by(simp add: commit_def key_gen_def)
  also have "... = TRY do {
    s :: nat \<leftarrow> sample_uniform (order G);
    let (ck,vk) = (s, \<^bold>g [^] s);
    ((m0, m1), \<sigma>) \<leftarrow> \<A>1 vk;
    _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
    b \<leftarrow> coin_spmf; 
    z \<leftarrow> map_spmf (\<lambda>y. (\<^bold>g [^] y, (if b then m0 else m1) \<otimes> (\<^bold>g [^] (ck*y)))) (sample_uniform (order G));
    guess :: bool \<leftarrow> \<A>2 z \<sigma>;
    return_spmf(guess = b)} ELSE coin_spmf"
    by(simp add: bind_map_spmf o_def)
  also have "... = TRY do {
    s :: nat \<leftarrow> sample_uniform (order G);
    ((m0, m1), \<sigma>) \<leftarrow> \<A>1 (\<^bold>g [^] s);
    _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
    b \<leftarrow> coin_spmf; 
    z \<leftarrow> map_spmf (\<lambda>y. (\<^bold>g [^] y, (if b then m0 else m1) \<otimes> (\<^bold>g [^] (s*y)))) (sample_uniform (order G));
    guess :: bool \<leftarrow> \<A>2 z \<sigma>;
    return_spmf(guess = b)} ELSE coin_spmf"
    by simp
  also have "... = TRY do {
    s :: nat \<leftarrow> sample_uniform (order G);
    ((m0, m1), \<sigma>) \<leftarrow> \<A>1 (\<^bold>g [^] s);
    _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
    b \<leftarrow> coin_spmf; 
    z \<leftarrow> map_spmf (\<lambda>y. (\<^bold>g [^] y ,(\<^bold>g [^] (y)))) (sample_uniform (order G));
    guess :: bool \<leftarrow> \<A>2 z \<sigma>;
    return_spmf(guess = b)} ELSE coin_spmf"
    unfolding valid_msg_def
    by (simp add: sample_uniform_one_time_pad_preop)
  also have "... = TRY do {
    s :: nat \<leftarrow> sample_uniform (order G);
    ((m0, m1), \<sigma>) \<leftarrow> \<A>1 (\<^bold>g [^] s);
    _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
    z \<leftarrow> map_spmf (\<lambda>y. (\<^bold>g [^] y, \<^bold>g [^] y)) (sample_uniform (order G));
    guess :: bool \<leftarrow> \<A>2 z \<sigma>;
    map_spmf((=) guess) coin_spmf} ELSE coin_spmf"
      by(simp add: map_spmf_conv_bind_spmf)
  also have "... = coin_spmf"
     by(auto simp add: bind_spmf_const map_eq_const_coin_spmf try_bind_spmf_lossless2' scale_bind_spmf weight_spmf_le_1 scale_scale_spmf)
  ultimately show ?thesis by(simp add: spmf_of_set)
qed

theorem abstract_perfect_hiding: 
  shows "elgamal_commit.perfect_hiding_ind_cpa \<A>"
proof-
  have "spmf (elgamal_commit.hiding_game_ind_cpa \<A>) True - 1/2 = 0" 
    using perfect_hiding by fastforce
  thus ?thesis 
    by(simp add: abstract_commitment.perfect_hiding_ind_cpa_def abstract_commitment.hiding_advantage_ind_cpa_def)
qed

end

end