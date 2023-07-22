theory BeOriginal
  imports "CryptHOL.CryptHOL" "Sigma_Commit_Crypto.Commitment_Schemes" "Berlekamp_Zassenhaus.Finite_Field_Factorization"
begin

text \<open>I formalize the Commitment to a Polynomial and show its correctness and soundness wrt. 
it's binding property. 
Sigma_Commit_Crypto.Commitment_Schemes gives the basis which outlines how commitment 
schemes are formalized in Isabelle. On top of this template I define the relevant functions and show 
the game-based proofs of interest, namely correctness and the binding property.\<close>

section \<open>Assumptions\<close>

subsection \<open>t-Strong Diffie Hellmann Assumption (t-SDH)\<close>

locale t_SDH = G : Cyclic_Group.cyclic_group G
for G (structure)
begin

(*type_synonym 'grp' t_SDH_adversary = "'grp' list \<Rightarrow> ('q mod_ring *'grp') spmf"*)
type_synonym 'grp adversary = "'grp list \<Rightarrow> (nat *'grp) spmf"


text \<open>TODO ändere to setup function\<close>
definition game :: "nat \<Rightarrow> 'a adversary \<Rightarrow> bool spmf" where 
  "game t \<A> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G);
    (c, g) \<leftarrow> \<A> (map (\<lambda>t'. \<^bold>g [^] (int \<alpha>^t')) [0..<t+1]);
    return_spmf (\<^bold>g [^] (1/((\<alpha>+c))) = g) 
  } ELSE return_spmf False"


definition advantage :: "nat \<Rightarrow> 'a adversary \<Rightarrow> real"
  where "advantage t \<A> = spmf (game t \<A>) True" \<comment>\<open>subtract Pr random (\<alpha>+c)\<close>

(* adapted proof from Sigma_Commit_Crypto.Commitment_Schemes bind_game_alt_def  *)
lemma game_alt_def:
  "game t \<A> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G);
    (c, g) \<leftarrow> \<A> (map (\<lambda>t'. \<^bold>g [^] (int \<alpha>^t')) [0..<t+1]);
    _::unit \<leftarrow> assert_spmf (\<^bold>g [^] (1/((\<alpha>+c))) = g);
    return_spmf (True) } ELSE return_spmf False"
  (is "?lhs = ?rhs")
proof -
   have "?lhs = TRY do {
      \<alpha> \<leftarrow> sample_uniform (order G);
      TRY do {
        (c, g) \<leftarrow> \<A> (map (\<lambda>t'. \<^bold>g [^] (int \<alpha>^t')) [0..<t+1]);
          TRY return_spmf (\<^bold>g [^] (1/((\<alpha>+c))) = g) ELSE return_spmf False
      } ELSE return_spmf False
    } ELSE return_spmf False"
    unfolding split_def game_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  also have "\<dots> = TRY do {
      \<alpha> \<leftarrow> sample_uniform (order G);
      TRY do {
        (c, g) \<leftarrow> \<A> (map (\<lambda>t'. \<^bold>g [^] (int \<alpha>^t')) [0..<t+1]);
          TRY do {
            _ :: unit \<leftarrow> assert_spmf (\<^bold>g [^] (1/((\<alpha>+c))) = g);
            return_spmf True
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

locale Poly_Commit_base =
  fixes G :: "'grp Cyclic_Group.cyclic_group" (structure)
  and t::nat
assumes prime_order: "prime (order G)"
and G_cyclic: "Cyclic_Group.cyclic_group G"
begin

type_synonym 'grp' ck = "'grp' list"
type_synonym 'grp' vk = "'grp' list"
type_synonym 'a plain = "'a mod_ring poly"
type_synonym 'grp' commit = "'grp'"
type_synonym 'a "opening" = "'a mod_ring poly"

definition key_gen :: "('grp ck \<times> 'grp vk) spmf"
where 
  "key_gen = do {
    \<alpha> :: nat \<leftarrow> sample_uniform (order G);
    let PK = map (\<lambda>t. \<^bold>g\<^bsub>G\<^esub> [^]\<^bsub>G\<^esub> (\<alpha>^t)) [0..<Suc t];
    return_spmf (PK, PK) 
  }" 

fun g_pow_ck_Prod :: "'grp list \<Rightarrow>'a::finite mod_ring poly \<Rightarrow> 'grp" where
  "g_pow_ck_Prod ck \<phi> = fold (\<lambda>i g. g \<otimes>\<^bsub>G\<^esub> ck!i [^]\<^bsub>G\<^esub> (to_int_mod_ring (poly.coeff \<phi> i))) [0..<Suc (degree \<phi>)] \<one>\<^bsub>G\<^esub>"

definition commit :: "'grp ck \<Rightarrow> 'a::finite plain \<Rightarrow> ('grp commit \<times> 'a opening) spmf"
where 
  "commit ck m = do {
    let com = g_pow_ck_Prod ck m in
    return_spmf (com,m) 
  }"

definition verify :: "'grp vk \<Rightarrow> 'a::finite plain \<Rightarrow> 'grp commit \<Rightarrow> 'a opening \<Rightarrow> bool"
where 
  "verify v_key m c d = (c = g_pow_ck_Prod v_key d \<and> m=d)"

definition valid_msg :: "'a::finite  plain \<Rightarrow> bool"
  where "valid_msg msg \<equiv> (degree msg < t)"

sublocale poly_commit: abstract_commitment key_gen commit verify valid_msg .

sublocale t_SDH_asm: t_SDH G
  unfolding t_SDH_def using G_cyclic .

end

section \<open>Commitment Proofs\<close>

locale Poly_Commit = Poly_Commit_base
begin

subsection \<open>Correctness\<close>

lemma correct:
  shows "spmf (poly_commit.correct_game m) True = 1" 
  apply(simp add: abstract_commitment.correct_game_def Let_def commit_def verify_def)
  apply (simp add: key_gen_def Let_def bind_spmf_const cong: bind_spmf_cong_simp)
  apply (simp add: t_SDH_asm.G.order_gt_0)

theorem abstract_correct:
  shows "poly_commit.correct (TYPE ('a'::finite))"
  unfolding abstract_commitment.correct_def using correct by blast
    
subsection \<open>Soundness wrt. binding (i.e. a commitment cannot (easily) be resolved to two different messages)\<close>



end

end