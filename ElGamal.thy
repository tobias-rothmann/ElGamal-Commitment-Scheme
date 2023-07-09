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
the game-based proofs of interest, namely correctness and the hiding and the binding propert.\<close>

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

locale ElGamal_Commit_base =
  fixes G :: "'grp Cyclic_Group.cyclic_group" (structure)
assumes prime_order: "prime (order G)"
and G_cyclic: "Cyclic_Group.cyclic_group G"
begin

type_synonym ck = "nat" (*s is Zp*)
type_synonym 'grp' vk = "'grp'"
type_synonym 'grp' plain = "'grp'"
type_synonym 'grp' commit = "'grp' *'grp' * 'grp'"
type_synonym 'grp' "opening" = "nat * nat * 'grp'" (*s and y is Zp*)

definition key_gen :: "(ck \<times> 'grp vk) spmf"
where 
  "key_gen = do {
    s :: nat \<leftarrow> sample_uniform (order G);
    return_spmf (s, \<^bold>g [^] s) 
  }" 

definition commit :: "ck \<Rightarrow> 'grp plain \<Rightarrow> ('grp commit \<times> 'grp opening) spmf"
where 
  "commit ck m = do {
    y :: nat \<leftarrow> sample_uniform (order G);
    return_spmf ((\<^bold>g [^] ck, \<^bold>g [^] y, m \<otimes> (\<^bold>g [^] (ck*y))), (ck,y,m)) 
  }"

definition verify :: "'grp vk \<Rightarrow> 'grp plain \<Rightarrow> 'grp commit \<Rightarrow> 'grp opening \<Rightarrow> bool"
where 
  "verify v_key m c d = (let (gps, gpy, mgpsy) = c;
    (s,y,m) = d
    in (\<^bold>g [^] s = gps \<and> \<^bold>g [^] y = gpy \<and> m \<otimes>  \<^bold>g [^] (s*y) = mgpsy)
)"

definition valid_msg :: "'grp plain \<Rightarrow> bool"
  where "valid_msg msg \<equiv> True"

sublocale elgamal_commit: abstract_commitment key_gen commit verify valid_msg .

sublocale t_SDH_asm: t_SDH G
  unfolding t_SDH_def using G_cyclic .

end

section \<open>Commitment Proofs\<close>

locale ElGamal_Commit = ElGamal_Commit_base + cyclic_group G
begin

subsection \<open>Correctness\<close>

lemma correct:
  shows "spmf (elgamal_commit.correct_game m) True = 1" 
  apply (simp add: abstract_commitment.correct_game_def commit_def verify_def key_gen_def)
  apply(simp add: Let_def bind_spmf_const lossless_weight_spmfD cong: bind_spmf_cong_simp)
  apply (simp add: t_SDH_asm.G.order_gt_0)
  done

theorem abstract_correct:
  shows "elgamal_commit.correct (TYPE ('a'::finite))"
  unfolding abstract_commitment.correct_def using correct by blast
    
subsection \<open>Soundness wrt. binding (i.e. a commitment cannot (easily) be resolved to two different messages)\<close>



end

end