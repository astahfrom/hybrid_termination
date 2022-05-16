theory Termination imports "Hybrid_Logic.Hybrid_Logic" Trees begin

(*
Inspired by:
Bolander, T., & Blackburn, P. (2007). Termination for Hybrid Tableaus.
Journal of Logic and Computation, 17(3), 517-554. https://doi.org/10.1093/logcom/exm014

*)

(* TODO: Maybe do B \<subseteq> nominals all labels? (still curious about this) *)

(* TODO: is it nicer if we use sets for the introduced formulas? *)

section \<open>Tableau\<close>

datatype ('a, 'b) tag
  = Close 'b \<open>('a, 'b) fm\<close>
  | Open
  | Block 'b
  | Rule 'b \<open>('a, 'b) fm list list\<close>
  | Fresh 'b \<open>('a, 'b) fm\<close> 'b

datatype ('a, 'b) step =
  Step (getTag: \<open>('a, 'b) tag\<close>) (getPotential: nat) (getBranch: \<open>('a, 'b) branch\<close>)

type_synonym ('a, 'b) tableau = \<open>('a, 'b) step tree\<close>

coinductive wft :: \<open>'b set \<Rightarrow> ('a, 'b) tableau \<Rightarrow> bool\<close>
  for A :: \<open>'b set\<close> where
    WfClose:
    \<open>p at i in branch \<Longrightarrow> (\<^bold>\<not> p) at i in branch \<Longrightarrow>
     wft A (Node (Step (Close i p) n branch) [])\<close>
  | WfOpen: (* TODO: Do I want to enforce that this is saturated? *)
    \<open>\<nexists>p i. p at i in branch \<and> (\<^bold>\<not> p) at i in branch \<Longrightarrow>
     wft A (Node (Step Open n branch) [])\<close>
  | WfNeg:
    \<open>(\<^bold>\<not> \<^bold>\<not> p) at a in (ps, a) # branch \<Longrightarrow>
    new p a ((ps, a) # branch) \<Longrightarrow>
    getBranch (getLabel s) = (p # ps, a) # branch \<Longrightarrow>
    getPotential (getLabel s) = Suc n \<Longrightarrow>
    wft A s \<Longrightarrow>
    wft A (Node (Step (Rule a [[p]]) n ((ps, a) # branch)) [s])\<close>
  | WfDisP:
    \<open>(p \<^bold>\<or> q) at a in (ps, a) # branch \<Longrightarrow>
     new p a ((ps, a) # branch) \<Longrightarrow> new q a ((ps, a) # branch) \<Longrightarrow>
     getBranch (getLabel sl) = (p # ps, a) # branch \<Longrightarrow> getPotential (getLabel sl) = Suc n \<Longrightarrow>
     getBranch (getLabel sr) = (q # ps, a) # branch \<Longrightarrow> getPotential (getLabel sr) = Suc n \<Longrightarrow>
     wft A sl \<Longrightarrow> wft A sr \<Longrightarrow>
     wft A (Node (Step (Rule a [[p], [q]]) n ((ps, a) # branch)) [sl, sr])\<close>
  | WfDisN:
    \<open>(\<^bold>\<not> (p \<^bold>\<or> q)) at a in (ps, a) # branch \<Longrightarrow>
     new (\<^bold>\<not> p) a ((ps, a) # branch) \<or> new (\<^bold>\<not> q) a ((ps, a) # branch) \<Longrightarrow>
     getBranch (getLabel s) = ((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, a) # branch \<Longrightarrow>
     getPotential (getLabel s) = Suc n \<Longrightarrow>
     wft A s \<Longrightarrow>
     intro = filter (\<lambda>p. new p a ((ps, a) # branch)) [\<^bold>\<not> q, \<^bold>\<not> p] \<Longrightarrow>
     wft A (Node (Step (Rule a [intro]) n ((ps, a) # branch)) [s])\<close>
  | WfDiaP:
    \<open>(\<^bold>\<diamond> p) at a in (ps, a) # branch \<Longrightarrow>
     i \<notin> A \<union> branch_nominals ((ps, a) # branch) \<Longrightarrow>
     \<nexists>a. p = Nom a \<Longrightarrow> \<not> witnessed p a ((ps, a) # branch) \<Longrightarrow>
     getBranch (getLabel s) = ((\<^bold>@ i p) # (\<^bold>\<diamond> Nom i) # ps, a) # branch \<Longrightarrow>
     getPotential (getLabel s) = Suc n \<Longrightarrow>
     wft A s \<Longrightarrow>
     wft A (Node (Step (Fresh a p i) n ((ps, a) # branch)) [s])\<close>
  | WfDiaN:
    \<open>(\<^bold>\<not> (\<^bold>\<diamond> p)) at a in (ps, a) # branch \<Longrightarrow>
     (\<^bold>\<diamond> Nom i) at a in (ps, a) # branch \<Longrightarrow>
     new (\<^bold>\<not> (\<^bold>@ i p)) a ((ps, a) # branch) \<Longrightarrow>
     getBranch (getLabel s) = ((\<^bold>\<not> (\<^bold>@ i p)) # ps, a) # branch \<Longrightarrow>
     getPotential (getLabel s) = Suc n \<Longrightarrow>
     wft A s \<Longrightarrow>
     wft A (Node (Step (Rule a [[\<^bold>\<not> (\<^bold>@ i p)]]) n ((ps, a) # branch)) [s])\<close>
  | WfSatP:
    \<open>(\<^bold>@ a p) at b in (ps, a) # branch \<Longrightarrow>
     new p a ((ps, a) # branch) \<Longrightarrow>
     getBranch (getLabel s) = (p # ps, a) # branch \<Longrightarrow> getPotential (getLabel s) = Suc n \<Longrightarrow>
     wft A s \<Longrightarrow>
     wft A (Node (Step (Rule a [[p]]) n ((ps, a) # branch)) [s])\<close>
  | WfSatN:
    \<open>(\<^bold>\<not> (\<^bold>@ a p)) at b in (ps, a) # branch \<Longrightarrow>
     new (\<^bold>\<not> p) a ((ps, a) # branch) \<Longrightarrow>
     getBranch (getLabel s) = ((\<^bold>\<not> p) # ps, a) # branch \<Longrightarrow> getPotential (getLabel s) = Suc n \<Longrightarrow>
     wft A s \<Longrightarrow>
     wft A (Node (Step (Rule a [[\<^bold>\<not> p]]) n ((ps, a) # branch)) [s])\<close>
  | WfGoTo:
    \<open>i \<in> branch_nominals branch \<Longrightarrow>
     getBranch (getLabel s) = ([], i) # branch \<Longrightarrow> getPotential (getLabel s) = n \<Longrightarrow>
     wft A s \<Longrightarrow>
     wft A (Node (Step (Block i) (Suc n) branch) [s])\<close>
  | WfNom:
    \<open>p at b in (ps, a) # branch \<Longrightarrow> Nom a at b in (ps, a) # branch \<Longrightarrow>
     \<forall>i. p = Nom i \<or> p = (\<^bold>\<diamond> Nom i) \<longrightarrow> i \<in> A \<Longrightarrow>
     new p a ((ps, a) # branch) \<Longrightarrow>
     getBranch (getLabel s) = (p # ps, a) # branch \<Longrightarrow> getPotential (getLabel s) = Suc n \<Longrightarrow>
     wft A s \<Longrightarrow>
     wft A (Node (Step (Rule a [[p]]) n ((ps, a) # branch)) [s])\<close>

lemma example:
  \<open>wft A (Node (Step (Rule a [[Pro ''p'']]) 0 [([\<^bold>\<not> \<^bold>\<not> Pro ''p'', Pro ''q'', \<^bold>\<not> Pro ''p''], a)])
  [Node (Step (Close a (Pro ''p'')) 1
    [([Pro ''p'', \<^bold>\<not> \<^bold>\<not> Pro ''p'', Pro ''q'', \<^bold>\<not> Pro ''p''], a)]) []])\<close>
proof -
  have \<open>wft A (Node (Step (Close a (Pro ''p'')) 1
      [([Pro ''p'', \<^bold>\<not> \<^bold>\<not> Pro ''p'', Pro ''q'', \<^bold>\<not> Pro ''p''], a)]) [])\<close>
    using WfClose[where p=\<open>Pro ''p''\<close> and i=a] by simp
  then show ?thesis
    using WfNeg[where p=\<open>Pro ''p''\<close> and a=a] unfolding new_def by simp
qed

section \<open>Soundness\<close>

lemma fin_no_open_sound:
  assumes \<open>fin tab\<close> \<open>wft A tab\<close> \<open>alwt (holdst (\<lambda>step. getTag step \<noteq> Open)) tab\<close>
  shows \<open>A, getPotential (getLabel tab) \<turnstile> getBranch (getLabel tab)\<close>
  using assms
proof (induct tab rule: fin.induct)
  case (Fin subs l)
  from this(3) show ?case
  proof cases
    case AlwT
    with Fin(2, 1) show ?thesis
      by cases (simp_all add: STA.intros)
  qed
qed

lemma fin_no_open_sound_labels:
  assumes \<open>fin tab\<close> \<open>wft A tab\<close> \<open>\<forall>l \<in> labels tab. getTag l \<noteq> Open\<close>
  shows \<open>A, getPotential (getLabel tab) \<turnstile> getBranch (getLabel tab)\<close>
  using assms fin_no_open_sound labels_alwt_holdst by blast

section \<open>LTL\<close>

lemma alwt_wft: \<open>alwt (wft A impl nxtt (wft A)) tab\<close>
  by (coinduction arbitrary: tab) (auto elim: wft.cases)

lemma wft_alwt:
  assumes \<open>wft A tab\<close> \<open>\<And>t. wft A t \<Longrightarrow> P t\<close>
  shows \<open>alwt P tab\<close>
  using assms by (coinduction arbitrary: tab) (auto elim: wft.cases)

lemma wft_alwt_impl:
  assumes \<open>wft A tab\<close> \<open>\<And>t. wft A t \<Longrightarrow> P t \<Longrightarrow> Q t\<close>
  shows \<open>alwt (P impl Q) tab\<close>
  using assms by (coinduction arbitrary: tab) (auto elim: wft.cases)

lemma wft_ipath:
  assumes \<open>wft A t\<close> \<open>ipath t s\<close>
  shows \<open>\<exists>t. wft A t \<and> ipath t (stl s)\<close>
  using assms
proof cases
  case (WfClose p i branch n)
  then show ?thesis
    using assms(2) by (auto elim: ipath.cases)
next
  case (WfOpen branch n)
  then show ?thesis
    using assms(2) by (auto elim: ipath.cases)
next
  case (WfNeg p a ps branch s n)
  from this(1, 6) show ?thesis
    using assms(2) ipath.cases by fastforce
next
  case (WfDisP p q a ps branch sl n sr)
  from this(1, 9-10) show ?thesis
    using assms(2) ipath.cases by fastforce
next
  case (WfDisN p q a ps branch s n intro)
  from this(1, 6) show ?thesis
    using assms(2) ipath.cases by fastforce
next
  case (WfDiaP p a ps branch i s n)
  from this(1, 8) show ?thesis
    using assms(2) ipath.cases by fastforce
next
  case (WfDiaN p a ps branch i s n)
  from this(1, 7) show ?thesis
    using assms(2) ipath.cases by fastforce
next
  case (WfSatP a p b ps branch s n)
  from this(1, 6) show ?thesis
    using assms(2) ipath.cases by fastforce
next
  case (WfSatN a p b ps branch s n)
  from this(1, 6) show ?thesis
    using assms(2) ipath.cases by fastforce
next
  case (WfGoTo i branch s n)
  from this(1, 5) show ?thesis
    using assms(2) ipath.cases by fastforce
next
  case (WfNom p b ps a branch s n)
  from this(1, 8) show ?thesis
    using assms(2) ipath.cases by fastforce
qed

lemma wft_alw:
  assumes \<open>wft A t\<close>  \<open>ipath t s\<close> \<open>\<And>t. wft A t \<Longrightarrow> relt r t\<close>
  shows \<open>alw (rels r) s\<close>
  using assms
proof (coinduction arbitrary: s t)
  case alw
  then have ?case if \<open>rels r s\<close> \<open>\<exists>t. wft A t \<and> ipath t (stl s)\<close>
    using that by simp
  moreover from alw have \<open>rels r s\<close>
    using relt_ipath by fast
  moreover have \<open>\<exists>t. wft A t \<and> ipath t (stl s)\<close>
    using alw wft_ipath by fast
  ultimately show ?case .
qed

lemma alwt_aand:
  assumes \<open>alwt P t\<close> \<open>alwt Q t\<close>
  shows \<open>alwt (P aand Q) t\<close>
  using assms by (coinduction arbitrary: t) (auto elim: alwt.cases)

lemma alwt_nxtt:
  assumes \<open>alwt P t\<close> \<open>\<And>t. P t \<Longrightarrow> Q t \<Longrightarrow> nxtt Q t\<close> \<open>Q t\<close>
  shows \<open>alwt Q t\<close>
  using assms by (coinduction arbitrary: t) (auto elim: alwt.cases)

lemma holds_holdst:
  assumes \<open>ipath t s\<close> \<open>holdst P t\<close>
  shows \<open>holds P s\<close>
  using assms by (auto elim: ipath.cases)

(* TODO: unused *)
lemma alw_impl:
  assumes \<open>alw (P impl Q) s\<close> \<open>P (sdrop k s)\<close>
  shows \<open>Q (sdrop k s)\<close>
  using assms by (simp add: alw_iff_sdrop)

lemma alwt_aand_E1: \<open>alwt (P aand Q) t \<Longrightarrow> alwt P t\<close>
  by (coinduction arbitrary: t) (auto elim: alwt.cases)

lemma alwt_aand_E2: \<open>alwt (P aand Q) t \<Longrightarrow> alwt Q t\<close>
  by (coinduction arbitrary: t) (auto elim: alwt.cases)

lemma wft_ipath_sdrop:
  assumes \<open>wft A tab\<close> \<open>ipath tab steps\<close>
  shows \<open>\<exists>tab. wft A tab \<and> ipath tab (sdrop n steps)\<close>
  using assms
proof (induct n)
  case (Suc n)
  then show ?case
    using wft_ipath by fastforce
qed auto

section \<open>Preservation\<close>

lemma preservation_Next:
  assumes \<open>wft A tab\<close>
  shows \<open>relt (Impl (\<lambda>l. p at a in getBranch l) (Next (Here (\<lambda>l. p at a in getBranch l)))) tab\<close>
  using assms
proof cases
  case (WfDisP p q a ps branch sl n sr)
  from this(1, 5, 7) show ?thesis
    by fastforce
next
  case (WfDisN p q a ps branch s n intro)
  from this(1, 4) show ?thesis
    by fastforce
next
  case (WfDiaN p a ps branch i s n)
  from this(1, 5) show ?thesis
    by fastforce
next
  case (WfNom p b ps a branch s n)
  from this(1, 6) show ?thesis
    by fastforce
qed fastforce+

lemma preservation_alw:
  assumes \<open>wft A tab\<close> \<open>ipath tab steps\<close>
  shows \<open>alw (holds (\<lambda>l. p at a in getBranch l)
   impl (nxt (holds (\<lambda>l. p at a in getBranch l)))) steps\<close>
proof -
  have \<open>alw (rels (Impl (\<lambda>l. p at a in getBranch l)
      (Next (Here (\<lambda>l. p at a in getBranch l))))) steps\<close>
    using wft_alw assms preservation_Next .
  then show ?thesis
    by simp
qed

(* TODO: is this nice to have on top? *)
lemma preservation_invar:
  assumes \<open>wft A tab\<close> \<open>ipath tab steps\<close> \<open>holds (\<lambda>l. p at a in getBranch l) steps\<close>
  shows \<open>alw (holds (\<lambda>l. p at a in getBranch l)) steps\<close>
proof -
  have \<open>alw (holds (\<lambda>l. p at a in getBranch l)
  impl (nxt (holds (\<lambda>l. p at a in getBranch l)))) steps\<close>
    using assms preservation_alw by fast
  then show ?thesis
    using alw_invar assms(3) by blast
qed

section \<open>Nominals\<close>

(* TODO: think about this. It's not local since it uses labels *)
subsection \<open>Generated\<close>

fun generates :: \<open>('a, 'b) tag \<Rightarrow> 'b set\<close> where
  \<open>generates (Fresh _  _ b) = {b}\<close>
| \<open>generates _ = {}\<close>

definition generated :: \<open>('a, 'b) tableau \<Rightarrow> 'b set\<close> where
  \<open>generated tab \<equiv> \<Union>step \<in> labels tab. generates (getTag step)\<close>

definition generated_ipath :: \<open>('a, 'b) step stream \<Rightarrow> 'b set\<close> where
  \<open>generated_ipath steps \<equiv> \<Union>step \<in> sset steps. generates (getTag step)\<close>

lemma nxtt_generated:
  assumes \<open>wft A tab\<close> \<open>generated tab \<subseteq> B\<close>
  shows \<open>nxtt (\<lambda>t. generated t \<subseteq> B) tab\<close>
  using assms unfolding generated_def
  by (fastforce elim: wft.cases)

lemma alwt_generated:
  assumes \<open>wft A tab\<close>
  shows \<open>alwt ((\<lambda>t. generated t \<subseteq> B) impl nxtt (\<lambda>t. generated t \<subseteq> B)) tab\<close>
  using wft_alwt_impl assms nxtt_generated .

lemma wft_generated_nxtt:
  assumes \<open>wft A tab\<close> \<open>generated tab \<subseteq> B\<close>
    \<open>holdst (\<lambda>t. \<forall>i \<in> branch_nominals (getBranch t). i \<in> orig \<or> i \<in> B) tab\<close>
  shows \<open>nxtt (holdst (\<lambda>s. \<forall>i \<in> branch_nominals (getBranch s). i \<in> orig \<or> i \<in> B)) tab\<close>
  using assms
proof cases
  case (WfNeg p a ps branch s n)
  moreover from this(2) have
    \<open>branch_nominals ((p # ps, a) # branch) \<subseteq> branch_nominals ((ps, a) # branch)\<close>
    using WfNeg(2) unfolding branch_nominals_def by fastforce
  ultimately show ?thesis
    using assms(3) by auto
next
  case (WfDisP p q a ps branch sl n sr)
  moreover from this(2) have
    \<open>branch_nominals ((p # ps, a) # branch) \<subseteq> branch_nominals ((ps, a) # branch)\<close>
    \<open>branch_nominals ((q # ps, a) # branch) \<subseteq> branch_nominals ((ps, a) # branch)\<close>
    unfolding branch_nominals_def by fastforce+
  ultimately show ?thesis
    using assms(3) by auto
next
  case (WfDisN p q a ps branch s n intro)
  moreover from this(2) have
    \<open>branch_nominals (((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, a) # branch) \<subseteq> branch_nominals ((ps, a) # branch)\<close>
    unfolding branch_nominals_def by fastforce
  ultimately show ?thesis
    using assms(3) by auto
next
  case (WfDiaP p a ps branch i s n)
  have \<open>branch_nominals (((\<^bold>@ i p) # (\<^bold>\<diamond> Nom i) # ps, a) # branch) =
          {i} \<union> nominals p \<union> branch_nominals ((ps, a) # branch)\<close>
    unfolding branch_nominals_def by auto
  moreover have \<open>nominals p \<subseteq> branch_nominals ((ps, a) # branch)\<close>
    using WfDiaP(2) unfolding branch_nominals_def by fastforce
  then have \<open>\<forall>i \<in> nominals p. i \<in> orig \<or> i \<in> B\<close>
    using WfDiaP(1) assms(3) by auto
  ultimately have ?thesis if \<open>i \<in> B\<close>
    using that WfDiaP(1, 6) assms(3) by auto
  moreover have \<open>i \<in> B\<close>
    using WfDiaP(1) assms(2) unfolding generated_def by simp
  ultimately show ?thesis
    using WfDiaP(1, 8) by fastforce
next
  case (WfDiaN p a ps branch i s n)
  moreover have \<open>nominals (\<^bold>\<not> (\<^bold>@ i p)) \<subseteq> branch_nominals ((ps, a) # branch)\<close>
    using WfDiaN(2-3) unfolding branch_nominals_def by fastforce
  then have
    \<open>branch_nominals (((\<^bold>\<not> (\<^bold>@ i p)) # ps, a) # branch) \<subseteq> branch_nominals ((ps, a) # branch)\<close>
    using WfDiaN(2) unfolding branch_nominals_def by auto
  ultimately show ?thesis
    using assms(3) unfolding generated_def by auto
next
  case (WfSatP a p b ps branch s n)
  moreover have \<open>branch_nominals ((p # ps, a) # branch) \<subseteq> branch_nominals ((ps, a) # branch)\<close>
    using WfSatP(2) unfolding branch_nominals_def by fastforce
  ultimately show ?thesis
    using assms(3) unfolding generated_def by auto
next
  case (WfSatN a p b ps branch s n)
  moreover have \<open>branch_nominals (((\<^bold>\<not> p) # ps, a) # branch) \<subseteq> branch_nominals ((ps, a) # branch)\<close>
    using WfSatN(2) unfolding branch_nominals_def by fastforce
  ultimately show ?thesis
    using assms(3) unfolding generated_def by auto
next
  case (WfGoTo i branch s n)
  moreover have \<open>branch_nominals (([], i) # branch) \<subseteq> branch_nominals branch\<close>
    using WfGoTo(2) unfolding branch_nominals_def by simp
  ultimately show ?thesis
    using assms(3) unfolding generated_def by auto
next
  case (WfNom p b ps a branch s n)
  moreover have \<open>branch_nominals ((p # ps, a) # branch) \<subseteq> branch_nominals ((ps, a) # branch)\<close>
    using WfNom(2) unfolding branch_nominals_def by fastforce
  ultimately show ?thesis
    using assms(3) unfolding generated_def by (simp add: in_mono)
qed simp_all

lemma wft_generated':
  assumes \<open>wft A tab\<close> \<open>generated tab \<subseteq> B\<close>
    \<open>holdst (\<lambda>t. \<forall>i \<in> branch_nominals (getBranch t). i \<in> orig \<or> i \<in> B) tab\<close>
  shows \<open>alwt (holdst (\<lambda>step. \<forall>i \<in> branch_nominals (getBranch step). i \<in> orig \<or> i \<in> B)) tab\<close>
proof -
  have \<open>alwt (wft A) tab\<close>
    using assms(1) wft_alwt by blast
  moreover have \<open>alwt (\<lambda>t. generated t \<subseteq> B) tab\<close>
    using alwt_impl_nxtt alwt_generated assms(1-2) .
  ultimately have \<open>alwt (wft A aand (\<lambda>t. generated t \<subseteq> B)) tab\<close>
    using alwt_aand by blast
  with alwt_nxtt[where Q=\<open>holdst (\<lambda>t. \<forall>i \<in> branch_nominals (getBranch t). i \<in> orig \<or> i \<in> B)\<close>]
  show ?thesis
    using wft_generated_nxtt assms(3) by blast
qed

lemma wft_generated:
  assumes \<open>wft A tab\<close>
  shows \<open>alwt (holdst (\<lambda>step. \<forall>i \<in> branch_nominals (getBranch step).
    i \<in> branch_nominals (getBranch (getLabel tab)) \<or> i \<in> generated tab)) tab\<close>
  using assms wft_generated' by blast

lemma wft_generated_ipath':
  assumes \<open>ipath tab steps\<close> \<open>wft A tab\<close> \<open>generated_ipath steps \<subseteq> B\<close>
    \<open>holds (\<lambda>l. branch_nominals (getBranch l) \<subseteq> orig \<union> B) steps\<close>
  shows \<open>alw (holds (\<lambda>l. branch_nominals (getBranch l) \<subseteq> orig \<union> B)) steps\<close>
  using assms
proof (coinduction arbitrary: tab steps)
  case alw
  then show ?case
  proof cases
    case (IPath s' subs tail l)
    then have wft: \<open>wft A s'\<close>
      using alw(2) by (auto elim: wft.cases)

    with alw(2) show ?thesis
    proof cases
      case (WfClose p i branch n)
      then show ?thesis
        using IPath by simp
    next
      case (WfOpen branch n)
      then show ?thesis
        using IPath by simp
    next
      case (WfNeg p a ps branch s n)
      from this(1) have ?thesis if \<open>branch_nominals (getBranch (getLabel s)) \<subseteq> orig \<union> B\<close>
        using that wft IPath alw(3-) holds_holdst unfolding generated_ipath_def by fastforce
      moreover have \<open>nominals p \<subseteq> orig \<union> B\<close>
        using WfNeg(1-2) IPath alw(4) unfolding branch_nominals_def by fastforce
      then have \<open>branch_nominals (getBranch (getLabel s)) \<subseteq> orig \<union> B\<close>
        using WfNeg(1, 4) IPath alw(4) unfolding branch_nominals_def by simp
      ultimately show ?thesis
        by simp
    next
      case (WfDisP p q a ps branch sl n sr)
      have ?thesis if
        \<open>branch_nominals (getBranch (getLabel s')) \<subseteq> orig \<union> B\<close>
        using that wft IPath alw(3-) holds_holdst unfolding generated_ipath_def by fastforce
      moreover have \<open>s' = sl \<or> s' = sr\<close>
        using WfDisP(1) IPath by simp
      moreover have \<open>nominals p \<subseteq> orig \<union> B\<close> \<open>nominals q \<subseteq> orig \<union> B\<close>
        using WfDisP(1-2) IPath alw(4) unfolding branch_nominals_def by fastforce+
      then have
        \<open>branch_nominals (getBranch (getLabel sl)) \<subseteq> orig \<union> B\<close>
        \<open>branch_nominals (getBranch (getLabel sr)) \<subseteq> orig \<union> B\<close>
        using WfDisP(1, 5, 7) IPath alw(4) unfolding branch_nominals_def by simp_all
      ultimately show ?thesis
        by blast
    next
      case (WfDisN p q a ps branch s n intro)
      from this(1) have ?thesis if \<open>branch_nominals (getBranch (getLabel s)) \<subseteq> orig \<union> B\<close>
        using that wft IPath alw(3-) holds_holdst unfolding generated_ipath_def by fastforce
      moreover have \<open>nominals p \<subseteq> orig \<union> B\<close> \<open>nominals q \<subseteq> orig \<union> B\<close>
        using WfDisN(1-2) IPath alw(4) unfolding branch_nominals_def by fastforce+
      then have \<open>branch_nominals (getBranch (getLabel s)) \<subseteq> orig \<union> B\<close>
        using WfDisN(1, 4) IPath alw(4) unfolding branch_nominals_def by simp
      ultimately show ?thesis
        by simp
    next
      case (WfDiaP p a ps branch i s n)
      from this(1) have ?thesis if \<open>branch_nominals (getBranch (getLabel s)) \<subseteq> orig \<union> B\<close>
        using that wft IPath alw(3-) holds_holdst unfolding generated_ipath_def by fastforce
      moreover {
        have \<open>nominals p \<subseteq> orig \<union> B\<close>
          using WfDiaP(1-2) IPath alw(4) unfolding branch_nominals_def by fastforce
        moreover have \<open>i \<in> B\<close>
          using WfDiaP(1) IPath alw(3) unfolding generated_ipath_def by simp
        ultimately have \<open>branch_nominals (getBranch (getLabel s)) \<subseteq> orig \<union> B\<close>
          using WfDiaP(1, 6) IPath alw(4) unfolding branch_nominals_def by simp
      }
      ultimately show ?thesis
        by simp
    next
      case (WfDiaN p a ps branch i s n)
      from this(1) have ?thesis if \<open>branch_nominals (getBranch (getLabel s)) \<subseteq> orig \<union> B\<close>
        using that wft IPath alw(3-) holds_holdst unfolding generated_ipath_def by fastforce
      moreover {
        have \<open>nominals p \<subseteq> orig \<union> B\<close>
          using WfDiaN(1-2) IPath alw(4) unfolding branch_nominals_def by fastforce
        moreover have \<open>i \<in> orig \<union> B\<close>
          using WfDiaN(1, 3) IPath alw(4) unfolding branch_nominals_def by fastforce
        ultimately have \<open>branch_nominals (getBranch (getLabel s)) \<subseteq> orig \<union> B\<close>
          using WfDiaN(1, 5) IPath alw(4) unfolding branch_nominals_def by simp
      }
      ultimately show ?thesis
        by simp
    next
      case (WfSatP a p b ps branch s n)
      from this(1) have ?thesis if \<open>branch_nominals (getBranch (getLabel s)) \<subseteq> orig \<union> B\<close>
        using that wft IPath alw(3-) holds_holdst unfolding generated_ipath_def by fastforce
      moreover have \<open>nominals p \<subseteq> orig \<union> B\<close>
        using WfSatP(1-2) IPath alw(4) unfolding branch_nominals_def by force
      then have \<open>branch_nominals (getBranch (getLabel s)) \<subseteq> orig \<union> B\<close>
        using WfSatP(1, 4) IPath alw(4) unfolding branch_nominals_def by simp
      ultimately show ?thesis
        by simp
    next
      case (WfSatN a p b ps branch s n)
      from this(1) have ?thesis if \<open>branch_nominals (getBranch (getLabel s)) \<subseteq> orig \<union> B\<close>
        using that wft IPath alw(3-) holds_holdst unfolding generated_ipath_def by fastforce
      moreover have \<open>nominals p \<subseteq> orig \<union> B\<close>
        using WfSatN(1-2) IPath alw(4) unfolding branch_nominals_def by force
      then have \<open>branch_nominals (getBranch (getLabel s)) \<subseteq> orig \<union> B\<close>
        using WfSatN(1, 4) IPath alw(4) unfolding branch_nominals_def by simp
      ultimately show ?thesis
        by simp
    next
      case (WfGoTo i branch s n)
      from this(1) have ?thesis if \<open>branch_nominals (getBranch (getLabel s)) \<subseteq> orig \<union> B\<close>
        using that wft IPath alw(3-) holds_holdst unfolding generated_ipath_def by fastforce
      moreover have \<open>i \<in> orig \<union> B\<close>
        using WfGoTo(1-2) IPath alw(4) unfolding branch_nominals_def by auto
      then have \<open>branch_nominals (getBranch (getLabel s)) \<subseteq> orig \<union> B\<close>
        using WfGoTo(1, 3) IPath alw(4) unfolding branch_nominals_def by simp
      ultimately show ?thesis
        by simp
    next
      case (WfNom p b ps a branch s n)
      from this(1) have ?thesis if \<open>branch_nominals (getBranch (getLabel s)) \<subseteq> orig \<union> B\<close>
        using that wft IPath alw(3-) holds_holdst unfolding generated_ipath_def by fastforce
      moreover have \<open>nominals p \<subseteq> orig \<union> B\<close>
        using WfNom(1-2) IPath alw(4) unfolding branch_nominals_def by fastforce
      then have \<open>branch_nominals (getBranch (getLabel s)) \<subseteq> orig \<union> B\<close>
        using WfNom(1, 6) IPath alw(4) unfolding branch_nominals_def by simp
      ultimately show ?thesis
        by simp
    qed
  qed
qed

lemma wft_generated_ipath:
  assumes \<open>ipath tab steps\<close> \<open>wft A tab\<close>
  shows \<open>alw (holds (\<lambda>l. branch_nominals (getBranch l) \<subseteq>
      branch_nominals (getBranch (shd steps)) \<union> generated_ipath steps)) steps\<close>
  using assms wft_generated_ipath' by fastforce

lemma wft_generated_labels:
  assumes \<open>wft A tab\<close> \<open>step \<in> labels tab\<close> \<open>i \<in> branch_nominals (getBranch step)\<close>
  shows \<open>i \<in> branch_nominals (getBranch (getLabel tab)) \<or> i \<in> generated tab\<close>
  using assms wft_generated alwt_holdst_labels by fast

section \<open>Quasi subformulas\<close>

subsection \<open>Quasis\<close>

fun quasis :: \<open>'b set \<Rightarrow> ('a, 'b) fm \<Rightarrow> ('a, 'b) fm set\<close> where
  \<open>quasis A (\<^bold>\<not> \<^bold>\<not> p) = {p} \<union> quasis A p\<close>
| \<open>quasis A (p \<^bold>\<or> q) = {p, q} \<union> quasis A p \<union> quasis A q\<close>
| \<open>quasis A (\<^bold>\<not> (p \<^bold>\<or> q)) = {\<^bold>\<not> p, \<^bold>\<not> q} \<union> quasis A (\<^bold>\<not> p) \<union> quasis A (\<^bold>\<not> q)\<close>
| \<open>quasis A (\<^bold>\<diamond> p) = (if \<exists>a. p = Nom a then {} else {\<^bold>@ i p |i. i \<in> A} \<union> {p} \<union> quasis A p)\<close>
| \<open>quasis A (\<^bold>\<not> (\<^bold>\<diamond> p)) = {\<^bold>\<not> (\<^bold>@ i p) |i. i \<in> A} \<union> {\<^bold>\<not> p} \<union> quasis A (\<^bold>\<not> p)\<close>
| \<open>quasis A (\<^bold>@ i p) = {p} \<union> quasis A p\<close>
| \<open>quasis A (\<^bold>\<not> (\<^bold>@ i p)) = {\<^bold>\<not> p} \<union> quasis A (\<^bold>\<not> p)\<close>
| \<open>quasis _ p = {p}\<close>

lemma quasis_subset_closed: \<open>p' \<in> quasis A p \<Longrightarrow> quasis A p' \<subseteq> quasis A p\<close>
  by (induct p rule: quasis.induct) (auto split: if_splits)

lemma finite_quasis: \<open>finite A \<Longrightarrow> finite (quasis A p)\<close>
  by (induct p rule: quasis.induct) auto

definition branch_formulas :: \<open>('a, 'b) branch \<Rightarrow> ('a, 'b) fm set\<close> where
  \<open>branch_formulas branch \<equiv> \<Union>(ps, i) \<in> set branch. {Nom i} \<union> set ps\<close>

lemma finite_branch_formulas: \<open>finite (branch_formulas branch)\<close>
  unfolding branch_formulas_def by auto

definition formula_bound :: \<open>'b set \<Rightarrow> ('a, 'b) branch \<Rightarrow> ('a, 'b) fm set\<close> where
  \<open>formula_bound B branch \<equiv>
    branch_formulas branch \<union>
    (\<Union>p \<in> branch_formulas branch. quasis B p) \<union>
    (\<Union>i \<in> B. {Nom i, \<^bold>\<diamond> Nom i})\<close>

lemma finite_formula_bound: \<open>finite B \<Longrightarrow> finite (formula_bound B branch)\<close>
  unfolding formula_bound_def using finite_branch_formulas finite_quasis by auto

lemma formula_bound_quasis: \<open>\<forall>p \<in> formula_bound B branch. quasis B p \<subseteq> formula_bound B branch\<close>
  unfolding formula_bound_def using quasis_subset_closed by fastforce

(* TODO: may not need rest of section *)

lemma branch_formulas_Cons [simp]:
  \<open>branch_formulas ((p # ps, a) # branch) = {p} \<union> branch_formulas ((ps, a) # branch)\<close>
  unfolding branch_formulas_def by simp

lemma at_in_branch_formulas: \<open>p at a in branch \<Longrightarrow> p \<in> branch_formulas branch\<close>
  unfolding branch_formulas_def by auto

lemma branch_nominals_there:
  assumes \<open>p' at b in ((ps, a) # branch)\<close> \<open>nominals p \<subseteq> nominals p'\<close>
    \<open>branch_nominals ((ps, a) # branch) \<subseteq> B\<close>
  shows \<open>branch_nominals ((p # ps, a) # branch) \<subseteq> B\<close>
proof -
  have \<open>nominals p \<subseteq> branch_nominals ((ps, a) # branch)\<close>
    using assms(1-2) unfolding branch_nominals_def by fastforce
  then have \<open>nominals p \<subseteq> B\<close>
    using assms(3) by simp
  then show ?thesis
    using assms(3) unfolding branch_nominals_def by simp
qed

lemma branch_nominals_Cons [simp]:
  \<open>branch_nominals ((p # ps, a) # branch) = nominals p \<union> branch_nominals ((ps, a) # branch)\<close>
  unfolding branch_nominals_def by auto

section \<open>Finite Intro Rules\<close>

fun introduces :: \<open>('a, 'b) tag \<Rightarrow> (('a, 'b) fm list list \<times> 'b) option\<close> where
  \<open>introduces (Rule a ps) = Some (ps, a)\<close>
| \<open>introduces (Fresh a p i) = Some ([[\<^bold>@ i p, \<^bold>\<diamond> Nom i]], a)\<close>
| \<open>introduces _ = None\<close>

subsection \<open>Distinct\<close>

lemma introduces_new:
  assumes \<open>wft A tab\<close>
  shows \<open>relt (Here (\<lambda>t. \<forall>pps a. introduces (getTag t) = Some (pps, a) \<longrightarrow>
      (\<forall>ps \<in> set pps. \<forall>p \<in> set ps. new p a (getBranch t)))) tab\<close>
  using assms
proof cases
  case (WfDiaP p a ps branch i s n)
  from this(1, 3) show ?thesis
    unfolding branch_nominals_def new_def by fastforce
qed auto

lemma introduces_new_ipath:
  assumes \<open>wft A tab\<close> \<open>ipath tab steps\<close>
  shows \<open>alw (holds (\<lambda>t. \<forall>pps a. introduces (getTag t) = Some (pps, a) \<longrightarrow>
      (\<forall>ps \<in> set pps. \<forall>p \<in> set ps. new p a (getBranch t)))) steps\<close>
proof -
  have \<open>alw (rels (Here (\<lambda>t. \<forall>pps a. introduces (getTag t) = Some (pps, a) \<longrightarrow>
      (\<forall>ps \<in> set pps. \<forall>p \<in> set ps. new p a (getBranch t))))) steps\<close>
  using wft_alw assms introduces_new .
  then show ?thesis
    by simp
qed

lemma introduces_Next:
  assumes \<open>wft A tab\<close>
  shows \<open>relt (Impl (\<lambda>t. introduces (getTag t) = Some (pps, a))
      (Next (Here (\<lambda>s. \<exists>ps \<in> set pps. ps \<noteq> [] \<and> (\<forall>p \<in> set ps. p at a in getBranch s))))) tab\<close>
  using assms
proof cases
  case (WfDisP p q a ps branch sl n sr)
  then show ?thesis
    by force
next
  case (WfNom p b ps a branch s n)
  from this(1, 6) show ?thesis
    by fastforce
qed fastforce+

lemma introduces_alw_nxt:
  assumes \<open>wft A tab\<close> \<open>ipath tab steps\<close>
  shows \<open>alw (holds (\<lambda>t. introduces (getTag t) = Some (pps, a))
   impl (nxt (holds (\<lambda>s. \<exists>ps \<in> set pps. ps \<noteq> [] \<and> (\<forall>p \<in> set ps. p at a in getBranch s))))) steps\<close>
proof -
  have \<open>alw (rels (Impl (\<lambda>t. introduces (getTag t) = Some (pps, a))
      (Next (Here (\<lambda>s. \<exists>ps \<in> set pps. ps \<noteq> [] \<and> (\<forall>p \<in> set ps. p at a in getBranch s)))))) steps\<close>
    using wft_alw assms introduces_Next .
  then show ?thesis
    by simp
qed

(* TODO: preservation-invar requires finding a tab in ipath tab (sdrop m steps)
  [2021-06-10: I don't know what this means anymore]
*)

lemma distinct_introduces:
  assumes \<open>wft A tab\<close> \<open>ipath tab steps\<close> \<open>steps !! m = s\<close> \<open>steps !! n = s'\<close> \<open>m < n\<close>
    \<open>introduces (getTag s) = Some (pps, a)\<close> \<open>introduces (getTag s') = Some (qqs, b)\<close>
  shows \<open>(pps, a) \<noteq> (qqs, b)\<close>
proof
  assume \<open>(pps, a) = (qqs, b)\<close>

  have \<open>alw (holds (\<lambda>t. introduces (getTag t) = Some (pps, a))
   impl nxt (holds (\<lambda>s. \<exists>ps\<in>set pps. ps \<noteq> [] \<and> (\<forall>p \<in> set ps. p at a in getBranch s)))) steps\<close>
    using introduces_alw_nxt assms(1-2) .
  then have \<open>holds (\<lambda>s. \<exists>ps\<in>set pps. ps \<noteq> [] \<and>
      (\<forall>p \<in> set ps. p at a in getBranch s)) (sdrop (Suc m) steps)\<close>
    using assms(3, 6) by (simp add: alw_iff_sdrop)
  then obtain ps where
    \<open>ps \<in>. pps\<close>
    \<open>ps \<noteq> []\<close>
    \<open>\<forall>p \<in> set ps. holds (\<lambda>s. p at a in getBranch s) (sdrop (Suc m) steps)\<close>
    by auto
  moreover have \<open>alw (holds (\<lambda>l. p at a in getBranch l)
            impl nxt (holds (\<lambda>l. p at a in getBranch l))) steps\<close> for p
    using preservation_alw assms(1-2) .
  then have \<open>alw (holds (\<lambda>l. p at a in getBranch l)
        impl nxt (holds (\<lambda>l. p at a in getBranch l))) (sdrop (Suc m) steps)\<close> for p
    using alw_sdrop by blast
  ultimately have \<open>\<forall>p \<in> set ps. alw (holds (\<lambda>l. p at a in getBranch l)) (sdrop (Suc m) steps)\<close>
    using alw_invar by blast
  then have \<open>\<forall>p \<in> set ps. holds (\<lambda>l. p at a in getBranch l) (sdrop n steps)\<close>
    using \<open>m < n\<close> by (auto simp: alw_iff_sdrop elim: less_natE)

  moreover have \<open>alw (holds (\<lambda>l. \<forall>pps a. introduces (getTag l) = Some (pps, a) \<longrightarrow>
    (\<forall>ps \<in> set pps. \<forall>p\<in>set ps. new p a (getBranch l)))) steps\<close>
    using introduces_new_ipath assms(1-2) .
  then have \<open>alw (holds (\<lambda>l. \<forall>pps a. introduces (getTag l) = Some (pps, a) \<longrightarrow>
    (\<forall>ps \<in> set pps. \<forall>p\<in>set ps. new p a (getBranch l)))) (sdrop n steps)\<close>
   by (simp add: alw_iff_sdrop)
  then have \<open>\<forall>qs \<in> set qqs. \<forall>q\<in>set qs. holds (\<lambda>l. new q b (getBranch l)) (sdrop n steps)\<close>
    using assms(4, 7) by auto
  then have \<open>\<forall>p\<in>set ps. holds (\<lambda>l. \<not> p at a in (getBranch l)) (sdrop n steps)\<close>
    unfolding new_def using \<open>ps \<in>. pps\<close> \<open>(pps, a) = (qqs, b)\<close> by simp
  ultimately show False
    by (cases ps) (auto simp: \<open>ps \<noteq> []\<close>)    
qed

subsection \<open>Quasi\<close>

lemma wft_introduces_quasis_ipath':
  assumes
    \<open>ipath tab steps\<close> \<open>wft A tab\<close>
    \<open>generated_ipath steps \<subseteq> B\<close>
    \<open>holds (\<lambda>l. branch_nominals (getBranch l) \<subseteq> B) steps\<close>
    \<open>holds (\<lambda>l. branch_formulas (getBranch l) \<subseteq> X) steps\<close>
    and X: \<open>\<forall>x \<in> X. quasis B x \<subseteq> X\<close> and Xi: \<open>\<forall>i \<in> B. {Nom i, \<^bold>\<diamond> Nom i} \<subseteq> X\<close>
  shows \<open>alw (holds (\<lambda>step.
      (\<forall>pps a. introduces (getTag step) = Some (pps, a) \<longrightarrow> set (concat pps) \<subseteq> X) \<and>
      (\<forall>a p i. getTag step = Fresh a p i \<longrightarrow> (\<nexists>a. p = Nom a) \<and> (\<^bold>\<diamond> p) \<in> X))) steps\<close>
  using assms(1-5)
proof (coinduction arbitrary: tab steps)
  case alw
  then show ?case
  proof cases
    case (IPath s' subs tail l)
    then have wft: \<open>wft A s'\<close>
      using alw(2) wft_alwt by (auto elim: wft.cases)
    from alw(2) show ?thesis
    proof cases
      case (WfClose p i branch n)
      then show ?thesis
        using IPath by simp
    next
      case (WfOpen branch n)
      then show ?thesis
        using IPath by simp
    next
      case (WfNeg p a ps branch s n)
      from this(1) have s: \<open>s' = s\<close>
        using IPath by simp

      have ?thesis if
        \<open>p \<in> X\<close>
        \<open>holds (\<lambda>l. branch_nominals (getBranch l) \<subseteq> B) tail\<close>
        \<open>holds (\<lambda>l. branch_formulas (getBranch l) \<subseteq> X) tail\<close>
        using that wft WfNeg(1) alw(3-) IPath unfolding generated_ipath_def by auto

      moreover have \<open>(\<^bold>\<not> \<^bold>\<not> p) \<in> X\<close>
        using WfNeg(1, 2) IPath alw(5) at_in_branch_formulas
        by (metis holds_Stream insert_subset mk_disjoint_insert step.sel(3) tree.inject)
      then have \<open>p \<in> X\<close>
        using X by auto

      moreover have \<open>holdst (\<lambda>l. branch_nominals (getBranch l) \<subseteq> B) s\<close>
        using WfNeg(1-2, 4) IPath alw(4) branch_nominals_there[where p=p] by fastforce
      then have \<open>holds (\<lambda>l. branch_nominals (getBranch l) \<subseteq> B) tail\<close>
        using s IPath holds_holdst by fast

      moreover have \<open>holdst (\<lambda>l. branch_formulas (getBranch l) \<subseteq> X) s\<close>
        using WfNeg(1, 4) alw(5) \<open>p \<in> X\<close> IPath(1-2) by auto
      then have \<open>holds (\<lambda>l. branch_formulas (getBranch l) \<subseteq> X) tail\<close>
        using s IPath holds_holdst by fast

      ultimately show ?thesis
        by simp
    next
      case (WfDisP p q a ps branch sl n sr)
      from this(1) have s: \<open>s' = sl \<or> s' = sr\<close>
        using IPath by simp

      have ?thesis if
        \<open>p \<in> X\<close> \<open>q \<in> X\<close>
        \<open>holds (\<lambda>l. branch_nominals (getBranch l) \<subseteq> B) tail\<close>
        \<open>holds (\<lambda>l. branch_formulas (getBranch l) \<subseteq> X) tail\<close>
        using that wft WfDisP(1) alw(3-) IPath unfolding generated_ipath_def by auto

      moreover have \<open>(p \<^bold>\<or> q) \<in> X\<close>
        using WfDisP(1, 2) IPath alw(5) at_in_branch_formulas
        by (metis holds_Stream insert_subset mk_disjoint_insert step.sel(3) tree.inject)
      then have \<open>p \<in> X\<close> \<open>q \<in> X\<close>
        using X by auto

      moreover {
        have \<open>holdst (\<lambda>l. branch_nominals (getBranch l) \<subseteq> B) sl\<close>
          using WfDisP(1-2, 5) IPath alw(4) branch_nominals_there[where p=p] by fastforce
        moreover have \<open>holdst (\<lambda>l. branch_nominals (getBranch l) \<subseteq> B) sr\<close>
          using WfDisP(1-2, 7) IPath alw(4) branch_nominals_there[where p=q] by fastforce
        ultimately have \<open>holds (\<lambda>l. branch_nominals (getBranch l) \<subseteq> B) tail\<close>
          using s IPath holds_holdst by fast
      }

      moreover have
        \<open>holdst (\<lambda>l. branch_formulas (getBranch l) \<subseteq> X) sl\<close>
        \<open>holdst (\<lambda>l. branch_formulas (getBranch l) \<subseteq> X) sr\<close>
        using WfDisP(1, 5, 7) alw(5) \<open>p \<in> X\<close> \<open>q \<in> X\<close> IPath(1-2) by auto
      then have \<open>holds (\<lambda>l. branch_formulas (getBranch l) \<subseteq> X) tail\<close>
        using s IPath holds_holdst by fast

      ultimately show ?thesis
        by simp
    next
      case (WfDisN p q a ps branch s n intro)
      from this(1) have s: \<open>s' = s\<close>
        using IPath by simp

      have ?thesis if
        \<open>(\<^bold>\<not> p) \<in> X\<close> \<open>(\<^bold>\<not> q) \<in> X\<close>
        \<open>holds (\<lambda>l. branch_nominals (getBranch l) \<subseteq> B) tail\<close>
        \<open>holds (\<lambda>l. branch_formulas (getBranch l) \<subseteq> X) tail\<close>
        using that wft WfDisN(1, 7) alw(3-) IPath unfolding generated_ipath_def by auto

      moreover have \<open>(\<^bold>\<not> (p \<^bold>\<or> q)) \<in> X\<close>
        using WfDisN(1, 2) IPath alw(5) at_in_branch_formulas
        by (metis holds_Stream insert_subset mk_disjoint_insert step.sel(3) tree.inject)
      then have \<open>(\<^bold>\<not> p) \<in> X\<close> \<open>(\<^bold>\<not> q) \<in> X\<close>
        using X by auto

      moreover {
        have \<open>branch_nominals (((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, a) # branch) \<subseteq> nominals p \<union> nominals q \<union> B\<close>
          using WfDisN(1-2) IPath alw(4) by auto
        moreover have \<open>nominals p \<subseteq> B\<close> \<open>nominals q \<subseteq> B\<close>
          using WfDisN(1-2) IPath(1-2) alw(4) unfolding branch_nominals_def by force+
        ultimately have \<open>holdst (\<lambda>l. branch_nominals (getBranch l) \<subseteq> B) s\<close>
          using WfDisN(1, 4) IPath alw(4) by simp
        then have \<open>holds (\<lambda>l. branch_nominals (getBranch l) \<subseteq> B) tail\<close>
          using s IPath holds_holdst by fast
      }

      moreover have \<open>holdst (\<lambda>l. branch_formulas (getBranch l) \<subseteq> X) s\<close>
        using WfDisN(1, 4) alw(5) \<open>(\<^bold>\<not> p) \<in> X\<close> \<open>(\<^bold>\<not> q) \<in> X\<close> IPath(1-2) by auto
      then have \<open>holds (\<lambda>l. branch_formulas (getBranch l) \<subseteq> X) tail\<close>
        using s IPath holds_holdst by fast

      ultimately show ?thesis
        by simp
    next
      case (WfDiaP p a ps branch i s n)
      from this(1) have s: \<open>s' = s\<close>
        using IPath by simp

      have ?thesis if
        \<open>(\<^bold>@ i p) \<in> X\<close> \<open>(\<^bold>\<diamond> Nom i) \<in> X\<close> \<open>(\<^bold>\<diamond> p) \<in> X\<close>
        \<open>holds (\<lambda>l. branch_nominals (getBranch l) \<subseteq> B) tail\<close>
        \<open>holds (\<lambda>l. branch_formulas (getBranch l) \<subseteq> X) tail\<close>
        using that wft WfDiaP(1, 4) alw(3-) IPath unfolding generated_ipath_def by auto

      moreover have \<open>i \<in> B\<close>
        using WfDiaP(1) alw(3) IPath unfolding generated_ipath_def by simp

      moreover have \<open>(\<^bold>\<diamond> p) \<in> X\<close>
        using WfDiaP(1, 2) IPath alw(5) at_in_branch_formulas
        by (metis holds_Stream insert_subset mk_disjoint_insert step.sel(3) tree.inject)
      moreover from this have \<open>(\<^bold>@ i p) \<in> X\<close> \<open>(\<^bold>\<diamond> Nom i) \<in> X\<close>
        using \<open>i \<in> B\<close> WfDiaP(4) X Xi by fastforce+

      moreover {
        have \<open>branch_nominals (((\<^bold>@ i p) # (\<^bold>\<diamond> Nom i) # ps, a) # branch) \<subseteq> {i} \<union> nominals p \<union> B\<close>
          using WfDiaP(1-2) IPath alw(4) by auto
        moreover have \<open>nominals p \<subseteq> B\<close>
          using WfDiaP(1-2) IPath(1-2) alw(4) unfolding branch_nominals_def by force
        ultimately have \<open>holdst (\<lambda>l. branch_nominals (getBranch l) \<subseteq> B) s\<close>
          using \<open>i \<in> B\<close> WfDiaP(1, 6) IPath alw(4) by simp
        then have \<open>holds (\<lambda>l. branch_nominals (getBranch l) \<subseteq> B) tail\<close>
          using s IPath holds_holdst by fast
      }

      moreover have \<open>holdst (\<lambda>l. branch_formulas (getBranch l) \<subseteq> X) s\<close>
        using WfDiaP(1, 6) alw(5) \<open>(\<^bold>@ i p) \<in> X\<close> \<open>(\<^bold>\<diamond> Nom i) \<in> X\<close> IPath(1-2) by auto
      then have \<open>holds (\<lambda>l. branch_formulas (getBranch l) \<subseteq> X) tail\<close>
        using s IPath holds_holdst by fast

      ultimately show ?thesis
        by simp
    next
      case (WfDiaN p a ps branch i s n)
      from this(1) have s: \<open>s' = s\<close>
        using IPath by simp

      have \<open>i \<in> B\<close>
        using WfDiaN(1, 3) alw(4) IPath unfolding branch_nominals_def by force

      have ?thesis if
        \<open>(\<^bold>\<not> (\<^bold>@ i p)) \<in> X\<close>
        \<open>holds (\<lambda>l. branch_nominals (getBranch l) \<subseteq> B) tail\<close>
        \<open>holds (\<lambda>l. branch_formulas (getBranch l) \<subseteq> X) tail\<close>
        using that wft WfDiaN(1) alw(3-) IPath unfolding generated_ipath_def by auto

      moreover have \<open>(\<^bold>\<not> (\<^bold>\<diamond> p)) \<in> X\<close>
        using WfDiaN(1, 2) IPath alw(5) at_in_branch_formulas
        by (metis holds_Stream insert_subset mk_disjoint_insert step.sel(3) tree.inject)
      then have \<open>(\<^bold>\<not> (\<^bold>@ i p)) \<in> X\<close>
        using \<open>i \<in> B\<close> X by fastforce

      moreover {
        have \<open>branch_nominals (((\<^bold>\<not> (\<^bold>@ i p)) # ps, a) # branch) \<subseteq> {i} \<union> nominals p \<union> B\<close>
          using WfDiaN(1-3) IPath alw(4) by auto
        moreover have \<open>nominals p \<subseteq> B\<close>
          using WfDiaN(1-2) IPath(1-2) alw(4) unfolding branch_nominals_def by force
        ultimately have \<open>holdst (\<lambda>l. branch_nominals (getBranch l) \<subseteq> B) s\<close>
          using \<open>i \<in> B\<close> WfDiaN(1, 5) IPath alw(4) by simp
        then have \<open>holds (\<lambda>l. branch_nominals (getBranch l) \<subseteq> B) tail\<close>
          using s IPath holds_holdst by fast
      }

      moreover have \<open>holdst (\<lambda>l. branch_formulas (getBranch l) \<subseteq> X) s\<close>
        using WfDiaN(1, 5) alw(5) \<open>(\<^bold>\<not> (\<^bold>@ i p)) \<in> X\<close> IPath(1-2) by auto
      then have \<open>holds (\<lambda>l. branch_formulas (getBranch l) \<subseteq> X) tail\<close>
        using s IPath holds_holdst by fast

      ultimately show ?thesis
        by simp
    next
      case (WfSatP a p b ps branch s n)
      from this(1) have s: \<open>s' = s\<close>
        using IPath by simp

      have ?thesis if
        \<open>p \<in> X\<close>
        \<open>holds (\<lambda>l. branch_nominals (getBranch l) \<subseteq> B) tail\<close>
        \<open>holds (\<lambda>l. branch_formulas (getBranch l) \<subseteq> X) tail\<close>
        using that wft WfSatP(1) alw(3-) IPath unfolding generated_ipath_def by auto

      moreover have \<open>(\<^bold>@ a p) \<in> X\<close>
        using WfSatP(1, 2) IPath alw(5) at_in_branch_formulas
        by (metis holds_Stream insert_subset mk_disjoint_insert step.sel(3) tree.inject)
      then have \<open>p \<in> X\<close>
        using X by auto

      moreover have \<open>holdst (\<lambda>l. branch_nominals (getBranch l) \<subseteq> B) s\<close>
        using WfSatP(1-2, 4) IPath alw(4) branch_nominals_there[where p=p] by fastforce
      then have \<open>holds (\<lambda>l. branch_nominals (getBranch l) \<subseteq> B) tail\<close>
        using s IPath holds_holdst by fast

      moreover have \<open>holdst (\<lambda>l. branch_formulas (getBranch l) \<subseteq> X) s\<close>
        using WfSatP(1, 4) alw(5) \<open>p \<in> X\<close> IPath(1-2) by auto
      then have \<open>holds (\<lambda>l. branch_formulas (getBranch l) \<subseteq> X) tail\<close>
        using s IPath holds_holdst by fast

      ultimately show ?thesis
        by simp
    next
      case (WfSatN a p b ps branch s n)
      from this(1) have s: \<open>s' = s\<close>
        using IPath by simp

      have ?thesis if
        \<open>(\<^bold>\<not> p) \<in> X\<close>
        \<open>holds (\<lambda>l. branch_nominals (getBranch l) \<subseteq> B) tail\<close>
        \<open>holds (\<lambda>l. branch_formulas (getBranch l) \<subseteq> X) tail\<close>
        using that wft WfSatN(1) alw(3-) IPath unfolding generated_ipath_def by auto

      moreover have \<open>(\<^bold>\<not> (\<^bold>@ a p)) \<in> X\<close>
        using WfSatN(1, 2) IPath alw(5) at_in_branch_formulas
        by (metis holds_Stream insert_subset mk_disjoint_insert step.sel(3) tree.inject)
      then have \<open>(\<^bold>\<not> p) \<in> X\<close>
        using X by auto

      moreover have \<open>holdst (\<lambda>l. branch_nominals (getBranch l) \<subseteq> B) s\<close>
        using WfSatN(1-2, 4) IPath alw(4) branch_nominals_there[where p=\<open>\<^bold>\<not> p\<close>] by fastforce
      then have \<open>holds (\<lambda>l. branch_nominals (getBranch l) \<subseteq> B) tail\<close>
        using s IPath holds_holdst by fast

      moreover have \<open>holdst (\<lambda>l. branch_formulas (getBranch l) \<subseteq> X) s\<close>
        using WfSatN(1, 4) alw(5) \<open>(\<^bold>\<not> p) \<in> X\<close> IPath(1-2) by auto
      then have \<open>holds (\<lambda>l. branch_formulas (getBranch l) \<subseteq> X) tail\<close>
        using s IPath holds_holdst by fast

      ultimately show ?thesis
        by simp
    next
      case (WfGoTo i branch s n)
      from this(1) have s: \<open>s' = s\<close>
        using IPath by simp

      have ?thesis if
        \<open>holds (\<lambda>l. branch_nominals (getBranch l) \<subseteq> B) tail\<close>
        \<open>holds (\<lambda>l. branch_formulas (getBranch l) \<subseteq> X) tail\<close>
        using that wft WfGoTo(1) alw(3-) IPath unfolding generated_ipath_def by auto

      moreover have \<open>i \<in> B\<close>
        using WfGoTo(1-2) IPath alw(4) by auto
      then have \<open>holdst (\<lambda>l. branch_nominals (getBranch l) \<subseteq> B) s\<close>
        using WfGoTo(1, 3) IPath alw(4) unfolding branch_nominals_def by auto        
      then have \<open>holds (\<lambda>l. branch_nominals (getBranch l) \<subseteq> B) tail\<close>
        using s IPath holds_holdst by fast

      moreover have \<open>holdst (\<lambda>l. branch_formulas (getBranch l) \<subseteq> X) s\<close>
        using WfGoTo(1, 3) alw(5) \<open>i \<in> B\<close> Xi IPath(1-2) unfolding branch_formulas_def by simp
      then have \<open>holds (\<lambda>l. branch_formulas (getBranch l) \<subseteq> X) tail\<close>
        using s IPath holds_holdst by fast

      ultimately show ?thesis
        by simp
    next
      case (WfNom p b ps a branch s n)
           from this(1) have s: \<open>s' = s\<close>
        using IPath by simp

      have ?thesis if
        \<open>p \<in> X\<close>
        \<open>holds (\<lambda>l. branch_nominals (getBranch l) \<subseteq> B) tail\<close>
        \<open>holds (\<lambda>l. branch_formulas (getBranch l) \<subseteq> X) tail\<close>
        using that wft WfNom(1) alw(3-) IPath unfolding generated_ipath_def by auto

      moreover have \<open>p \<in> X\<close>
        using WfNom(1, 2) IPath alw(5) at_in_branch_formulas
        by (metis holds_Stream insert_subset mk_disjoint_insert step.sel(3) tree.inject)

      moreover have \<open>holdst (\<lambda>l. branch_nominals (getBranch l) \<subseteq> B) s\<close>
        using WfNom(1-2, 6) IPath alw(4) branch_nominals_there[where p=p] by fastforce
      then have \<open>holds (\<lambda>l. branch_nominals (getBranch l) \<subseteq> B) tail\<close>
        using s IPath holds_holdst by fast

      moreover have \<open>holdst (\<lambda>l. branch_formulas (getBranch l) \<subseteq> X) s\<close>
        using WfNom(1, 6) alw(5) \<open>p \<in> X\<close> IPath(1-2) by auto
      then have \<open>holds (\<lambda>l. branch_formulas (getBranch l) \<subseteq> X) tail\<close>
        using s IPath holds_holdst by fast

      ultimately show ?thesis
        by simp
    qed
  qed
qed

lemma wft_introduces_quasis_ipath:
  fixes tab steps
  defines \<open>B \<equiv> generated_ipath steps \<union> branch_nominals (getBranch (shd steps))\<close>
  defines \<open>X \<equiv> formula_bound B (getBranch (shd steps))\<close>
  assumes \<open>ipath tab steps\<close> \<open>wft A tab\<close>
  shows
    \<open>alw (holds (\<lambda>l. \<forall>pps a. introduces (getTag l) = Some (pps, a) \<longrightarrow> set (concat pps) \<subseteq> X)) steps\<close>
    \<open>alw (holds (\<lambda>step. \<forall>a p i. getTag step = Fresh a p i \<longrightarrow> (\<nexists>a. p = Nom a) \<and>(\<^bold>\<diamond> p) \<in> X)) steps\<close>
proof -
  have \<open>generated_ipath steps \<subseteq> B\<close> \<open>branch_nominals (getBranch (shd steps)) \<subseteq> B\<close>
    unfolding B_def by simp_all
  moreover have \<open>branch_formulas (getBranch (shd steps)) \<subseteq> X\<close> \<open>\<forall>i\<in>B. {Nom i, \<^bold>\<diamond> Nom i} \<subseteq> X\<close>
    unfolding B_def X_def formula_bound_def by blast+
  moreover have \<open>\<forall>x\<in>X. quasis B x \<subseteq> X\<close>
    unfolding X_def using formula_bound_quasis by blast
  ultimately have \<open>alw
      (holds (\<lambda>step. (\<forall>pps a. introduces (getTag step) = Some (pps, a) \<longrightarrow> set (concat pps) \<subseteq> X) \<and>
      (\<forall>a p i. getTag step = Fresh a p i \<longrightarrow> (\<nexists>a. p = Nom a) \<and> (\<^bold>\<diamond> p) \<in> X))) steps\<close>
    using assms(3-4) wft_introduces_quasis_ipath' by fastforce
  then show
    \<open>alw (holds (\<lambda>l. \<forall>pps a. introduces (getTag l) = Some (pps, a) \<longrightarrow> set (concat pps) \<subseteq> X)) steps\<close>
    \<open>alw (holds (\<lambda>step. \<forall>a p i. getTag step = Fresh a p i \<longrightarrow> (\<nexists>a. p = Nom a) \<and> (\<^bold>\<diamond> p) \<in> X)) steps\<close>
    by (metis (no_types, lifting) alw_sset sset_alw)+
qed

subsection \<open>Finite\<close>

lemma finite_introduces_lists:
  fixes X k
  defines \<open>Y \<equiv> {ps. set ps \<subseteq> X \<and> length ps \<le> k}\<close>
  assumes \<open>finite X\<close>
  shows \<open>finite {pps. set pps \<subseteq> Y \<and> length pps \<le> m}\<close>
proof -
  have \<open>finite Y\<close>
    unfolding Y_def using finite_lists_length_le \<open>finite X\<close> .
  then show ?thesis
    using finite_lists_length_le \<open>finite X\<close> by blast
qed

(* TODO: maybe drop some inner universal quantifiers? *)
lemma introduces_lengths:
  assumes \<open>wft A tab\<close>
  shows \<open>alwt (holdst (\<lambda>l. \<forall>pps a.
    (introduces (getTag l) = Some (pps, a) \<longrightarrow>
      length pps \<le> 2 \<and> (\<forall>ps \<in> set pps. length ps \<le> 2)))) tab\<close>
  using assms by (coinduction arbitrary: tab) (fastforce elim: wft.cases)

lemma wft_introduces_nominals:
  assumes \<open>wft A tab\<close>
  shows \<open>relt (Here (\<lambda>step. \<forall>ps a. introduces (getTag step) = Some (ps, a) \<longrightarrow>
    a \<in> branch_nominals (getBranch step))) tab\<close>
  using assms unfolding branch_nominals_def by (auto elim: wft.cases)

lemma wft_introduces_nominals_ipath:
  assumes \<open>wft A tab\<close> \<open>ipath tab steps\<close>
  shows \<open>alw (holds (\<lambda>step. \<forall>ps a. introduces (getTag step) = Some (ps, a) \<longrightarrow>
    a \<in> branch_nominals (getBranch step))) steps\<close>
proof -
  have \<open>alw (rels (Here (\<lambda>step. \<forall>ps a. introduces (getTag step) = Some (ps, a) \<longrightarrow>
    a \<in> branch_nominals (getBranch step)))) steps\<close>
    using wft_alw assms wft_introduces_nominals .
  then show ?thesis
    by simp
qed

lemma introduces_bound:
  fixes steps
  defines \<open>B \<equiv> generated_ipath steps \<union> branch_nominals (getBranch (shd steps))\<close>
  assumes \<open>wft A tab\<close> \<open>ipath tab steps\<close> \<open>finite B\<close>
  shows \<open>\<exists>n. \<forall>k \<ge> n. introduces (getTag (steps !! k)) = None\<close>
proof -
  let ?X = \<open>formula_bound B (getBranch (shd steps))\<close>
  let ?f = \<open>introduces o getTag\<close>
  let ?D = \<open>?f ` sset steps\<close>

  let ?Y = \<open>{pps. set pps \<subseteq> {ps. set ps \<subseteq> ?X \<and> length ps \<le> 2} \<and> length pps \<le> 2}\<close>

  have \<open>alw (holds (\<lambda>l. \<forall>pps a. ?f l = Some (pps, a) \<longrightarrow> set (concat pps) \<subseteq> ?X)) steps\<close>
    using assms wft_introduces_quasis_ipath by auto
  then have \<open>\<forall>intro \<in> ?D. \<forall>pps a. intro = Some (pps, a) \<longrightarrow> set (concat pps) \<subseteq> ?X\<close>
    using alw_sset by (smt (verit, best) imageE)
  then have \<open>\<forall>intro \<in> ?D. \<forall>pps a. intro = Some (pps, a) \<longrightarrow> (\<forall>ps \<in> set pps. set ps \<subseteq> ?X)\<close>
    by auto

  moreover have \<open>\<forall>intro \<in> ?D. \<forall>pps a. intro = Some (pps, a) \<longrightarrow>
      length pps \<le> 2 \<and> (\<forall>ps \<in> set pps. length ps \<le> 2)\<close>
    using assms(2-3) alw_sset introduces_lengths alwt_ipath by fastforce
  ultimately have \<open>\<forall>intro \<in> ?D. \<forall>pps a. intro = Some (pps, a) \<longrightarrow> pps \<in> ?Y\<close>
    by auto

  (* TODO: pps should be pss? *)
  moreover {
    have \<open>alw (holds (\<lambda>step. \<forall>pps a. ?f step = Some (pps, a) \<longrightarrow>
        a \<in> branch_nominals (getBranch step))) steps\<close>
      using assms wft_introduces_nominals_ipath by auto
    then have \<open>\<forall>step \<in> sset steps. \<forall>pps a. ?f step = Some (pps, a) \<longrightarrow>
      a \<in> branch_nominals (getBranch step)\<close>
      using alw_sset by (metis (mono_tags, lifting))
    moreover have \<open>alw (holds (\<lambda>l. branch_nominals (getBranch l) \<subseteq>
         branch_nominals (getBranch (shd steps)) \<union> generated_ipath steps)) steps\<close>
      using assms(2-3) wft_generated_ipath by fast
    then have \<open>\<forall>step \<in> sset steps. branch_nominals (getBranch step) \<subseteq>
         branch_nominals (getBranch (shd steps)) \<union> generated_ipath steps\<close>
      using alw_sset by (metis (mono_tags, lifting))
    ultimately have \<open>\<forall>intro \<in> ?D. \<forall>pps a. intro = Some (pps, a) \<longrightarrow> a \<in> B\<close>
      unfolding B_def comp_def by fast
  }
  ultimately have \<open>\<forall>intro \<in> ?D. \<forall>x. intro = Some x \<longrightarrow> x \<in> ?Y \<times> B\<close>
    by simp
  then have \<open>?D \<subseteq> {None} \<union> Some ` (?Y \<times> B)\<close>
    by blast

  moreover have \<open>finite ?X\<close>
    using assms(4) finite_formula_bound by blast
  then have \<open>finite ?Y\<close>
    using finite_introduces_lists by blast
  then have \<open>finite ({None} \<union> Some ` (?Y \<times> B))\<close>
    using \<open>finite B\<close> by blast
  ultimately have \<open>finite ?D\<close>
    by (simp add: finite_subset)

  then obtain n where n: \<open>?D \<subseteq> ?f ` set (stake n steps)\<close>
    using stake_finite' by blast

  have \<open>\<forall>k \<ge> Suc n. ?f (steps !! k) = None\<close>
  proof (intro allI impI)
    fix k
    assume \<open>Suc n \<le> k\<close>
    show \<open>?f (steps !! k) = None\<close>
    proof (rule ccontr)
      assume \<open>?f (steps !! k) \<noteq> None\<close>
      then obtain ps a where ps: \<open>?f (steps !! k) = Some (ps, a)\<close>
        by fast
      then have \<open>Some (ps, a) \<in> ?D\<close>
        by (metis comp_apply imageI snth_sset)
      then have \<open>Some (ps, a) \<in> ?f ` set (stake n steps)\<close>
        using n by blast
      then obtain m where \<open>m \<le> n\<close> \<open>?f (steps !! m) = Some (ps, a)\<close>
        using stake_snth by force
      moreover have \<open>m < k\<close>
        using \<open>m \<le> n\<close> \<open>Suc n \<le> k\<close> by simp
      ultimately show False
        using ps assms(2-3) distinct_introduces by fastforce
    qed
  qed
  then show ?thesis
    by auto
qed

lemma Block_Next_potential:
  assumes \<open>wft A tab\<close>
  shows \<open>relt (Impl (\<lambda>l. (\<exists>i. getTag l = Block i) \<and> getPotential l = Suc n)
    (Next (Here (\<lambda>t. getPotential t = n)))) tab\<close>
  using assms by (auto elim: wft.cases)

lemma Block_nxt_potential:
  assumes \<open>wft A tab\<close> \<open>ipath tab steps\<close>
  shows \<open>alw (holds (\<lambda>l. (\<exists>i. getTag l = Block i) \<and> getPotential l = Suc n)
    impl (nxt (holds (\<lambda>t. getPotential t = n)))) steps\<close>
proof -
  have \<open>alw (rels (Impl (\<lambda>l. (\<exists>i. getTag l = Block i) \<and> getPotential l = Suc n)
    (Next (Here (\<lambda>t. getPotential t = n))))) steps\<close>
    using wft_alw assms Block_Next_potential .
  then show ?thesis
    by simp
qed

lemma Suc_potential:
  assumes \<open>wft A tab\<close>
  shows \<open>relt (Here (\<lambda>l. (\<exists>i. getTag l = Block i) \<longrightarrow> (\<exists>n. getPotential l = Suc n))) tab\<close>
  using assms(1) by (auto elim: wft.cases)

lemma Suc_potential_ipath:
  assumes \<open>wft A tab\<close> \<open>ipath tab steps\<close>
  shows \<open>alw (holds (\<lambda>l. (\<exists>i. getTag l = Block i) \<longrightarrow> (\<exists>n. getPotential l = Suc n))) steps\<close>
proof -
  have \<open>alw (rels (Here (\<lambda>l. (\<exists>i. getTag l = Block i) \<longrightarrow> (\<exists>n. getPotential l = Suc n)))) steps\<close>
    using wft_alw assms Suc_potential .
  then show ?thesis
    by simp
qed

lemma ipath_ev_not_Block:
  assumes \<open>wft A tab\<close> \<open>ipath tab steps\<close>
  shows \<open>\<exists>k. \<nexists>i. getTag (sdrop m steps !! k) = Block i\<close>
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
  then have *: \<open>\<forall>k. \<exists>i. getTag (sdrop m steps !! k) = Block i\<close>
    by blast
  moreover have \<open>alw (holds (\<lambda>l. (\<exists>i. getTag l = Block i) \<longrightarrow> (\<exists>n. getPotential l = Suc n))) steps\<close>
    using Suc_potential_ipath assms .
  ultimately have suc: \<open>\<forall>k. \<exists>n. getPotential (sdrop m steps !! k) = Suc n\<close>
    using alw_snth alw_sdrop by blast
  then obtain n where n: \<open>getPotential (shd (sdrop m steps)) = Suc n\<close>
    by (metis snth.simps(1))

  have \<open>alw (holds (\<lambda>l. (\<exists>i. getTag l = Block i) \<and> getPotential l = Suc n)
    impl (nxt (holds (\<lambda>t. getPotential t = n)))) steps\<close> for n
    using Block_nxt_potential assms .
  then have \<open>alw (holds (\<lambda>l. (\<exists>i. getTag l = Block i) \<and> getPotential l = Suc n)
    impl (nxt (holds (\<lambda>t. getPotential t = n)))) (sdrop m steps)\<close> for n
    by (simp add: alw_iff_sdrop)
  then have \<open>\<forall>k. ((holds (\<lambda>l. (\<exists>i. getTag l = Block i) \<and> getPotential l = Suc n))
       impl (nxt (holds (\<lambda>t. getPotential t = n)))) (sdrop (m + k) steps)\<close> for n
    by (simp add: alw_iff_sdrop)
  then have \<open>\<forall>k. holds (\<lambda>l. (\<exists>i. getTag l = Block i) \<and> getPotential l = Suc n) (sdrop (m + k) steps)
       \<longrightarrow> holds (\<lambda>t. getPotential t = n) (sdrop (Suc m + k) steps)\<close> for n
    by simp
  moreover from * have \<open>\<forall>k. holds (\<lambda>l. (\<exists>i. getTag l = Block i)) (sdrop (m + k) steps)\<close>
    by (metis (mono_tags, lifting) holds.elims(1) sdrop_add sdrop_simps(1))
  ultimately have **: \<open>\<forall>k. (holds (\<lambda>l. getPotential l = Suc n)) (sdrop (m + k) steps)
       \<longrightarrow> (holds (\<lambda>t. getPotential t = n)) (sdrop (Suc (m + k)) steps)\<close> for n
    by (simp add: alw_iff_sdrop)

  have \<open>getPotential (sdrop m steps !! k) = Suc n - k\<close> for k
  proof (induct k)
    case 0
    then show ?case
      using n by simp
  next
    case (Suc k)
    moreover obtain x where x: \<open>getPotential (sdrop m steps !! k) = Suc x\<close>
      using suc by metis
    then have \<open>getPotential (sdrop m steps !! Suc k) = x\<close>
      using ** by (simp add: sdrop_snth)
    ultimately show ?case
      using x by simp
  qed
  then have \<open>getPotential (sdrop m steps !! Suc n) = 0\<close>
    by presburger
  then show False
    using suc by (metis Zero_not_Suc)
qed

lemma ipath_Open_Close:
  assumes \<open>ipath tab steps\<close> \<open>wft A tab\<close> 
  shows \<open>alw (holds (\<lambda>l. getTag l \<noteq> Open \<and> (\<nexists>p i. getTag l = Close p i))) steps\<close>
  using assms
proof (coinduction arbitrary: tab steps)
  case alw
  then show ?case
    by cases (fastforce elim: wft.cases)
qed

lemma introduces_None:
  assumes \<open>introduces t = None\<close>
  shows \<open>t = Open \<or> (\<exists>p i. t = Close p i) \<or> (\<exists>i. t = Block i)\<close>
  using assms by (cases t) simp_all

theorem infinite_generated:
  assumes \<open>wft A tab\<close> \<open>ipath tab steps\<close>
  shows \<open>infinite (generated_ipath steps)\<close>
proof
  let ?B = \<open>generated_ipath steps \<union> branch_nominals (getBranch (shd steps))\<close>
  assume \<open>finite (generated_ipath steps)\<close>
  then have \<open>finite ?B\<close>
    using finite_branch_nominals by blast
  then obtain k where k: \<open>\<forall>k' \<ge> k. introduces (getTag (steps !! k')) = None\<close>
    using assms(1-2) introduces_bound by blast
  then have \<open>alw (holds (\<lambda>l. introduces (getTag l) = None)) (sdrop k steps)\<close>
    by (simp add: alw_iff_sdrop)
  moreover have \<open>alw (holds (\<lambda>l. getTag l \<noteq> Open \<and> (\<nexists>p i. getTag l = Close p i))) steps\<close>
    using ipath_Open_Close assms(2, 1) .
  then have \<open>alw (holds (\<lambda>l. getTag l \<noteq> Open \<and> (\<nexists>p i. getTag l = Close p i))) (sdrop k steps)\<close>
    by (simp add: alw_iff_sdrop)
  ultimately have *: \<open>alw (holds (\<lambda>l. \<exists>i. getTag l = Block i)) (sdrop k steps)\<close>
    using introduces_None by (metis (mono_tags, lifting) alw_sset sset_alw)
  moreover have \<open>\<exists>x. \<nexists>i. getTag (sdrop k steps !! x) = Block i\<close>
    using ipath_ev_not_Block assms(1-2) .
  ultimately show False
    using alw_snth by blast
qed

section \<open>Infinite Path\<close>

definition propers :: \<open>('a, 'b) fm set \<Rightarrow> ('a, 'b) fm set\<close> where
  \<open>propers X \<equiv> {p. p \<in> X \<and> (\<exists>p'. p = (\<^bold>\<diamond> p') \<and> (\<nexists>a. p' = Nom a))}\<close>

lemma finite_propers_quasis: \<open>finite (propers (quasis A p))\<close>
proof (induct p rule: quasis.induct)
  case (1 A p)
  moreover have \<open>propers (quasis A (\<^bold>\<not> \<^bold>\<not> p)) \<subseteq> {p} \<union> propers (quasis A p)\<close>
    unfolding propers_def by auto
  ultimately show ?case
    by (simp add: finite_subset)
next
  case (2 A p q)
  moreover have \<open>propers (quasis A (p \<^bold>\<or> q)) \<subseteq> {p, q} \<union> propers (quasis A p) \<union> propers (quasis A q)\<close>
    unfolding propers_def by auto
  ultimately show ?case
    by (simp add: finite_subset)
next
  case (3 A p q)
  moreover have \<open>propers (quasis A (\<^bold>\<not> (p \<^bold>\<or> q))) \<subseteq>
      {\<^bold>\<not> p, \<^bold>\<not> q} \<union> propers (quasis A (\<^bold>\<not> p)) \<union> propers (quasis A (\<^bold>\<not> q))\<close>
    unfolding propers_def by auto
  ultimately show ?case
    by (simp add: finite_subset)
next
  case (4 A p)
  moreover have \<open>propers (quasis A (\<^bold>\<diamond> p)) \<subseteq> {p} \<union> propers (quasis A p)\<close>
    unfolding propers_def by auto
  ultimately show ?case
    unfolding propers_def
    by (cases \<open>\<exists>a. p = Nom a\<close>) (simp_all add: finite_subset)
next
  case (5 A p)
  moreover have \<open>propers (quasis A (\<^bold>\<not> (\<^bold>\<diamond> p))) \<subseteq> {\<^bold>\<not> p} \<union> propers (quasis A (\<^bold>\<not> p))\<close>
    unfolding propers_def by auto
  ultimately show ?case
    by (simp add: finite_subset)    
next
  case (6 A i p)
  moreover have \<open>propers (quasis A (\<^bold>@ i p)) \<subseteq> {p} \<union> propers (quasis A p)\<close>
    unfolding propers_def by auto
  ultimately show ?case
    by (simp add: finite_subset)    
next
  case (7 A i p)
  moreover have \<open>propers (quasis A (\<^bold>\<not> (\<^bold>@ i p))) \<subseteq> {\<^bold>\<not> p} \<union> propers (quasis A (\<^bold>\<not> p))\<close>
    unfolding propers_def by auto
  ultimately show ?case
    by (simp add: finite_subset)    
qed (simp_all add: propers_def)

lemma propers_Un: \<open>propers (A \<union> B) = propers A \<union> propers B\<close>
  unfolding propers_def by blast

lemma propers_subset: \<open>propers X \<subseteq> X\<close>
  unfolding propers_def by blast

lemma finite_propers_formula_bound: \<open>finite (propers (formula_bound B branch))\<close>
proof -
  let ?b = \<open>branch_formulas branch\<close>
  have b: \<open>finite ?b\<close>
    using finite_branch_formulas by blast

  let ?X = \<open>formula_bound B branch\<close>

  have \<open>propers (\<Union>p \<in> ?b. quasis B p) = (\<Union>p \<in> ?b. propers (quasis B p))\<close>
    unfolding propers_def by blast
  moreover have \<open>finite (propers (quasis B p))\<close> for p :: \<open>('a, 'b) fm\<close>
    using finite_propers_quasis by blast
  ultimately have \<open>finite (propers (\<Union>p \<in> ?b. quasis B p))\<close>
    using b by simp
  moreover have \<open>finite (propers ?b)\<close>
    using b finite_subset propers_subset by blast
  moreover have \<open>propers ?X = propers ?b \<union> propers (\<Union>p \<in> ?b. quasis B p)\<close>
    unfolding formula_bound_def propers_def by blast
  ultimately show ?thesis
    by simp
qed

lemma Fresh_unwitnessed:
  assumes \<open>wft A tab\<close>
  shows \<open>relt (Here (\<lambda>t. \<forall>a p i. getTag t = Fresh a p i \<longrightarrow> \<not> witnessed p a (getBranch t))) tab\<close>
  using assms by (auto elim: wft.cases)

lemma Fresh_unwitnessed_ipath:
  assumes \<open>wft A tab\<close> \<open>ipath tab steps\<close>
  shows \<open>alw (holds (\<lambda>t. \<forall>a p i. getTag t = Fresh a p i \<longrightarrow> \<not> witnessed p a (getBranch t))) steps\<close>
proof -
  have \<open>alw (rels (Here (\<lambda>t. \<forall>a p i. getTag t = Fresh a p i \<longrightarrow>
    \<not> witnessed p a (getBranch t)))) steps\<close>
  using wft_alw assms Fresh_unwitnessed .
  then show ?thesis
    by simp
qed

lemma distinct_Fresh:
  assumes \<open>wft A tab\<close> \<open>ipath tab steps\<close> \<open>steps !! m = s\<close> \<open>steps !! n = s'\<close> \<open>m < n\<close>
    \<open>getTag s = Fresh a p i\<close> \<open>getTag s' = Fresh a q j\<close>
  shows \<open>p \<noteq> q\<close>
proof -
  let ?ps = \<open>[\<^bold>@ i p, \<^bold>\<diamond> Nom i]\<close>
  have \<open>alw (holds (\<lambda>t. introduces (getTag t) = Some ([?ps], a))
   impl nxt (holds (\<lambda>s. \<exists>ps \<in> set [?ps]. ps \<noteq> [] \<and> (\<forall>p\<in>set ps. p at a in getBranch s)))) steps\<close>
    using introduces_alw_nxt assms(1-2) .
  then have \<open>holds (\<lambda>s. \<forall>p\<in>set ?ps. p at a in getBranch s) (sdrop (Suc m) steps)\<close>
    using assms(3, 6) by (simp add: alw_iff_sdrop)
  then have
    \<open>holds (\<lambda>s. (\<^bold>@ i p) at a in getBranch s) (sdrop (Suc m) steps)\<close>
    \<open>holds (\<lambda>s. (\<^bold>\<diamond> Nom i) at a in getBranch s) (sdrop (Suc m) steps)\<close>
    by auto
  moreover have \<open>alw (holds (\<lambda>l. p at a in getBranch l)
            impl nxt (holds (\<lambda>l. p at a in getBranch l))) steps\<close> for p
    using preservation_alw assms(1-2) .
  then have \<open>alw (holds (\<lambda>l. p at a in getBranch l)
        impl nxt (holds (\<lambda>l. p at a in getBranch l))) (sdrop (Suc m) steps)\<close> for p
    using alw_sdrop by blast
  ultimately have
    \<open>alw (holds (\<lambda>l. (\<^bold>@ i p) at a in getBranch l)) (sdrop (Suc m) steps)\<close>
    \<open>alw (holds (\<lambda>l. (\<^bold>\<diamond> Nom i) at a in getBranch l)) (sdrop (Suc m) steps)\<close>
    using alw_invar by blast+
  then have
    \<open>holds (\<lambda>l. (\<^bold>@ i p) at a in getBranch l) (sdrop n steps)\<close>
    \<open>holds (\<lambda>l. (\<^bold>\<diamond> Nom i) at a in getBranch l) (sdrop n steps)\<close>
    using \<open>m < n\<close> by (auto simp: alw_iff_sdrop elim: less_natE)
  then have \<open>holds (\<lambda>l. witnessed p a (getBranch l)) (sdrop n steps)\<close>
    unfolding witnessed_def by auto

  moreover have \<open>alw (holds (\<lambda>t. \<forall>a p i. getTag t = Fresh a p i \<longrightarrow>
    \<not> witnessed p a (getBranch t))) steps\<close>
    using Fresh_unwitnessed_ipath assms(1-2) .
  then have \<open>alw (holds (\<lambda>t. \<forall>a p i. getTag t = Fresh a p i \<longrightarrow>
    \<not> witnessed p a (getBranch t))) (sdrop n steps)\<close>
    by (simp add: alw_iff_sdrop)
  then have \<open>holds (\<lambda>t. \<not> witnessed q a (getBranch t)) (sdrop n steps)\<close>
    using assms(4, 7) by auto
  ultimately show ?thesis
    unfolding witnessed_def  by auto
qed

lemma labels_sset:
  assumes \<open>\<forall>l \<in> labels t. P l\<close> \<open>ipath t s\<close>
  shows \<open>\<forall>l \<in> sset s. P l\<close>
  using assms by (meson alw_sset alwt_ipath labels_alwt_holdst)

lemma finite_inj_preimage:
  assumes \<open>finite (f ` X)\<close> \<open>inj f\<close>
  shows \<open>finite X\<close>
  using assms by (meson finite.emptyI finite.insertI finite_vimageI inf_img_fin_dom)

lemma Fresh_determined_nominal:
  assumes \<open>wft A tab\<close> \<open>ipath tab steps\<close>
    \<open>Fresh a p i \<in> getTag ` sset steps\<close> \<open>Fresh a p i' \<in> getTag ` sset steps\<close>
  shows \<open>i = i'\<close>
proof -
  obtain m where m: \<open>getTag (steps !! m) = Fresh a p i\<close>
    using assms(3) sset_range by (metis image_iff)
  obtain n where n: \<open>getTag (steps !! n) = Fresh a p i'\<close>
    using assms(4) sset_range by (metis image_iff)

  consider (lt) \<open>m < n\<close> | (eq) \<open>m = n\<close> | (gt) \<open>n < m\<close>
    by linarith
  then show ?thesis
  proof cases
    case lt
    then show ?thesis
      using assms(1-2) m n distinct_Fresh by fast
  next
    case eq
    then show ?thesis
      using m n by simp
  next
    case gt
    then show ?thesis
      using assms(1-2) m n distinct_Fresh by fast
  qed
qed

lemma Fresh_determined_nominal_f:
  assumes \<open>wft A tab\<close> \<open>ipath tab steps\<close>
  shows \<open>\<exists>f. \<forall>p i. Fresh a p i \<in> getTag ` sset steps \<longrightarrow> f p = i\<close>
proof (intro exI allI impI)
  fix p i
  let ?f = \<open>\<lambda>p. THE i. Fresh a p i \<in> getTag ` sset steps\<close>
  assume \<open>Fresh a p i \<in> getTag ` sset steps\<close>
  then show \<open>?f p = i\<close>
    using assms Fresh_determined_nominal by fast
qed

lemma finite_Fresh_nominal:
  assumes \<open>wft A tab\<close> \<open>ipath tab steps\<close>
    \<open>finite {p |p i. Fresh a p i \<in> getTag ` sset steps}\<close>
  shows \<open>finite {i |p i. Fresh a p i \<in> getTag ` sset steps}\<close>
proof -
  obtain f where \<open>\<forall>p i. Fresh a p i \<in> getTag ` sset steps \<longrightarrow> f p = i\<close>
    using assms(1-2) Fresh_determined_nominal_f by metis
  then have \<open>{f p |p i. Fresh a p i \<in> getTag ` sset steps} =
      {i |p i. Fresh a p i \<in> getTag ` sset steps}\<close>
    by blast
  moreover have \<open>finite {f p |p i. Fresh a p i \<in> getTag ` sset steps}\<close>
    using assms(3) by simp
  ultimately show ?thesis
    by simp
qed

text \<open>The number of nominals generated by any fixed nominal is finite.\<close>

theorem generated_bound:
  assumes \<open>wft A tab\<close> \<open>ipath tab steps\<close>
  shows \<open>finite {(a, i) |p i. Fresh a p i \<in> getTag ` sset steps}\<close>
proof -
  let ?B = \<open>generated_ipath steps \<union> branch_nominals (getBranch (shd steps))\<close>
  let ?X = \<open>formula_bound ?B (getBranch (shd steps))\<close>
  let ?Y = \<open>propers ?X\<close>

  have \<open>alw (holds (\<lambda>step. \<forall>a p i. getTag step = Fresh a p i \<longrightarrow>
      (\<nexists>a. p = Nom a) \<and> (\<^bold>\<diamond> p) \<in> ?X)) steps\<close>
    using assms wft_introduces_quasis_ipath by blast
  then have \<open>\<forall>l \<in> sset steps. \<forall>p i. getTag l = Fresh a p i \<longrightarrow>
      (\<nexists>a. p = Nom a) \<and> (\<^bold>\<diamond> p) \<in> ?X\<close>
    by (smt alw_sset)
  then have \<open>\<forall>l \<in> sset steps. \<forall>p i. getTag l = Fresh a p i \<longrightarrow> (\<^bold>\<diamond> p) \<in> ?Y\<close>
    unfolding propers_def by blast
  moreover have \<open>finite ?Y\<close>
    using finite_propers_formula_bound  by blast
  ultimately have \<open>finite {\<^bold>\<diamond> p |p i. Fresh a p i \<in> getTag ` sset steps}\<close>
    by (smt finite_subset imageE mem_Collect_eq subsetI)
  moreover have \<open>Dia ` {p |p i. Fresh a p i \<in> getTag ` sset steps} \<subseteq>
      {\<^bold>\<diamond> p |p i. Fresh a p i \<in> getTag ` sset steps}\<close>
    by blast
  ultimately have \<open>finite (Dia ` {p |p i. Fresh a p i \<in> getTag ` sset steps})\<close>
    by (simp add: finite_subset)    
  moreover have \<open>inj Dia\<close>
    unfolding inj_def by blast
  ultimately have \<open>finite {p |p i. Fresh a p i \<in> getTag ` sset steps}\<close>
    using finite_inj_preimage by fast
  then have \<open>finite {i |p i. Fresh a p i \<in> getTag ` sset steps}\<close>
    using assms finite_Fresh_nominal by fast
  then have \<open>finite ({a} \<times> {i |p i. Fresh a p i \<in> getTag ` sset steps})\<close>
    by blast
  moreover have \<open>({a} \<times> {i |p i. Fresh a p i \<in> getTag ` sset steps}) =
      {(a, i) |p i. Fresh a p i \<in> getTag ` sset steps}\<close>
    by fast
  ultimately show ?thesis
    by simp
qed

(**********************************************************************************)

section \<open>CURRENT WORK\<close>

(* Ignoring Lemma 6.4 / 4.2 for a bit (finite set of well-founded, finitely branching trees) *)

(* Ignoring Lemma 6.5 for a bit (must be an infinite chain) *)


(* TODO: not currently used *)
definition set_to_list :: \<open>'a set \<Rightarrow> 'a list\<close> where
  \<open>set_to_list s = (SOME l. set l = s)\<close>

lemma set_set_to_list: \<open>finite s \<Longrightarrow> set (set_to_list s) = s\<close>
  unfolding set_to_list_def by (metis (mono_tags) finite_list some_eq_ex)

primcorec mkTree :: \<open>('b \<times> 'b) set \<Rightarrow> 'b \<Rightarrow> 'b tree\<close> where
  \<open>getLabel (mkTree T a) = a\<close>
| \<open>getSubs (mkTree T a) = map (mkTree T) (set_to_list {b. (a, b) \<in> T})\<close>

(*
    a      h    j
  b   c    i
  d  e f
     g
*)

(* Major TODO
  + We have that ipath \<Longrightarrow> infinite nominals generated on that ipath
  + We have that any root has a finite number of subtrees (generated_bound).
  
  - We need to show that infinite nominals on an ipath means an infinite chain
  - We need to show the decreasing measure
*)

subsection \<open>Measure\<close>

lemma woop1:
  assumes \<open>ipath tab steps\<close> \<open>wft A tab\<close>
    \<open>Fresh b t c \<in> getTag ` sset steps\<close> (* b < c *)
    \<open>(holds (\<lambda>step. \<forall>r'. r' at c in getBranch step \<longrightarrow> size r' \<le> size r) impl
     (holds (\<lambda>step. \<exists>r'. r' at b in getBranch step \<and> size r < size r'))) steps\<close>
  shows \<open>alw
    (holds (\<lambda>step. \<forall>r'. r' at c in getBranch step \<longrightarrow> size r' \<le> size r) impl
    (holds (\<lambda>step. \<exists>r'. r' at b in getBranch step \<and> size r < size r'))) steps\<close>
  using assms
proof (coinduction arbitrary: tab steps)
  case alw
  then show ?case
  proof cases
    case (IPath s' subs tail l)
    then have wft: \<open>wft A s'\<close>
      using alw(2) wft_alwt by (auto elim: wft.cases)
    from alw(2) show ?thesis
    proof cases
      case (WfClose p i branch n)
      then show ?thesis
        using IPath(1-2) alw(1-2) alw_holds ipath_Open_Close
        by (metis (mono_tags, lifting) step.sel(1) tree.inject)
    next
      case (WfOpen branch n)
      then show ?thesis
        using IPath(1-2) alw(1-2) alw_holds ipath_Open_Close
        by (metis (mono_tags, lifting) step.sel(1) tree.inject)
    next
      case (WfNeg p a ps branch s n)
      then have the: ?thesis if
        \<open>(\<forall>r'. r' at c in getBranch (shd tail) \<longrightarrow> size r' \<le> size r) \<longrightarrow>
         (\<exists>r'. r' at b in getBranch (shd tail) \<and> size r < size r')\<close>
        using that alw IPath by auto

      have *:
        \<open>(\<forall>r'. r' at c in getBranch l \<longrightarrow> size r' \<le> size r) \<longrightarrow>
         (\<exists>r'. r' at b in getBranch l \<and> size r < size r')\<close>
        using IPath(2) alw(4) by auto

      have \<open>getBranch (shd tail) = (p # ps, a) # branch\<close>
        using IPath(1, 3-4) WfNeg(1, 4) by (fastforce elim: ipath.cases)
      moreover have \<open>getBranch l = (ps, a) # branch\<close>
        using IPath(1) WfNeg(1) by auto
      moreover note \<open>(\<^bold>\<not> \<^bold>\<not> p) at a in (ps, a) # branch\<close>
      moreover have \<open>size p \<le> size (\<^bold>\<not> \<^bold>\<not> p)\<close>
        by simp
      ultimately have **: \<open>\<forall>r'. r' at c in getBranch (shd tail) \<longrightarrow>
          (\<exists>r''. r'' at c in getBranch l \<and> size r' \<le> size r'')\<close>
        \<open>\<forall>r'. r' at c in getBranch l \<longrightarrow>
          (\<exists>r''. r'' at c in getBranch (shd tail) \<and> size r' \<le> size r'')\<close>
        by (metis (no_types, opaque_lifting) list.set_intros(1-2) on.simps order_refl prod.inject
            set_ConsD)+

      {
        assume assm: \<open>\<forall>r'. r' at c in getBranch (shd tail) \<longrightarrow> size r' \<le> size r\<close>
        then have \<open>\<forall>r'. r' at c in getBranch (shd tail) \<longrightarrow>
            (\<exists>r''. r'' at c in getBranch l \<and> size r' \<le> size r'')\<close>
          using **(1) by blast
        then have \<open>\<forall>r'. r' at c in getBranch l \<longrightarrow> size r' \<le> size r\<close>
          using **(2) assm by (meson le_trans)
        then have \<open>\<exists>r'. r' at b in getBranch l \<and> size r < size r'\<close>
          using * by blast
        then have \<open>\<exists>r'. r' at b in getBranch (shd tail) \<and> size r < size r'\<close>
          using \<open>getBranch (shd tail) = (p # ps, a) # branch\<close> \<open>getBranch l = (ps, a) # branch\<close> 
          by (metis list.set_intros(1-2) on.simps prod.inject set_ConsD)
      }
      then show ?thesis
        using the by blast
    next
      case (WfDisP p q a ps branch sl n sr)
      then show ?thesis sorry
    next
      case (WfDisN p q a ps branch s n intro)
      then show ?thesis sorry
    next
      case (WfDiaP p a ps branch i s n)
      then show ?thesis sorry
    next
      case (WfDiaN p a ps branch i s n)
      then show ?thesis sorry
    next
      case (WfSatP a p b ps branch s n)
      then show ?thesis sorry
    next
      case (WfSatN a p b ps branch s n)
      then show ?thesis sorry
    next
      case (WfGoTo i branch s n)
      then show ?thesis sorry
    next
      case (WfNom p b ps a branch s n)
      then show ?thesis sorry
    qed
  qed
qed

(* tricky to show this directly by coinduction since we lack the assumption
   but it should hold and it's what we want *)
(* c is generated, so there cannot be any c blocks initially *)
lemma woop2:
  assumes \<open>ipath tab steps\<close> \<open>wft A tab\<close>
    \<open>Fresh b t c \<in> getTag ` sset steps\<close> (* b < c *)
  shows \<open>alw (holds (\<lambda>step. \<exists>r. r at b in getBranch step \<and>
      (\<forall>r'. r' at c in getBranch step \<longrightarrow> size r' < size r))) steps\<close>
  using assms
proof (coinduction arbitrary: tab steps)
  case alw
  then show ?case
  proof cases
    case (IPath s' subs tail l)
    then have wft: \<open>wft A s'\<close>
      using alw(2) wft_alwt by (auto elim: wft.cases)
    from alw(2) show ?thesis
    proof cases
      case (WfClose p i branch n)
      then show ?thesis
        using IPath(1, 3) by simp
    next
      case (WfOpen branch n)
      then show ?thesis
        using IPath(1, 3) by simp
    next
      case (WfNeg p a ps branch s n)
      then show ?thesis
        sorry
    next
      case (WfDisP p q a ps branch sl n sr)
      then show ?thesis sorry
    next
      case (WfDisN p q a ps branch s n intro)
      then show ?thesis sorry
    next
      case (WfDiaP p a ps branch i s n)
      then show ?thesis sorry
    next
      case (WfDiaN p a ps branch i s n)
      then show ?thesis sorry
    next
      case (WfSatP a p b ps branch s n)
      then show ?thesis sorry
    next
      case (WfSatN a p b ps branch s n)
      then show ?thesis sorry
    next
      case (WfGoTo i branch s n)
      then show ?thesis sorry
    next
      case (WfNom p b ps a branch s n)
      then show ?thesis sorry
    qed
  qed
qed

text \<open>
  There is an infinite chain of generated nominals starting with i if
  within some prefix, i generates j and the remaining suffix has a chain from j.
\<close>
coinductive infgen :: \<open>'b \<Rightarrow> ('a, 'b) step stream \<Rightarrow> bool\<close> where
  InfGen: \<open>Fresh i p j \<in> getTag ` set (stake n xs) \<Longrightarrow>
   infgen j (sdrop n xs) \<Longrightarrow>
   infgen i xs\<close>

text \<open>Version that gives us the stream of nominals.\<close>
coinductive infgens :: \<open>'b stream \<Rightarrow> ('a, 'b) step stream \<Rightarrow> bool\<close> where
  InfGens: \<open>Fresh i p j \<in> getTag ` set (stake n xs) \<Longrightarrow>
   infgens (j ## bs) (sdrop n xs) \<Longrightarrow>
   infgens (i ## j ## bs) xs\<close>

(*
  Branch: step step step step
  Some steps are the generation of a nominal
  We know that an infinite branch must have an infinite number of nominals
  We will also show that they must form a chain

  Assume we have such a chain in our branch
  We will show that each generated nominal has smaller formulas on it
  This leads to an infinite descent in formula size
  This is a contradiction
*)

definition fms_at :: \<open>'b \<Rightarrow> ('a, 'b) step stream \<Rightarrow> ('a, 'b) fm set\<close> where
  \<open>fms_at i steps \<equiv> {p |p step. step \<in> sset steps \<and> p at i in getBranch step}\<close>

(* TODO: need quasi-root lemmas to show this, I guess *)
lemma finite_size_fms_at:
  assumes \<open>ipath tab steps\<close> \<open>wft A tab\<close>
  shows \<open>finite (size ` fms_at i steps)\<close>
  sorry

definition M_branch :: \<open>'b \<Rightarrow> ('a, 'b) step stream \<Rightarrow> nat\<close> where
  \<open>M_branch i steps \<equiv> Max (size ` fms_at i steps)\<close>

lemma M_branch_le:
  assumes \<open>p \<in> fms_at i steps\<close> \<open>\<forall>q. q \<in> fms_at i steps \<longrightarrow> size q \<le> size p\<close>
  shows \<open>M_branch i steps = size p\<close>
  using assms unfolding M_branch_def (* TODO: smt *)
  by (smt (verit, del_insts) Max_eqI finite_nat_set_iff_bounded_le image_iff)

(*
  Imagine we have the whole branch in front of us.
  Then we consider a maximal element at c.
  We see what introduced it.
  In each case, we show that there is a bigger element at b.
  
  What kind of principle is this?
  
  Assume it holds.
  Show it keeps holding under extensions.
  alw P steps?
  But P references all of steps

*)

(*
    \<open>(holds (\<lambda>step. \<forall>r'. r' at c in getBranch step \<longrightarrow> size r' \<le> size r) impl
     (holds (\<lambda>step. \<exists>r'. r' at b in getBranch step \<and> size r < size r'))) steps\<close>
  shows \<open>alw
    (holds (\<lambda>step. \<forall>r'. r' at c in getBranch step \<longrightarrow> size r' \<le> size r) impl
    (holds (\<lambda>step. \<exists>r'. r' at b in getBranch step \<and> size r < size r'))) steps\<close>

this isn't good for going to the global M_branch we need for the descent

alw (\<forall>r. r at c in getBranch step \<longrightarrow> size r < M_branch b steps) steps
*)

lemma fms_at_SCons: \<open>fms_at i xs \<subseteq> fms_at i (x ## xs)\<close>
  unfolding fms_at_def by auto

lemma M_branch_SCons: \<open>M_branch i xs \<le> M_branch i (x ## xs)\<close>
  unfolding M_branch_def using fms_at_SCons finite_size_fms_at sorry
    (* TODO: ipath tab xs of wft tab *)

lemma zoop1':
  assumes \<open>ipath tab steps\<close> \<open>wft A tab\<close>
    \<open>M_branch c steps \<le> x\<close>
  shows \<open>alw (holds (\<lambda>step. \<forall>r. r at c in getBranch step \<longrightarrow> size r \<le> x)) steps\<close>
  using assms
proof (coinduction arbitrary: tab steps)
  case alw
  then show ?case
  proof cases
    case (IPath s' subs tail l)
    then have wft: \<open>wft A s'\<close>
      using alw(2) wft_alwt by (auto elim: wft.cases)
    from alw(2) show ?thesis
    proof cases
      case (WfClose p i branch n)
      then show ?thesis
        using IPath(1, 3) by simp
    next
      case (WfOpen branch n)
      then show ?thesis
        using IPath(1, 3) by simp
    next
      case (WfNeg p a ps branch s n)
      then have ?thesis if
        \<open>\<forall>r. r at c in (ps, a) # branch \<longrightarrow> size r \<le> x\<close>
        \<open>M_branch c tail \<le> x\<close>
        using that IPath(1-2, 4) wft by auto
      
      moreover have \<open>M_branch c tail \<le> x\<close>
        using alw(3) IPath(2) M_branch_SCons by (metis dual_order.trans)

      moreover from alw(3) have \<open>\<forall>r \<in> fms_at c steps. size r \<le> x\<close>
        unfolding M_branch_def using alw(1-2) finite_size_fms_at
        by (metis Max_ge dual_order.trans image_eqI)
      then have \<open>\<forall>r. r at c in (ps, a) # branch \<longrightarrow> size r \<le> x\<close>
        unfolding fms_at_def using IPath(1-2) WfNeg(1) by fastforce

      ultimately show ?thesis
        by blast
    next
      case (WfDisP p q a ps branch sl n sr)
      then show ?thesis sorry
    next
      case (WfDisN p q a ps branch s n intro)
      then show ?thesis sorry
    next
      case (WfDiaP p a ps branch i s n)
      then show ?thesis sorry
    next
      case (WfDiaN p a ps branch i s n)
      then show ?thesis sorry
    next
      case (WfSatP a p b ps branch s n)
      then show ?thesis sorry
    next
      case (WfSatN a p b ps branch s n)
      then show ?thesis sorry
    next
      case (WfGoTo i branch s n)
      then show ?thesis sorry
    next
      case (WfNom p b ps a branch s n)
      then show ?thesis sorry
    qed
  qed
qed

(* Trying to work out how to formulate the a < b \<longrightarrow> m b < m a lemma in a way we can prove *)

lemma zoop1:
  assumes \<open>ipath tab steps\<close> \<open>wft A tab\<close>
  shows \<open>alw (holds (\<lambda>step. \<forall>p. p at i in getBranch step \<longrightarrow> size p \<le> M_branch i steps)) steps\<close>
  using assms zoop1' by fast

lemma zoop2:
  assumes \<open>ipath tab steps\<close> \<open>wft A tab\<close>
    \<open>Fresh b t c \<in> getTag ` sset steps\<close> (* b < c *)
    \<open>M_branch b steps \<le> bmax\<close>
  shows \<open>alw (holds (\<lambda>step. \<forall>r. r at c in getBranch step \<longrightarrow> size r < bmax)) steps\<close>
  (* idea, don't look at a max c-formula, just look at all of them, at all steps.
    we can add that it holds initially if we need to (probably do)
    This gives us something suitable for the coinduction principle

    We need to then bound it by M_branch c steps afterwards
    And the bound needs to be tight so it doesn't surpass bmax
    But the bound is only tight in the limit, not at each step

    
    at each step, a local (varying) measure is smaller than a global (constant) measure
    l c < m b
    l c \<le> m c
    I need m c < m b
  *)
  sorry

(* the induction principle is local but the measure is global

  I need to look at a largest formula and see what rule introduced it.

  No matter what largest c-formula you look at,
  by looking at what introduced it,
  you can point to a larger b-formula
  when b < c


  Let's say we show the local property:
    at all steps, all c-formulas are smaller than bmax

  Then we get a property about each step.
  But the measure is defined across the steps.
  So we need to show
  - Each step is at most the measure (should be possible)
  - There is a step equal to the measure
  So we get a tight bound.
*)


lemma zoop1a:
  assumes \<open>ipath tab steps\<close> \<open>wft A tab\<close>
  shows \<open>ev (holds (\<lambda>step. \<exists>p. p at i in getBranch step \<and> M_branch i steps \<le> size p)) steps\<close>
  sorry



lemma zoop3:
  assumes \<open>ipath tab steps\<close> \<open>wft A tab\<close>
    \<open>Fresh b t c \<in> getTag ` sset steps\<close> (* b < c *)
    \<open>M_branch b steps \<le> bmax\<close>
  shows \<open>alw (holds (\<lambda>step. M_branch c steps < bmax)) steps\<close>
proof -
  have \<open>alw (holds (\<lambda>step. \<forall>r. r at c in getBranch step \<longrightarrow> size r < bmax)) steps\<close>
    using assms zoop2 by fast
  then have *: \<open>\<forall>step \<in> sset steps. \<forall>r. r at c in getBranch step \<longrightarrow> size r < bmax\<close>
    using alw_sset by (metis (mono_tags, lifting))
  
  have
    \<open>alw (holds (\<lambda>step. \<forall>p. p at c in getBranch step \<longrightarrow> size p \<le> M_branch c steps)) steps\<close>
    using assms zoop1 by fast
  then have **:
    \<open>\<forall>step \<in> sset steps. \<forall>p. p at c in getBranch step \<longrightarrow> size p \<le> M_branch c steps\<close>
    using alw_sset by (metis (mono_tags, lifting))

  have \<open>\<forall>step \<in> sset steps. M_branch c steps \<le> bmax\<close>
  proof
    fix step
    assume step: \<open>step \<in> sset steps\<close>
    then have \<open>\<forall>r. r at c in getBranch step \<longrightarrow> size r < bmax\<close>
      using * by blast
    moreover have \<open>\<forall>r. r at c in getBranch step \<longrightarrow> size r \<le> M_branch c steps\<close>
      using step ** by blast
    ultimately show \<open>M_branch c steps \<le> bmax\<close>
      (* this makes no sense *)
      sorry
  qed
  then show ?thesis
    sorry
qed

lemma
  assumes \<open>ipath tab steps\<close> \<open>wft A tab\<close>
    \<open>Fresh b t c \<in> getTag ` sset steps\<close> (* b < c *)
    \<open>pc \<in> fms_at c steps\<close> \<open>\<forall>q. q \<in> fms_at c steps \<longrightarrow> size q \<le> size pc\<close> (* pc max at c *)
  shows \<open>size pc < M_branch b steps\<close>
  using assms
proof cases
  case (IPath s' subs tail l)
  then have wft: \<open>wft A s'\<close>
    using assms(2) wft_alwt by (auto elim: wft.cases)
  from assms(2) show ?thesis
  proof cases
    case (WfClose p i branch n)
    then show ?thesis
      using IPath(1, 3) by simp
  next
    case (WfOpen branch n)
    then show ?thesis
      using IPath(1, 3) by simp
  next
    case (WfNeg p a ps branch s n)
    then show ?thesis
      using IPath assms(3-) sorry
        (* if p = pc then \<not> \<not> p is bigger. Contradiction *)
        (* otherwise we need to know the thesis held before the extension *)
  next
    case (WfDisP p q a ps branch sl n sr)
    then show ?thesis sorry
  next
    case (WfDisN p q a ps branch s n intro)
    then show ?thesis sorry
  next
    case (WfDiaP p a ps branch i s n)
    then show ?thesis sorry
  next
    case (WfDiaN p a ps branch i s n)
    then show ?thesis sorry
  next
    case (WfSatP a p b ps branch s n)
    then show ?thesis sorry
  next
    case (WfSatN a p b ps branch s n)
    then show ?thesis sorry
  next
    case (WfGoTo i branch s n)
    then show ?thesis sorry
  next
    case (WfNom p b ps a branch s n)
    then show ?thesis sorry
  qed
qed


(* TODO: this is what we want for the infinite descent, question is how easy it is to prove *)
lemma woop4:
  assumes \<open>ipath tab steps\<close> \<open>wft A tab\<close>
    \<open>Fresh b t c \<in> getTag ` sset steps\<close> (* b < c *)
  shows \<open>M_branch c steps < M_branch b steps\<close>
  using assms
proof cases
  case (IPath s' subs tail l)
  then have wft: \<open>wft A s'\<close>
    using assms(2) wft_alwt by (auto elim: wft.cases)
  from assms(2) show ?thesis
  proof cases
    case (WfClose p i branch n)
    then show ?thesis
      using IPath(1, 3) by simp
  next
    case (WfOpen branch n)
    then show ?thesis
      using IPath(1, 3) by simp
  next
    case (WfNeg p a ps branch s n)
    then show ?thesis
      unfolding M_branch_def
      using IPath (* we lack inductive knowledge to build on *)
      sorry
  next
    case (WfDisP p q a ps branch sl n sr)
    then show ?thesis sorry
  next
    case (WfDisN p q a ps branch s n intro)
    then show ?thesis sorry
  next
    case (WfDiaP p a ps branch i s n)
    then show ?thesis sorry
  next
    case (WfDiaN p a ps branch i s n)
    then show ?thesis sorry
  next
    case (WfSatP a p b ps branch s n)
    then show ?thesis sorry
  next
    case (WfSatN a p b ps branch s n)
    then show ?thesis sorry
  next
    case (WfGoTo i branch s n)
    then show ?thesis sorry
  next
    case (WfNom p b ps a branch s n)
    then show ?thesis sorry
  qed
qed

lemma ne_sset: \<open>sset steps \<noteq> {}\<close>
  by (cases steps) auto

lemma fms_at_sdrop: \<open>fms_at i (sdrop n steps) \<subseteq> fms_at i steps\<close>
  unfolding fms_at_def (* TODO: smt *)
  by (smt (verit) Collect_mono sdrop_add sdrop_simps(1) snth_sset sset_sdrop)

lemma M_branch_sdrop: \<open>M_branch i (sdrop n steps) \<le> M_branch i steps\<close>
  unfolding M_branch_def using fms_at_sdrop sorry

lemma ipath_infgens':
  assumes \<open>ipath tab steps\<close> \<open>wft A tab\<close> \<open>infgens bs steps\<close>
    (* TODO: derive some infgens from ipath *)
    \<open>M_branch (shd bs) steps < r\<close> \<comment> \<open>to less-induct on a natural number (r)\<close>
  shows \<open>False\<close>
  using assms
proof (induct r arbitrary: tab bs steps rule: less_induct)
  case (less x)
  from less(4) show ?case
  proof cases
    case (InfGens i p j n bs')
    then have \<open>Fresh i p j \<in> getTag ` sset steps\<close>
      using stake_snth by fastforce
    then have \<open>M_branch j steps < M_branch i steps\<close>
      using less(2-3) woop4 by fast
    then have \<open>M_branch j (sdrop n steps) < M_branch i steps\<close>
      using M_branch_sdrop by (metis le_less_trans)
    then have \<open>M_branch j (sdrop n steps) < M_branch (shd bs) steps\<close>
      using InfGens(1) by simp
    moreover note \<open>infgens (j ## bs') (sdrop n steps)\<close> \<open>M_branch (shd bs) steps < x\<close>
    moreover obtain t where \<open>wft A t\<close> \<open>ipath t (sdrop n steps)\<close>
      using less(2-3) wft_ipath_sdrop by blast
    ultimately show False
      using less(1) by fastforce    
  qed
qed

theorem ipath_infgens:
  assumes \<open>ipath tab steps\<close> \<open>wft A tab\<close>
  shows \<open>\<not> infgens bs steps\<close>
  using assms ipath_infgens' by fast

(*
  m turns a branch and a nominal into a natural number
  then we less_induct on that number
*)

section \<open>THINGS I MAY NOT NEED\<close>

(* TODO: I don't think we actually need the whole (q)subfm machinery, just quasis. *)

primrec subfm :: \<open>('a, 'b) fm \<Rightarrow> ('a, 'b) fm \<Rightarrow> bool\<close> where
  \<open>subfm p (Pro x) = (p = Pro x)\<close>
| \<open>subfm p (Nom a) = (p = Nom a)\<close>
| \<open>subfm p (\<^bold>\<not> q) = (p = (\<^bold>\<not> q) \<or> subfm p q)\<close>
| \<open>subfm p (q \<^bold>\<or> r) = (p = (q \<^bold>\<or> r) \<or> subfm p q \<or> subfm p r)\<close>
| \<open>subfm p (\<^bold>\<diamond> q) = (p = (\<^bold>\<diamond> q) \<or> subfm p q)\<close>
| \<open>subfm p (\<^bold>@ i q) = (p = (\<^bold>@ i q) \<or> p = Nom i \<or> subfm p q)\<close>

lemma subfm_refl [simp]: \<open>subfm p p\<close>
  by (cases p) simp_all

lemma subfm_trans: \<open>subfm p q \<Longrightarrow> subfm q r \<Longrightarrow> subfm p r\<close>
  by (induct r) auto

lemma subfm_reflp: \<open>reflp subfm\<close>
  unfolding reflp_def by simp

lemma subfm_transp: \<open>transp subfm\<close>
  unfolding transp_def using subfm_trans by blast

lemma nominals_subfm [simp]: \<open>i \<in> nominals p \<Longrightarrow> subfm (Nom i) p\<close>
  by (induct p) auto

inductive qsubfm :: \<open>('a, 'b) fm \<Rightarrow> ('a, 'b) fm \<Rightarrow> bool\<close> where
  (* q is fixed but to express that, I need to put it first which would be annoying *)
  PureSub: \<open>subfm p q \<Longrightarrow> qsubfm p q\<close>
| NegPSub: \<open>subfm p q \<Longrightarrow> qsubfm (\<^bold>\<not> p) q\<close>
| SatPSub: \<open>subfm p q \<Longrightarrow> qsubfm (\<^bold>@ i p) q\<close>
| SatNSub: \<open>subfm p q \<Longrightarrow> qsubfm (\<^bold>\<not> (\<^bold>@ i p)) q\<close>

lemma qsubfm_reflp: \<open>reflp qsubfm\<close>
  unfolding reflp_def by (simp add: PureSub)

lemma quasis_qsubfm: \<open>p' \<in> quasis A p \<Longrightarrow> qsubfm p' p \<and> size p' \<le> size p\<close>
  by (induct p arbitrary: p' rule: quasis.induct)
    (fastforce simp: qsubfm.intros elim: qsubfm.cases split: if_splits)+

subsection \<open>Distinct branches\<close>

lemma fin_finite_branches:
  assumes \<open>fin tab\<close> \<open>wft A tab\<close>
  shows \<open>finite (getBranch ` labels tab)\<close>
  using assms by induct (fastforce simp: image_UN elim: wft.cases)

corollary infinite_branches_infin:
  assumes \<open>infinite (getBranch ` labels tab)\<close> \<open>wft A tab\<close>
  shows \<open>infin tab\<close>
  using assms fin_finite_branches by blast

definition nformulas :: \<open>('a, 'b) branch \<Rightarrow> nat\<close> where
  \<open>nformulas branch \<equiv> sum_list (map (Suc o length o fst) branch)\<close>

lemma alwt_nformulas:
  assumes \<open>wft A tab\<close> \<open>nformulas branch' < nformulas (getBranch (getLabel tab))\<close>
  shows \<open>alwt (holdst (\<lambda>step. nformulas branch' < nformulas (getBranch step))) tab\<close>
  using assms unfolding nformulas_def
  by (coinduction arbitrary: tab) (fastforce elim: wft.cases)

lemma nformulas_subs:
  assumes \<open>wft A (Node l subs)\<close> \<open>s \<in> set subs\<close>
  shows \<open>nformulas (getBranch l) < nformulas (getBranch (getLabel s))\<close>
  using assms unfolding nformulas_def by (fastforce elim: wft.cases)

(* TODO: may not be useful *)
lemma wft_potential_bound:
  assumes
    \<open>wft A tab\<close>
    \<open>getPotential (getLabel tab) \<le> start + nformulas (getBranch (getLabel tab))\<close>
  shows \<open>alwt (holdst (\<lambda>step. getPotential step \<le> start + nformulas (getBranch step))) tab\<close>
  using assms unfolding nformulas_def
  by (coinduction arbitrary: tab) (fastforce elim: wft.cases)

subsection \<open>Preservation\<close>

abbreviation preserved :: \<open>('a, 'b) branch \<Rightarrow> ('a, 'b) branch \<Rightarrow> bool\<close> where
  \<open>preserved branch branch' \<equiv> \<forall>p b. p at b in branch \<longrightarrow> p at b in branch'\<close>

lemma alwt_preservation':
  assumes \<open>wft A tab\<close> \<open>preserved branch' (getBranch (getLabel tab))\<close>
  shows \<open>alwt (holdst (\<lambda>step. preserved branch' (getBranch step))) tab\<close>
  using assms
proof (coinduction arbitrary: tab)
  case alwt
  then show ?case
  proof cases
    case (WfNeg p a ps branch s n)
    from this(1, 4, 6) show ?thesis
      using alwt(2) by fastforce
  next
    case (WfDisP p q a ps branch sl n sr)
    from this(1, 5, 7, 9-10) show ?thesis
      using alwt(2) by fastforce
  next
    case (WfDisN p q a ps branch s n)
    from this(1, 4, 6) show ?thesis
      using alwt(2) by fastforce
  next
    case (WfDiaP p a ps branch i s n)
    from this(1, 6, 8) show ?thesis
      using alwt(2) by fastforce
  next
    case (WfDiaN p a ps branch i s n)
    from this(1, 5, 7) show ?thesis
      using alwt(2) by fastforce
  next
    case (WfSatP a p b ps branch s n)
    from this(1, 4, 6) show ?thesis
      using alwt(2) by fastforce
  next
    case (WfSatN a p b ps branch s n)
    from this(1, 4, 6) show ?thesis
      using alwt(2) by fastforce
  next
    case (WfNom p b ps a branch s n)
    from this(1, 6, 8) show ?thesis
      using alwt(2) by fastforce
  qed auto
qed

lemma alwt_preservation:
  assumes \<open>wft A tab\<close>
  shows \<open>alwt (holdst (\<lambda>step. preserved (getBranch (getLabel tab)) (getBranch step))) tab\<close>
  using assms alwt_preservation' by blast

corollary alwt_preservation_subs:
  assumes \<open>wft A tab\<close> \<open>s \<in> set (getSubs tab)\<close>
  shows \<open>alwt (holdst (\<lambda>step. preserved (getBranch (getLabel tab)) (getBranch step))) s\<close>
  using assms alwt_preservation by (fastforce elim: alwt.cases)

lemma reflp_preserved: \<open>reflp preserved\<close>
  unfolding reflp_def by simp

lemma transp_preserved: \<open>transp preserved\<close>
  unfolding transp_def by simp

end