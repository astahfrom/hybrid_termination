theory Trees imports "HOL-Library.Linear_Temporal_Logic_on_Streams" begin

(* TODO: find a shorter naming convention for selectors? *)

(* TODO: maybe the property should go last in alwt etc. "alwt tab P" *)

(* TODO: would it be nicer to use fsets than lists for the subs? *)

codatatype (labels: 'a) tree = Node (getLabel: 'a) (getSubs: \<open>'a tree list\<close>)
  for map: tmap

lemmas tmap_simps[simp] = tree.map_sel
lemmas getLabel_labels = tree.set_sel(1)
lemmas getSubs_labels = tree.set_sel(2)

section \<open>Trees over fixed sets of labels\<close>

coinductive_set
  trees :: "'a set \<Rightarrow> 'a tree set"
  for A :: "'a set"
where
  Tree[intro, simp, no_atp]: \<open>\<lbrakk>l \<in> A; \<forall>s \<in> set subs. s \<in> trees A\<rbrakk> \<Longrightarrow> Node l subs \<in> trees A\<close>

lemma in_trees: \<open>\<forall>s \<in> set (getSubs t). s \<in> trees A \<Longrightarrow> getLabel t \<in> A \<Longrightarrow> t \<in> trees A\<close>
  by (cases t) simp_all

lemma treesE: \<open>t \<in> trees A \<Longrightarrow> (getLabel t \<in> A \<Longrightarrow> \<forall>s \<in> set (getSubs t). s \<in> trees A \<Longrightarrow> P) \<Longrightarrow> P\<close>
  by (auto elim: trees.cases)

lemma Trees_image: \<open>Node x y \<in> (Node x') ` Y \<longleftrightarrow> x = x' \<and> y \<in> Y\<close>
  by auto

lemma trees_Trees: \<open>Node l subs \<in> trees A \<longleftrightarrow> l \<in> A \<and> (\<forall>s \<in> set subs. s \<in> trees A)\<close>
  by (auto elim: trees.cases)

lemma labels_trees:
  assumes \<open>labels t \<subseteq> A\<close>
  shows \<open>t \<in> trees A\<close>
  using assms
proof (coinduction arbitrary: t)
  case trees then show ?case by (cases t) auto
qed

lemma trees_labels:
  assumes \<open>t \<in> trees A\<close>
  shows \<open>labels t \<subseteq> A\<close>
proof
  fix l
  assume \<open>l \<in> labels t\<close>
  then show \<open>l \<in> A\<close>
    using \<open>t \<in> trees A\<close> by (induct t) (auto elim: treesE)
qed

lemma trees_iff_labels: \<open>t \<in> trees A \<longleftrightarrow> labels t \<subseteq> A\<close>
  by (metis labels_trees trees_labels)

lemma trees_mono: \<open>t \<in> trees A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> t \<in> trees B\<close>
  unfolding trees_iff_labels by auto

lemma trees_mono2: \<open>S \<subseteq> T \<Longrightarrow> trees S \<subseteq> trees T\<close>
  by (auto intro: trees_mono)

lemma tmap_trees: \<open>t \<in> trees A \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x \<in> B) \<Longrightarrow> tmap f t \<in> trees B\<close>
  unfolding trees_iff_labels tree.set_map by fast

lemma streams_empty: \<open>trees {} = {}\<close>
  by (auto elim: trees.cases)

lemma streams_UNIV[simp]: \<open>trees UNIV = UNIV\<close>
  by (auto simp: trees_iff_labels)

section \<open>Finite trees and infinite paths\<close>

inductive fin :: \<open>'a tree \<Rightarrow> bool\<close> where
  Fin: \<open>\<forall>s \<in> set subs. fin s \<Longrightarrow> fin (Node l subs)\<close>

abbreviation infin :: \<open>'a tree \<Rightarrow> bool\<close> where
  \<open>infin x \<equiv> \<not> fin x\<close>

coinductive ipath :: \<open>'a tree \<Rightarrow> 'a stream \<Rightarrow> bool\<close> where
  IPath: \<open>s \<in> set subs \<Longrightarrow> ipath s tail \<Longrightarrow> ipath (Node l subs) (l ## tail)\<close>

lemma fin_no_ipath: \<open>fin tab \<Longrightarrow> \<not> ipath tab path\<close>
  by (induct tab arbitrary: path rule: fin.induct) (auto elim: ipath.cases)

lemma infin_sub: \<open>infin tab \<Longrightarrow> \<exists>s \<in> set (getSubs tab). infin s\<close>
  using Fin by (metis tree.exhaust_sel)

primcorec get_ipath :: \<open>'a tree \<Rightarrow> 'a stream\<close> where
  \<open>shd (get_ipath t) = getLabel t\<close>
| \<open>stl (get_ipath t) = get_ipath (SOME s. s \<in> set (getSubs t) \<and> infin s)\<close>

lemma ipath: \<open>infin tab \<Longrightarrow> ipath tab (get_ipath tab)\<close>
  by (coinduction arbitrary: tab)
    (metis (no_types, lifting) get_ipath.code infin_sub someI_ex tree.exhaust_sel)

corollary \<open>\<nexists>path. ipath tab path \<Longrightarrow> fin tab\<close>
  using ipath by blast

section \<open>Properties Inherited by Paths\<close>

datatype 'a rel
  = Here \<open>'a \<Rightarrow> bool\<close>
  | Next \<open>'a rel\<close>
  | Also \<open>'a rel\<close> \<open>'a rel\<close>
  | Impl \<open>'a \<Rightarrow> bool\<close> \<open>'a rel\<close>

primrec relt :: \<open>'a rel \<Rightarrow> 'a tree \<Rightarrow> bool\<close> where
  \<open>relt (Here P) t = P (getLabel t)\<close>
| \<open>relt (Next r) t = (\<forall>s \<in> set (getSubs t). relt r s)\<close>
| \<open>relt (Also r r') = relt r aand relt r'\<close>
| \<open>relt (Impl P r) = (P o getLabel) impl relt r\<close>

primrec rels :: \<open>'a rel \<Rightarrow> 'a stream \<Rightarrow> bool\<close> where
  \<open>rels (Here P) = holds P\<close>
| \<open>rels (Next r) = nxt (rels r)\<close>
| \<open>rels (Also r r') = rels r aand rels r'\<close>
| \<open>rels (Impl P r) = holds P impl rels r\<close>

lemma relt_ipath:
  assumes \<open>relt r t\<close> \<open>ipath t s\<close>
  shows \<open>rels r s\<close>
  using assms
  by (induct r arbitrary: t s) (fastforce elim: ipath.cases)+

section \<open>Trees where every subtree satisfies a property.\<close>

coinductive alwt :: \<open>('a tree \<Rightarrow> bool) \<Rightarrow> 'a tree \<Rightarrow> bool\<close> where
  AlwT: \<open>P t \<Longrightarrow> \<forall>s \<in> set (getSubs t). alwt P s \<Longrightarrow> alwt P t\<close>

abbreviation holdst :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a tree \<Rightarrow> bool\<close> where
  \<open>holdst P t \<equiv> P (getLabel t)\<close>

lemma alwt_holdst_trees: \<open>alwt (holdst P) t \<Longrightarrow> t \<in> trees (Collect P)\<close>
  by (coinduction arbitrary: t) (metis mem_Collect_eq alwt.cases tree.collapse)

lemma trees_alwt: \<open>t \<in> trees (Collect P) \<Longrightarrow> alwt (holdst P) t\<close>
  by (coinduction arbitrary: t) (auto elim: trees.cases)

lemma alwt_holdst_labels: \<open>alwt (holdst P) t \<Longrightarrow> l \<in> labels t \<Longrightarrow> P l\<close>
  using alwt_holdst_trees trees_labels by blast

lemma labels_alwt_holdst: \<open>\<forall>l \<in> labels t. P l \<Longrightarrow> alwt (holdst P) t\<close>
  by (simp add: trees_alwt Ball_Collect labels_trees)

corollary labels_alwt': \<open>alwt (holdst (\<lambda>n. n \<in> labels t)) t\<close>
  using labels_alwt_holdst by fast

lemma alwt_True: \<open>alwt (\<lambda>_. True) t\<close>
  by (coinduction arbitrary: t) simp_all

subsection \<open>Paths\<close>

lemma alw_sset: \<open>alw (holds P) stream \<Longrightarrow> s \<in> sset stream \<Longrightarrow> P s\<close>
  by (metis alw_iff_sdrop holds.simps imageE sdrop_simps(1) sset_range)

lemma sset_alw: \<open>\<forall>x \<in> sset s. P x \<Longrightarrow> alw (holds P) s\<close>
  by (simp add: alw_iff_sdrop)

lemma alw_in_sset: \<open>alw (holds (\<lambda>n. n \<in> sset s)) s\<close>
  by (simp add: sset_alw)

lemma alw_snth: \<open>alw (holds P) s \<Longrightarrow> P (s !! n)\<close>
  by (simp add: alw_iff_sdrop)

lemma alwt_ipath: \<open>alwt (holdst P) tab \<Longrightarrow> ipath tab path \<Longrightarrow> alw (holds P) path\<close>
proof (coinduction arbitrary: tab path)
  case alw
  then show ?case
    by cases (force elim: ipath.cases)
qed

lemma alw_streams: \<open>alw (holds P) s \<Longrightarrow> s \<in> streams (Collect P)\<close>
  by (meson Ball_Collect alw_sset sset_streams)

lemma trees_streams:
  assumes \<open>ipath t s\<close> \<open>t \<in> trees (Collect P)\<close>
  shows \<open>s \<in> streams (Collect P)\<close>
  using assms by (coinduction arbitrary: s)
    (meson alw_streams streams.cases alwt_ipath trees_alwt)

section \<open>Trees where every sub-tree eventually satisfies a property\<close>

inductive evt :: \<open>('a tree \<Rightarrow> bool) \<Rightarrow> 'a tree \<Rightarrow> bool\<close> where
  Here: \<open>P t \<Longrightarrow> evt P t\<close>
| There: \<open>\<forall>s \<in> set subs. evt P s \<Longrightarrow> evt P (Node l subs)\<close>

lemma alwt_evt: \<open>alwt P t \<Longrightarrow> evt P t\<close>
  by (auto elim: alwt.cases intro: evt.intros)

lemma evt_ev_holds:
  assumes \<open>evt (holdst P) t\<close> \<open>ipath t s\<close>
  shows \<open>ev (holds P) s\<close>
  using assms by (induct \<open>holdst P\<close> t arbitrary: P s)
    (fastforce simp: ev.intros elim: ipath.cases)+

section \<open>Next\<close>

abbreviation nxtt :: \<open>('a tree \<Rightarrow> bool) \<Rightarrow> 'a tree \<Rightarrow> bool\<close> where
  \<open>nxtt P t \<equiv> \<forall>s \<in> set (getSubs t). P s\<close>

lemma alwt_impl_nxtt: \<open>alwt (P impl nxtt P) t \<Longrightarrow> P t \<Longrightarrow> alwt P t\<close>
  by (coinduction arbitrary: t) (auto elim: alwt.cases)

(* TODO: is this useful? *)
lemma lift_alwt:
  assumes \<open>\<And>t. P t\<close>
  shows \<open>alwt P t\<close>
  using assms by (coinduction arbitrary: t) blast

(*
  introduces_lasting says:
  introduces _ = Some (ps, a) impl nxtt \<exists>p \<in> ps. p at a in _)

  And then preservation says it stays there.
*)

lemma alwt_holds_alw:
  assumes \<open>alwt (holdst P impl holdst Q) t\<close> \<open>ipath t s\<close>
  shows \<open>alw (holds P impl holds Q) s\<close>
  using assms
proof (coinduction arbitrary: t s)
  case alw
  then show ?case
  proof cases
    case AlwT
    with alw(2) show ?thesis
    proof cases
      case (IPath s subs tail l)
      then show ?thesis
        using AlwT by auto
    qed
  qed
qed

lemma alwt_nxt_holds_alw:
  assumes \<open>alwt (holdst P impl nxtt (holdst Q)) t\<close> \<open>ipath t s\<close>
  shows \<open>alw (holds P impl nxt (holds Q)) s\<close>
  using assms 
proof (coinduction arbitrary: t s)
  case alw
  then show ?case
  proof cases
    case AlwT
    with alw(2) show ?thesis
    proof cases
      case (IPath s' subs tail l)
      moreover from this have \<open>holds P s \<longrightarrow> nxt (holds Q) s\<close>
        using AlwT by (fastforce elim: ipath.cases)
      ultimately show ?thesis
        using AlwT by auto 
    qed
  qed
qed

lemma alwt_ipath_lt:
  assumes
    \<open>alwt (holdst P impl nxtt (holdst Q)) t\<close> \<open>alwt (holdst Q impl nxtt (holdst Q)) t\<close>
    \<open>ipath t s\<close> \<open>n < k\<close> \<open>P (s !! n)\<close>
  shows \<open>Q (s !! k)\<close>
proof -
  have \<open>alw (holds P impl nxt (holds Q)) s\<close>
    using assms(1, 3) alwt_nxt_holds_alw by blast
  then have \<open>alw (holds P impl nxt (holds Q)) (sdrop n s)\<close>
    using alw_sdrop by blast
  then have \<open>holds Q (sdrop (Suc n) s)\<close>
    using assms(5) by auto
  moreover have \<open>alw (holds Q impl nxt (holds Q)) s\<close>
    using assms(2-3) alwt_nxt_holds_alw by blast
  then have \<open>alw (holds Q impl nxt (holds Q)) (sdrop (Suc n) s)\<close>
    using alw_sdrop by blast
  ultimately have \<open>alw (holds Q) (sdrop (Suc n) s)\<close>
    using alw_invar by blast
  then have \<open>alw (holds Q) (sdrop k s)\<close>
    using assms(4) by (metis alw_sdrop less_iff_Suc_add sdrop.simps(2) sdrop_add)
  then show ?thesis
    by auto
qed

section \<open>Paths\<close>

lemma sset_sdrop: \<open>s \<in> sset steps \<Longrightarrow> \<exists>n. s = shd (sdrop n steps)\<close>
  by (metis imageE sdrop_simps(1) sset_range)

lemma stake_subset: \<open>n < k \<Longrightarrow> set (stake n steps) \<subseteq> set (stake k steps)\<close>
  using length_stake stake_cycle_le take_stake
  by (metis less_le set_take_subset stake_invert_Nil zero_order(2))

lemma snth_stake: \<open>steps !! n = s \<Longrightarrow> n < k \<Longrightarrow> s \<in> set (stake k steps)\<close>
  using stake_subset by (metis Suc_lessI in_set_conv_decomp stake_Suc subsetD)

lemma stake_finite:
  assumes \<open>S \<subseteq> sset steps\<close> \<open>finite S\<close>
  shows \<open>\<exists>n. S \<subseteq> set (stake n steps)\<close>
proof -
  obtain N where N: \<open>finite N\<close> \<open>\<forall>s \<in> S. \<exists>n \<in> N. steps !! n = s\<close>
    using assms by (metis (no_types, opaque_lifting) finite_subset_image imageE sset_range)
  then have \<open>\<forall>s \<in> S. s \<in> set (stake (Suc (Max N)) steps)\<close>
    using snth_stake by (metis Max_less_iff empty_iff lessI)
  then show ?thesis
    by blast
qed

lemma stake_finite':
  assumes \<open>S \<subseteq> f ` sset steps\<close> \<open>finite S\<close>
  shows \<open>\<exists>n. S \<subseteq> f ` set (stake n steps)\<close>
proof -
  obtain N where N: \<open>finite N\<close> \<open>\<forall>s \<in> S. \<exists>n \<in> N. f (steps !! n) = s\<close>
    using assms by (smt sset_range finite_subset_image image_iff) (* TODO: smt *)
  then have \<open>\<forall>s \<in> S. s \<in> f ` set (stake (Suc (Max N)) steps)\<close>
    using snth_stake by (metis Max_less_iff empty_iff image_iff lessI)
  then show ?thesis
    by blast
qed

lemma stake_snth:
  assumes \<open>s \<in> set (stake n steps)\<close>
  shows \<open>\<exists>m \<le> n. steps !! m = s\<close>
  using assms
proof (induct n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then consider (here) \<open>steps !! n = s\<close> | (there) \<open>s \<in> set (stake n steps)\<close>
    by (metis UnE list.set(1) list.set(2) set_append singletonD stake_Suc)
  then show ?case
    using Suc le_SucI by cases blast+
qed

end