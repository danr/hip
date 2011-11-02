-- http://dream.inf.ed.ac.uk/projects/lemmadiscovery/case_results.php

header{* Test Synthesis on Trees *}

theory Tree_size_height2

imports CaseAnalysis2 IsaP
begin


datatype 'a Tree =
    Leaf
  | Node "'a Tree" "'a" "'a Tree"

fun mirror ::"'a Tree \<Rightarrow> 'a Tree"
where
    mirror_leaf: "mirror Leaf = Leaf"
  | mirror_node: "mirror (Node l data r) = Node (mirror r) data (mirror l)"
declare mirror_leaf[wrule]
declare mirror_node[wrule]

fun nodes :: "'a Tree \<Rightarrow> N"
where
    nodes_leaf: "nodes Leaf = 0"
  | nodes_node: "nodes (Node l data r) =
                     (suc 0) + nodes l + nodes r"
declare nodes_leaf[wrule]
declare nodes_node[wrule]

 fun max :: "N \<Rightarrow> N \<Rightarrow> N"
where
    max_0: "max 0 y = y"
  | max_suc: "max (suc x) y = (case y of 0 => (suc x) | suc z => suc(max x z))"
declare max_0[wrule]
declare max_suc[wrule]

fun height :: "'a Tree \<Rightarrow> N"
where
  height_leaf: "height Leaf = 0"
  | height_node: "height (Node l data r) = suc(max (height l) (height r))"
declare height_leaf[wrule]
declare height_node[wrule]

end
