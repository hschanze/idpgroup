#
# IdPGroup: Implements identification functions for different $p$-groups.
#
#! @Chapter Introduction
#!
#! The purpose of the &IdPGroup; package is to implement identification functions for
#! different $p$-groups, which are implemented in the &SmallGrps; library, but lack
#! an effective identification routine in it.
#! The first function identifies the groups of order 512. This is done by calculating
#! a number of invariants of a given group and comparing them with the values of all
#! possible candidates via a precalculated search tree. More details can be found in
#! section <Ref Sect='Section_Identification'/>.
#!
#! Section <Ref Sect='Section_Load'/> introduces the definitions of (strong) siblings
#! and includes functions to load all such sets of groups of certain order.
#!
#! Functions that were used to calculate these lists of groups and which can be used to
#! calculate them for different orders can be found in section
#! <Ref Sect='Section_Calculate'/>.
#!
#! Once such sets of groups are determined one might want to examine them further by
#! checking certain properties and calculating additionaly invariants. In
#! Section <Ref Sect='Section_Table'/> one can find functions to calculate some
#! selected invarants and properties for such sets and export them into LaTeX-readable
#! lines of code.
#!
#! Finally section <Ref Sect='Section_Build'/> describes all funcions that were used
#! to build the search tree in the descirbed identification routine and which
#! can be used to build other such trees.


#! @Chapter Functionality
#!
#! This chapter lists all functions contained in the &IdPGroup; package.


#! @Section Identifying groups via a search tree
#! @SectionLabel Identification
#!
#! This section briefly describes the functions and variables of this package
#! associated to the identification of an arbitrary group of order 512 via
#! the search tree <Ref Var="ID_GROUP_512_TREE" Style="Text"/>.
#! When saying 'identify a group <M>G</M>' we want to find an __id__ such that
#!`SmallGroup(512, id)` is isomorphic to <M>G</M>.
#!
#! The used tree is implement as a nested record with the following components:
#! * "fp": a list of integers, each being the encoded fingerprint of the group resulting
#!         from the specific test performed at the current level of the identification
#!         routine. Each integer is gained from appyling
#!         <Ref Func="IdPGroup_Pack" Style="Text"/> to the fingerprint.
#! * "next": a list comprised of the resprective subbranches corresponding to the
#!           fingerprints in "fp". This is either a list of ids or a branch
#!           implemented as a record itself.
#! Depending on the level each record also has one of the following two components:
#! * "test": a string that indicates which test was used via
#!           <Ref Func="TestOnGroup" Style="Text"/> to create the listed fingerprints.
#! * "desc": a list of integers that encode a description of the performed test
#!           using `EvalFpCoc`.
#!
#! The first levels of <Ref Var="ID_GROUP_512_TREE" Style="Text"/> try to distinguish
#! groups by the following invariants:
#! * The rank of the group.
#! * The collected orders of all elements of the group.
#! * The numbers of conjugacy classes of each length and representative order (the
#!   order of the elements in the class) of the group.
#! * The isomorphism type of the parent of the group, i.e. the quotient of the group
#!   and the smallest non-trivial element of the lower-$p$-central series.
#! * The abelian invarants, i.e. the isomorphism types of the quotients of the
#!   derived series.
#! * The cycle structure of the permutations induced on all clusters of conjugacy
#!   classes of same length and representative order by the power map $x\mapsto x^3$.
#!
#! If necessary these invariants are followed by invaraints resulting from
#! tests evaluated on partitions of <M>G</M>.
#!
#! The initial partition is made of the conjugacy classes of <M>G</M>
#! grouped such that conjugacy classes of the same length and same representative
#! order belong to the same partitioning subset. The results of `EvalFpCoc`
#! applied to a partition give the invaraints used to distinguish groups in these
#! levels of the search tree. The exact behaviour is determined by the content
#! of the component "desc". After the evaluation of each test, the partition is refined
#! according to the result of `EvalFpCoc`.
#!
#! If the preceding invaraints do not lead to a single group, the following (more
#! time consuming) invaraints are calculated.
#! * The isomorphism types of the non-trivial factors formed by the group and
#!   elements of the smallest non-trivial element of the lower-p-central series.
#! * The isomorphism types of the non-trivial factors formed by the group and
#!   elements of the center.
#! * The isomorphism types of all maximal subgroups.
#!
#! Remaining are 139 pairs and 1 triplet of groups of unidentified groups. All these
#! groups are distinguished by a random isomorphism test. That is done by selecting
#! random elements from predefined clusters of conjugacy classes, that were used
#! and potentially refined before, until these elements generate the group. This list
#! of generators is then turned into a `pcgs` and the presentation encoded into
#! an integer by the funtion `CodeGenerators`. The resulting integer modulo 99661
#! is then compared with precalculated fingerprints of the candidate groups. If
#! none of the fingerprints coincides the process is repeated. Thus the runtime of
#! the identification for these groups is not constant.

#! @Arguments G [,opt]
#! @Returns The id of the group of order 512 that is isomorphic to <A>G</A>.
#! @Description
#! Identifies the group <A>G</A> of order 512.
#! This function accepts a record <A>opt</A> of options with the following content:
#! * <A>tree</A>: A search tree that was built using the invariants resulting from
#!                <M>tests</M>.
#! * <A>anupq</A>: A boolean that determines if <M>IsPqIsomorphicPGroup</M> from the
#!                 &Anupq;-Package should be used to find the to <A>G</A> isomorphic
#!                 group among the remaining candidates.
#! * <A>path</A>: A boolean that determines if the path through the tree shall be
#!                recorded while identification and returned as well.
#! The default values of <A>opt</A> is <C>rec(anupq</C>:=<K>false</K>,
#!  <C>tree:=ID_GROUP_512_TREE, path:=</C> <K>false</K> <C>)</C>.
#! @BeginExampleSession
#! gap> G := Image(IsomorphismPermGroup(SmallGroup(512, 1984)));;
#! gap> IdGroup512(G);
#! 1984
#! gap> IdGroup512(G, rec(path := true));
#! [ 1984, rec( fp := [ 2, 8217, 5321 ], pos := [ 2, 188, 1 ],
#!         tests := [ "Rank", "ElmOrds", [ 40511009 ] ] ) ]
#! gap> H := Image(IsomorphismPermGroup(SmallGroup(512, 449)));;
#! gap> IdGroup512(H, rec(anupq := false));
#! 449
#! gap> IdGroup512(H, rec(anupq := true));
#! 449
#! @EndExampleSession
DeclareGlobalFunction("IdGroup512");

#! @Description
#! The search tree of groups of order 512 that can determine the vast majority
#! of groups. At the beginning only a small part is loaded. Other branches are
#! loaded if necessary.
DeclareGlobalName("ID_GROUP_512_TREE");

#! @Description
#! Loads the entire search tree <Ref Var="ID_GROUP_512_TREE" Style="Text"/>.
DeclareGlobalFunction("LoadTotalTree");

#! @Returns A list of bins of group-ids, that
#! <Ref Var="ID_GROUP_512_TREE" Style="Text"/> can
#! not distinguish without random isomorphism tests.
#! @Description
#! @BeginExampleSession
#! gap> L := IdGroup512Exceptions();;
#! gap> Collected(List(L, Size));
#! [ [ 2, 139 ], [ 3, 1 ] ]
#! gap> L[138];
#! [ 6249609, 6249610, 6249611 ]
#! @EndExampleSession
DeclareGlobalFunction("IdGroup512Exceptions");

#! @Section Loading (strong) siblings
#! @SectionLabel Load
#!
#! This section describes the functions used to load precalculated lists of (strong)
#! siblings, i.e. groups that fulfil the following definitions:
#! * __subgroup-equivalent groups__ are groups with a bijection between the sets of
#!   proper subgroups s.t. preimage and image are isomorphic,
#! * __factor-equivalent groups__ are groups with a bijection between the sets of
#!   proper factors s.t. preimage and image are isomorphic,
#! * __siblings__ are subgroup- and factor-equivalent groups, where the
#!   bijection of proper subgroups preservs conjugacy and maps the Frattini subgroup,
#!   lower and upper central series onto the respective counterparts,
#! * __strong siblings__ are siblings that are also Brauer Pairs.
#! All (strong) siblings of orders dividing 512 together with some trivial cases
#! are implemented in this package and are callable by the following functions.

#! @Arguments order [,indices]
#! @Returns A list of lists of ids of siblings of size <A>order</A>.
#! @Description
#! Loads and returns a list of ids of siblings of size <A>order</A> if available.
#! Currently available sizes are:
#! * all orders of the form $p\,q$ for $p$ and $q$ primes,
#! * all powers of two smaller than $2^9$
#! * all powers of three smaller than $3^5$
#! * all powers of a prime smaller than $p^4 $
#! * all products of two powers and
#! * all orders smaller than 255 except 60, 120, 160, 168, 180, 189, 192 and 240.
#! If no list is available for the provided order <C>fail</C> is returned. If a
#! list <A>indices</A> is given, only the respective entries are returned.
#! @BeginExampleSession
#! gap> SiblingsIds(101);
#! [ ]
#! gap> SiblingsIds(128);
#! [ [ 1317, 1322 ], [ 1327, 1329 ], [ 1597, 1598 ] ]
#! gap> SiblingsIds(256, [1..3]);
#! [ [ 227, 228 ], [ 258, 260, 261 ], [ 845, 846 ] ]
#! @EndExampleSession
DeclareGlobalFunction("SiblingsIds");

#! @Arguments order [,indices]
#! @Returns A list of siblings of size <A>order</A>.
#! @Description
#! Loads and returns a list of siblings of size <A>order</A> if available. If
#! no list is available for the provided order <C>fail</C> is returned. If
#! <A>indices</A> are given, only the respective entries are returned.
DeclareGlobalFunction("Siblings");

#! @Arguments order [,indices]
#! @Returns A list of lists of ids of strong siblings of <A>order</A>.
#! @Description
#! Loads and returns a list of ids of strong siblings of <A>order</A> if available.
#! Currently available sizes are:
#! * all orders of the form $p\,q$ for $p$ and $q$ primes,
#! * all powers of two smaller than $2^9$
#! * all powers of three smaller than $3^5$
#! * all powers of a prime smaller than $p^4 $
#! * all products of two powers and
#! * all orders smaller than 255 except 60, 120, 160, 168, 180, 189, 192 and 240.
#! If no list is available for the provided order <C>fail</C> is returned. If a
#! list <A>indices</A> is given, only the respective entries are returned.
#! @BeginExampleSession
#! gap> StrongSiblingsIds(256);
#! [ [ 1734, 1735 ], [ 1736, 1737 ], [ 1739, 1740 ], [ 1741, 1742 ],
#!   [ 3678, 3679 ], [ 4154, 4157 ], [ 4155, 4158 ], [ 4156, 4159 ] ]
#! gap> StrongSiblingsIds(256, [1..3]);
#! [ [ 1734, 1735 ], [ 1736, 1737 ], [ 1739, 1740 ] ]
#! @EndExampleSession
DeclareGlobalFunction("StrongSiblingsIds");

#! @Arguments order [,indices]
#! @Returns A list of strong siblings of <A>order</A>.
#! @Description
#! Loads and returns a list of strong siblings of <A>order</A> if available. If
#! no list is available for the provided order <C>fail</C> is returned. If a
#! list <A>indices</A> is given, only the respective entries are returned.
DeclareGlobalFunction("StrongSiblings");

DeclareGlobalName("BINS_OF_IDS");

#! @Section Functions for calculating (strong) siblings
#! @SectionLabel Calculate
#!
#! This section describes all functions for calculating (strong) siblings
#! of a given order.

#! @Arguments Bins, order, test
#! @Returns A list of sublists of the provided lists in <A>Bins</A>.
#! @Description
#! Takes a list of bins with ids of groups of size <A>order</A> and splits
#! them via the outcome of <A>test</A> implemented in `TestOnGroup`.
#! @BeginExampleSession
#! gap> SplitBinsViaTest([[1..10]], 512, "MaxSubId");
#! [ [ 1 ], [ 2 ], [ 3, 8 ], [ 4 ], [ 5 ], [ 6, 7 ], [ 9 ], [ 10 ] ]
#! @EndExampleSession
#DeclareGlobalFunction("SplitBinsViaTest");

#! @Arguments order [,verbose]
#! @Returns A list of lists of ids of groups of size <A>order</A> that are
#! siblings.
#! @Description
#! Determines all siblings among the groups of size <A>order</A> by applying
#! <Ref Func="SplitBinsViaTest" Style="Text"/> with the tests
#! <C>"MaxSubId"</C>, <C>"SpSubId"</C>,
#! <C>"SubId"</C>, <C>"MaxFactId"</C> and <C>"FactId"</C> iterativly. The
#! tests <C>"MaxSubId"</C> and <C>"MaxFactId"</C> are not necessary, but are
#! efficient and eliminate some sets before applying the more costly tests.
#! The boolean <A>verbose</A> controls if a collection of bin sizes is
#! printed after each test (<K>true</K> as default).
#! @BeginExampleSession
#! gap> CalculateSiblings(128);
#! Test 'MaxSubId' found following bins of size greater one:[ [ 2, 23 ], [ 3, 2 ] ]
#! Test 'SpSubId' found following bins of size greater one:[ [ 2, 22 ] ]
#! Test 'SubId' found following bins of size greater one:[ [ 2, 16 ] ]
#! Test 'MaxFactId' found following bins of size greater one:[ [ 2, 3 ] ]
#! Test 'FactId' found following bins of size greater one:[ [ 2, 3 ] ]
#! [ [ 1317, 1322 ], [ 1327, 1329 ], [ 1597, 1598 ] ]
#! gap> CalculateSiblings(128, false);
#! [ [ 1317, 1322 ], [ 1327, 1329 ], [ 1597, 1598 ] ]
#! @EndExampleSession
DeclareGlobalFunction("CalculateSiblings");

#! @Arguments Bins, order
#! @Returns A list of sublists of the provided lists in <A>Bins</A>.
#! @Description
#! Determines the Brauer pairs among the bins of ids of groups of size
#! <A>order</A> listed in <A>Bins</A>.
#DeclareGlobalFunction("DetermineBrauerPairs");

#! @Arguments order [,verbose]
#! @Returns A list of lists of ids of groups of size <A>order</A> that are
#! strong siblings.
#! @Description
#! First calculats all siblings of size <A>order</A> via
#! <Ref Func="CalculateSiblings" Style="Text"/> and then determines all strong
#! siblings among these by <Ref Func="DetermineBrauerPairs" Style="Text"/>.
#! The boolean <A>verbose</A> controls if a
#! collection of bin sizes is printed after each test while siblings are
#! calculated (<K>true</K> as default).
#! @BeginExampleSession
#! gap> CalculateStrongSiblings(256, false);
#! [ [ 1734, 1735 ], [ 1736, 1737 ], [ 1739, 1740 ], [ 1741, 1742 ], [ 3678, 3679 ],
#!   [ 4154, 4157 ], [ 4155, 4158 ], [ 4156, 4159 ] ]
#! @EndExampleSession
DeclareGlobalFunction("CalculateStrongSiblings");

#! @Arguments Bin, order
#Splits list of ids of groups of size <A>order</A> in <A>Bin</A>, if their
#outer automorphism groups are isomorphic, via `IsPqIsomorphicPGroup`
#from the &Anupq; package.
#DeclareGlobalFunction("SplitExactOutEqv");

#Takes a list of bins with ids of groups of size <A>order</A> and evaluates
#which are outer-automorphism equivalent. If <A>exact</A> = <K>true</K>, sets
#of groups which could not be ruled out to be equivalent are testet via
#`SplitExactOutEqv`. Otherwise these sets are simply included.
#DeclareGlobalFunction("BinsOfOutEqGroups");

#! @Section Table of bins of groups
#! @SectionLabel Table
#!
#! This section includes the functions of the package that create and fill
#! a table for bins of groups, listing certain invaraints and properties and
#! exporting this table as rows of a latex-tables.

#! @Arguments Bins, order
#! @Returns A list of records.
#! @Description
#! Calculates some invariants and properties for the groups of
#! order <A>order</A> with ids in lists of <A>bins</A>. If the invariants
#! are equal for all groups of a bin, a record listing all information is
#! added to the returned list. The calculated invariants are:
#! * the rank of the groups,
#! * the $p$-class of the groups,
#! * the size of the groups of automorphisms.
#! Furthermore the following properties are examined for the groups of a
#! bin:
#! * Are the groups outer-automorphism-equivaleant, i.e. are the groups
#!   of outer-automorphism isomorphic?
#! * Are the groups isoclinic?
#! * Are the groups a modular isomorphic pair (MIP), i.e. are their group
#!   rings over a field of characteristic p isomorphic?
#! The last two properties are not examined and left as an empty string
#! in this function, but can be filled via
#! <Ref Func="DetermineMIPInTable" Style="Text"/>  and
#! <Ref Func="DetermineIsoclinicInTable" Style="Text"/>.
#! @BeginExampleSession
#! gap> Bins := StrongSiblingsIds(512, [1, 5, 14]);
#! [ [ 1364, 1368 ], [ 1680, 1681 ], [ 15826, 15827 ] ]
#! gap> TableOfGroupInvariants(Bins, 512);
#! [ rec( OutEqv := "yes", SizeAut := 8192, ids := [ 1364, 1368 ],
#!        isoclinic := "",  mip := "", pclass := 5, rank := 2 ),
#!  rec( OutEqv := "yes", SizeAut := 16384, ids := [ 1680, 1681 ],
#!       isoclinic := "", mip := "", pclass := 5, rank := 2 ),
#!  rec( OutEqv := "no", SizeAut := 65536, ids := [ 15826, 15827 ],
#!       isoclinic := "", mip := "", pclass := 3, rank := 3 ) ]
#! @EndExampleSession
DeclareGlobalFunction("TableOfGroupInvariants");

#! @Arguments tab
#! @Returns A list of records.
#! @Description
#! Determines if the sets of groups represented by the records in
#! <A>tab</A> are modular isomorphic pairs using the &ModIsom; package.
#! This information is added to each record of <A>tab</A> and the
#! updated list is returned. This function is included in an extension
#! of the package and only available if the respective package is loaded.
DeclareGlobalFunction("DetermineMIPInTable");

#! @Arguments tab
#! @Returns A list of records.
#! @Description
#! Determines if the sets of groups represented by the records in
#! <A>tab</A> are isoclinic using the &XMod; package. This
#! information is added to each record and the of <A>tab</A> updated
#! list is returned. This function is included in an extension
#! of the package and only available if the respective package is loaded.
DeclareGlobalFunction("DetermineIsoclinicInTable");

#! @Arguments tab1, tab2
#! @Returns A list of records.
#! @Description
#! Merges the tables <A>tab1</A> and <A>tab2</A> into one table. If
#! a record entry of only one is the empty string the non-empty
#!string is used. This enables the parallel computation of e.g.
#! <Ref Func="DetermineMIPInTable" Style="Text"/>  and
#! <Ref Func="DetermineIsoclinicInTable" Style="Text"/>.
DeclareGlobalFunction("MergeTablesOfInvariants");

#! @Arguments tab, filename
#! @Description
#! Exports the content of the table <A>tab</A> into
#! "<A>filename</A>_table.txt" as rows of a latex table.
DeclareGlobalFunction("PrintTableToFile");


#! @Section Functions for building a search tree
#! @SectionLabel Build
#!
#! This section describes all functions and variables connected to
#! building a search tree that can be used with
#! <Ref Func="IdGroup512" Style="Text"/> to
#! identify groups via implemented invariants.
#!
#! In short this is done be initializing a tree via calling
#! <Ref Func="TestOnClusterList" Style="Text"/> with a selected
#! test on a list of (lists of)
#! ids of groups of given order and then iteratnig the following
#! three steps
#! * Collecting the clusters of the curent tree via
#!       <Ref Func="ClusterList" Style="Text"/>,
#! * Performing a choosen test on these clusters via
#!       <Ref Func="TestOnClusterList" Style="Text"/>,
#! * Extending the tree with these test results via
#!       <Ref Func="AddClusterTestResults" Style="Text"/>.
#! A very effective set of invaraints can be obtained by calling
#! <Ref Func="CocTestOnClusterList" Style="Text"/> in the second step.
#! This should only be done when
#! the groups of each provided cluster yields the same value when the
#! test `CocList` is applied. Furthermore
#! these invaraints should be used for as few as possible clusters since
#! <Ref Func="CocTestOnClusterList" Style="Text"/>
#! includes a search for suitable parameters than can take quite some
#! time.

#! @Arguments list
#! @Returns An interger encoding the content of <A>list</A>.
#! @Description
#! Encodes the content of the provided <A>list</A> into an integer.
#! @BeginExampleSession
#! gap> IdPGroup_Pack([1,2,3]);
#! 123
#! gap> IdPGroup_Pack([606, 109, 1405]);
#! 63095
#! gap> IdPGroup_Pack([[1,2,3], [606, 1405]]);
#! 19765
#! @EndExampleSession
#DeclareGlobalFunction("IdPGroup_Pack");

#! @Arguments G
#! @Returns A list of lists containing the conjugacy classes of <A>G</A>.
#! @Description
#! Computes the conjugacy classes of the group <A>G</A> and clusters them
#! such that each clusters contains all classes of a certain length and
#! certain representative order (meaning the order of any representative).
#DeclareGlobalFunction("ClusterConjClasses");

#! @Arguments coc, n
#! @Returns A lists of lists of lists of integers
#! @Description Examines the permutation induced by the power map $x\mapsto x^n$
#! on each cluster of <A>coc</A>. If a class of a cluster is fixed, the
#! permutation within the class is determined and added to the lists of
#! permutations of the cluster.
#! Finally the cycle structure of each permutation associated to a cluster
#! is examined via `CycleStructurePerm` and saved as a list of integers
#! (undound entries are replaced by 0).
#DeclareGlobalFunction("PowerMapCocCycSt");

#! @Arguments tree
#! @Returns A list of all clusters of groups in <A>tree</A>
#!          (i.e. the leafs of <A>tree</A>).
#! @Description
#! Iterates through <A>tree</A> and collects information about each leaf
#! as a record. This includes the size of the leaf, the path through
#! <A>tree</A> leading to the leaf, the tests performed including
#! descriptions of performed `EvalFpCoc`-tests and the ids of the
#! groups contained in the leaf.
#! @BeginExampleSession
#! gap> tree := rec( fp := [ 63049, 75721, 4310 ],  next := [ [ 3, 8 ], [ 4 ],
#! gap>            rec( fp := [ 11744, 86646 ], next := [ [ 5 ], [ 6, 7 ] ],
#! gap>                test := "MaxSubId" ) ], test := "ElmOrds" );;
#! gap> ClusterList(tree);
#! [ rec( descl := [  ], ids := [ 3, 8 ], path := [ 63049 ], size := 2,
#!        tests := [ "ElmOrds" ] ),
#!   rec( descl := [  ], ids := [ 4 ], path := [ 75721 ], size := 1,
#!        tests := [ "ElmOrds" ] ),
#!   rec( descl := [  ], ids := [ 5 ], path := [ 4310, 11744 ], size := 1,
#!        tests := [ "ElmOrds", "MaxSubId" ] ),
#!   rec( descl := [  ], ids := [ 6, 7 ], path := [ 4310, 86646 ], size := 2,
#!        tests := [ "ElmOrds", "MaxSubId" ] ) ]
#! @EndExampleSession
DeclareGlobalFunction("ClusterList");

#! @Arguments G, test [,opt]
#! @Returns The result of <A>test</A> applied to <A>G</A>, if desried encoded as
#!          an integer.
#! @Description
#! Performs the selected <A>test</A> on the group <A>G</A>. The following
#! choices for <A>test</A> are implemented:
#! * <A>"ElmOrds"</A>: Collects the orders of all elements of <A>G</A>.
#! * <A>"Center"</A>: Calculates the abelian invariants of the center of
#!                    <A>G</A>.
#! * <A>"Rank"</A>: Calculates the rank of <A>G</A>.
#! * <A>"AbelInv"</A>: Computes the order of each term of the derived series
#!                     and the abelian Invariants of the derived factors of
#!                     <A>G</A>.
#! * <A>"UCSId"</A>: Identifies the proper subgroups of the upper central
#!                   series of <A>G</A>
#!                   via `IdGroup`.
#! * <A>"LCSId"</A>: Identifies the proper subgroups of the lower central
#!                   series of <A>G</A>
#!                   via `IdGroup`.
#! * <A>"PCSId"</A>: Identifies the proper subgroups of the p-central series
#!                   of <A>G</A>
#!                   via `IdGroup`.
#! * <A>"SpSubId"</A>: Computes the Frattini subgroup, the upper and lower
#!                     central series of <A>G</A> and identifies all terms
#!                     if possible via `IdGroup`.
#! * <A>"MaxSubId"</A>: Collects the sizes and isomorphism types of all
#!                      maximal subgroups of <A>G</A> via `IdGroup`.
#! * <A>"SubId"</A>: Collects the sizes and isormorphism types of conjugacy
#!                   classes of all proper subgoups via `IdGroup`.
#! * <A>"MaxFactId"</A>: Collects the sizes and isomorphism types of all
#!                       maximal factors of <A>G</A> via `IdGroup`.
#! * <A>"CentQuot"</A>: Collects the sizes and isomorphism types of all
#!                      quotients of <A>G</A> with non-trivial elements
#!                      of the center of <A>G</A> via `IdGroup`.
#! * <A>"LCSFactId"</A>: Collects the isomorphism types of all quotients of
#!                       <A>G</A> with with cyclic subgroups generated by
#!                       by non-trivial elements of the last non-trivial
#!                       term of the p-central series.
#! * <A>"FactId"</A>: Identifies all proper factors of <A>G</A> via `IdGroup`.
#! * <A>"CocList"</A>: Collects the number of conjugacy classes of a <A>G</A>
#!                     of same length and same representative order
#!                     (the order of a representative).
#! * <A>"PMCycSt"</A>: Determines the cycle-structure invariant for the power
#!                     map $x\mapsto x^3$ on the clusters of conjugacy classes via
#!                     `PowerMapCocCycSt`.
#! * <A>"OutId"</A>: Tries to identify the groups of outer automorphisms of
#!                   <A>G</A>, either via `IdGroup` (if available) or via its
#!                   size and `TestOnGroup` with <A>"ElmOrds"</A> and
#!                   <A>"CocList"</A> (<A>"MaxSubId"</A> and <A>"CentQuot"</A>
#!                   can also be used if feasible).
#! * <A>"LattEqv"</A>: Calculates all conjugacy classes of proper subgoups of
#!                     <A>G</A>, stores their size, identifies the the
#!                     isomorphism types of each class and determines the
#!                     isomorphism types and conjugacy classes in <A>G</A> of
#!                     its maximal subgroups and minimal supergroups.
#! This function accepts a record <A>opt</A> of options with the single content
#! <A>opt.pack</A>, a boolean that determines if <C>IdPGroup_Pack</C> should be applied
#! to the result of a test. The default value of <A>opt</A> is
#! <M>rec(pack:=</M><K>true</K><M>)</M>.
#! @BeginExampleSession
#! gap> G := SmallGroup(512, 1405);;
#! gap> TestOnGroup(G, "ElmOrds");
#! 85416
#! gap> TestOnGroup(G, "ElmOrds", rec(pack := false));
#! [ [ 1, 1 ], [ 2, 7 ], [ 4, 24 ], [ 8, 288 ], [ 16, 64 ], [ 32, 128 ] ]
#! @EndExampleSession
DeclareGlobalFunction("TestOnGroup");

#! @Arguments CL, test [,opt]
#! @Returns Either a list of pairs each containg the path to the respective
#! cluster (which is a leaf of a search tree) and the subbranch resulting
#! from the results of <A>test</A>, or just the list of subbranches if <A>CL</A>
#! contains only lists of integers. If <A>CL</A> consits of a single list
#! of integers the single resulting subbranch is returned on its own.
#! @Description
#! Performs the choosen test on the groups of each record in the <A>CL</A>.
#! The tests are performed by <Ref Func="TestOnGroup" Style="Text"/>.
#! <A>CL</A> could either be a
#! list of records produced by <Ref Func="ClusterList" Style="Text"/> or be
#! a list of lists containing
#! ids. In the former case the output is a list of pairs containg the path of
#! a cluster and the subbranch resulting from the test. In the latter case
#! only a list of subbranches is returned. If in the latter case the returned
#! list only one contains one subbranch, the subbranch itself is returned.
#! This is useful when building the first level of a search tree.
#! This function accepts a record <A>opt</A> of options with the following
#! content:
#! * <A>pack</A>: A boolean that is handed to <Ref Func="TestOnGroup" Style="Text"/>.
#! * <A>ign1cl</A>: A boolean that determines if clusters of size 1 should be
#!                  ignored.
#! * <A>order</A>: An integer giving the order of the groups with ids in
#!                 <A>CL</A>.
#! * <A>verbose</A>: A boolean that determines if progress should be printed.
#! * <A>notetest</A>: A boolean that decides if the performed test should be
#!                    noted in the returned subbranches. If so subbranches,
#!                    that do not split a cluster are omited.
#! The default value of <A>opt</A> is <M>rec(pack</M>:=<K>true</K>,
#! <M>ign1cl</M>:=<K>true</K>, <M>order</M>:=512,
#! <M>verbose</M>:=<K>true</K>, <M>notetest</M>:=<K>true</K><M>)</M>.
#! @BeginExampleSession
#! gap> TestOnClusterList([[1..10]],"ElmOrds", rec(verbose:=false));
#! rec( fp := [ 88570, 4310, 63049, 75721 ],
#!      next := [ [ 1 ], [ 2, 5, 6, 7, 9, 10 ], [ 3, 8 ], [ 4 ] ],
#!      test := "ElmOrds")
#! gap> TestOnClusterList([[1,2,5],[7,8,9]],"ElmOrds", rec(verbose:=false));
#! [ rec( fp := [ 88570, 4310 ], next := [ [ 1 ], [ 2, 5 ] ],
#!        test := "ElmOrds" ),
#!   rec( fp := [ 4310, 63049 ], next := [ [ 7, 9 ], [ 8 ] ],
#!        test := "ElmOrds") ]
#! gap> tree := TestOnClusterList([[3..8]],"ElmOrds", rec(verbose:=false));;
#! gap> CL := ClusterList(tree);
#! [ rec( descl := [  ], ids := [ 3, 8 ], path := [ 63049 ], size := 2,
#!        tests := [ "ElmOrds" ]),
#!   rec( descl := [  ], ids := [ 4 ], path := [ 75721 ], size := 1,
#!        tests := [ "ElmOrds" ]),
#!   rec( descl := [  ], ids := [ 5, 6, 7 ], path := [ 4310 ], size := 3,
#!        tests := [ "ElmOrds" ]) ]
#! gap> TestOnClusterList(CL, "MaxSubId", rec(verbose:=false, notetest := false));
#! [ [ [ 63049 ], rec( fp := [ 62603 ], next := [ [ 3, 8 ] ] ) ],
#!   [ [ 4310 ], rec( fp := [ 11744, 86646 ], next := [ [ 5 ], [ 6, 7 ] ] ) ] ]
#! @EndExampleSession
DeclareGlobalFunction("TestOnClusterList");

#! @Arguments tree, TR
#! @Returns The extended <A>tree</A> with the subbranches in <A>TR</A>.
#! @Description
#! Extends <A>tree</A> by the test results stored in <A>TR</A>, a list of pairs
#! each containing the path in <A>tree</A> and a branch (a tree of depth one),
#! extending the corresponding cluster of the inital <A>tree</A>.
#! @BeginExampleSession
#! gap> tree := TestOnClusterList([[3..8]],"ElmOrds", rec(verbose:=false));
#! rec( fp := [ 63049, 75721, 4310 ], next := [ [ 3, 8 ], [ 4 ], [ 5, 6, 7 ] ],
#!      test := "ElmOrds")
#! gap> TR:=TestOnClusterList(ClusterList(tree),"MaxSubId",rec(verbose:=false));
#! [ [ [ 4310 ], rec( fp := [ 11744, 86646 ], next := [ [ 5 ], [ 6, 7 ] ],
#!                    test := "MaxSubId" ) ] ]
#! gap> AddClusterTestResults(tree,TR);
#! rec( fp := [ 63049, 75721, 4310 ],
#!      next := [ rec( fp := [ 62603 ], next := [ [ 3, 8 ] ] ), [ 4 ],
#!                rec( fp := [ 11744, 86646 ], next := [ [ 5 ], [ 6, 7 ] ],
#!      test := "MaxSubId") ], test := "ElmOrds" )
#! @EndExampleSession
DeclareGlobalFunction("AddClusterTestResults");

#! @Arguments N, order, tests
#! @Returns A search tree (implemented as a record).
#! @Description
#! Builds a search tree for the groups with ids in <A>N</A> or, if <A>N</A> is
#! an integer, the first <A>N</A> groups of size <A>order</A>, using
#! <Ref Func="TestOnClusterList" Style="Text"/> with the tests from the
#! list <A>tests</A>.
#! @BeginExampleSession
#! gap> BuildSearchTree(5,512,["ElmOrds", "MaxSubId"]);
#! rec( fp := [ 88570, 4310, 63049, 75721 ], next := [ [ 1 ],
#!      rec( fp := [ 76646, 11744 ], next := [ [ 2 ], [ 5 ] ],
#!      test := "MaxSubId" ), [ 3 ], [ 4 ] ], test := "ElmOrds" )
#! gap> BuildSearchTree([1,2,3,5,7], 512, ["ElmOrds", "CocList"]);
#! rec( fp := [ 88570, 4310, 63049 ], next := [ [ 1 ],
#!      rec( fp := [ 96561, 32173 ], next := [ [ 2 ], [ 5, 7 ] ],
#!      test := "CocList" ), [ 3 ] ], test := "ElmOrds" )
#! @EndExampleSession
DeclareGlobalFunction("BuildSearchTree");

#! @Arguments Coc, paralist, it, maxit [,opt]
#! @Returns A pair made of a list of return values from `EvalFpCoc` and a list
#! describing the test performed by `EvalFpCoc`.
#! @Description
#! Does a parameter search such that evaluating `EvalFpCoc` on the clusters of
#! conjugacy classes in <A>coc</A> results in at least two different values. If
#! no suitable parameters are found, the function calls itself iterativly on
#! parameters that alter <A>Coc</A> until either a suitable list of parameters
#! is found or <A>it</A> is equal to <A>maxit</A>. The parameters of the current
#! iteration are provided in the list <A>paralist</A>.
#! If the function is initialized with <A>it</A>=0, it only returns a list of
#! parameters that alter the clusters in <A>Coc</A>.
#! Depending on the size of <A>coc</A> their can be a lot of parameters to check.
#! To decrease the needed time the following configurations are skipped:
#! * $[1,i,j]$, where the representative order of <A>coc[i]</A> and j are not coprime.
#! * $[2,i,j]$, where the representative order of <A>coc[i]</A> is less or equal
#!              then the order of <A>coc[j]</A> or the length of the classes in
#!              <A>coc[i]</A> is less then the ones of <A>coc[j]</A>.
#! * $[3,i,j]$, where the representative order of <A>coc[i]</A> is larger or equal
#!              then the order of <A>coc[j]</A> or the length of the classes in
#!              <A>coc[i]</A> is larger then the ones of <A>coc[j]</A>.
#! * $[4,i,j,k]$, where either the classes in <A>coc[i]</A> or <A>coc[j]</A> are of
#!                length one.
#! * $[5,i,j,k]$, where either the classes in <A>coc[i]</A> or <A>coc[j]</A> are of
#!                length one.
#!This function accepts a record <A>opt</A> of options with the following content:
#! * <A>target</A>: A list of integers that determines the desired second entries
#!                  of the parameters.
#! * <A>maxlevel</A>: An integer that determines the maximal first parameter entry.
#!                    That might be useful, since the parameters for test 4 and 5
#!                    often need more time then the rest.
#! The default value of <A>opt</A> is <M>rec(target:=[1..Size(Coc[1])],
#! maxlevel:=5</M>.
#! @BeginExampleSession
#! gap> Coc:=List([3, 8],id->ClusterConjClasses(SmallGroup(512, id)));;
#! gap> FindParametersForCocTest(Coc, [], 1, 1);
#! [ [ 1363, 46760 ], [ 3, 2, 4 ] ]
#! gap> FindParametersForCocTest(Coc, [], 1, 1, rec(target:=[4]));
#! [ [ 63010, 76026 ], [ [ 4, 4, 6, 5 ] ] ]
#! gap> FindParametersForCocTest(Coc, [], 0, 1, rec(target:=[4]));
#! [ [ 3, 4, 6 ], [ 4, 4, 6, 3 ], [ 4, 4, 6, 4 ], [ 4, 4, 6, 5 ] ]
#! gap> FindParametersForCocTest(Coc, [], 0, 1, rec(target:=[4], maxlevel := 3));
#! [ [ 3, 4, 6 ] ]
#! gap> Coc:=List([1883, 1885],id->ClusterConjClasses(SmallGroup(512, id)));;
#! gap> FindParametersForCocTest(Coc, [], 1, 2);
#! [ [ 8, 18 ], [ [ 1, 9, 3 ], [ 2, 14, 9 ] ] ]
#! @EndExampleSession
#DeclareGlobalFunction("FindParametersForCocTest");

#! @Arguments desc
#! @Returns An interger or a list of integers
#! @Description
#! De- or encodes a description for `EvalFPCoc`, depending on if an integer
#! (decodes to a list) or a list of integers (encodes to an integer)
#! is provided.
#! @BeginExampleSession
#! gap> DeEncodeDesc([3,2,4]);
#! 302004
#! gap> DeEncodeDesc(302004);
#! [3, 2, 4]
#! @EndExampleSession
#DeclareGlobalFunction("DeEncodeDesc");

#! @Arguments coc, desc, fp
#! @Returns A list of lists containing the conjugacy classes of a group.
#! @Description
#! Alters the clusters of conjugacy classes <A>coc</A> according the result
#! <A>fp</A> from <C>EvalFPCoc</C> evaluated with <A>desc</A> by spliting
#! the cluster at position <A>desc[2]</A> of <A>coc</A> into smaller ones.
#! @BeginExampleSession
#! gap> coc := ClusterConjClasses(SmallGroup(512, 3));;
#! gap> List(coc, Size);
#! [ 1, 15, 4, 24, 12, 48 ]
#! gap> fp := EvalFpCoc(coc, [3,2,4]);
#! [ 0, 0, 16, 16, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0 ]
#! gap> cocnew := AlterCocAccordingToFp(coc,[3,2,4],fp);;
#! gap> List(cocnew, Size);
#! [ 1, 12, 3, 4, 24, 12, 48 ]
#! @EndExampleSession
#DeclareGlobalFunction("AlterCocAccordingToFp");

#! @Arguments Ids, order, desclist, iterate
#! @Returns A search tree (implemented as a record).
#! @Description
#! Tries to split the list <A>Ids</A> of group ids of <A>order</A> with ids
#! as far as possible on the returned values of `EvalFpCoc` and returns the
#! resulting subbranch for a search tree with the relevant details. The
#! parameter search is done with at most <A>iterate</A> iterations.
#! Past perfomances of `EvalFpCoc` which altered the clusters of conjugacy
#! classes of the groups can be recreated in advance via the list <A>desclist</A>.
#! If no such splitis possible a warning is printed and <A>Ids</A> is returned.
#! @BeginExampleSession
#! gap> CocSplitRoutine([5,6,7], 512, [], 1);
#! rec( desc := [104003], fp := [ 1214, 16 ], next := [ [ 5 ],
#!      rec( desc := [40204005], fp := [ 20792, 46881 ],
#!           next := [ [ 6 ], [ 7 ] ] ) ] )
#! gap> CocSplitRoutine([1529,1530,1531], 512, [], 2);
#! rec( desc := [ 209003 ], fp := [ 4, 14 ], next :=
#!    [ rec( desc := [ 107003, 212007 ], fp := [ 14, 618 ],
#!     next := [ [ 1529 ], [ 1530 ] ] ), [ 1531 ] ] )
#! @EndExampleSession
#DeclareGlobalFunction("CocSplitRoutine");

#! @Arguments CL [,opt]
#! @Returns A list of pairs each containing the path of the respective cluster
#! and the subbranch resulting from `CocSplitRoutine`.
#! @Description
#! Tries to split each cluster in <A>CL</A> via <Ref Func="CocSplitRoutine" Style="Text"/>.
#! <A>CL</A> must be a cluster list produced by <Ref Func="ClusterList" Style="Text"/>.
#! This function
#! accepts a record <A>opt</A> of options with the following content:
#! * <A>pack</A>: A boolean that determines if <Ref Func="IdPGroup_Pack" Style="Text"/>
#!                should be applied to the result.
#! * <A>order</A>: An integer giving the order of the groups with ids in <A>CL</A>.
#! * <A>iterate</A>: An integer that determines the maximal number of iterations
#!                   done while searching parameters.
#! * <A>verbose</A>: An boolean that determines if progress should be printed.
#! The default value of <A>opt</A> is <A>rec(pack</A>:=<K>true</K>, <A>order</A>:=512,
#! <A>iterate</A>:=1,<A>verbose</A>:=<K>true</K><A>)</A>.
#! @BeginExampleSession
#! gap> tree := TestOnClusterList([[3,5,6,7,8]],"CocList",rec(verbose:=false));;
#! gap> CL := ClusterList(tree);
#! [ rec( descl := [  ], ids := [ 3, 8 ], path := [ 337 ], size := 2,
#!        tests := [ "CocList" ] ),
#!   rec( descl := [  ], ids := [ 5, 6, 7 ], path := [ 32173 ], size := 3,
#!        tests := [ "CocList" ] ) ]
#! gap> TR := CocTestOnClusterList(CL,rec(verbose:=false));;
#! gap> AddClusterTestResults(tree, TR);;
#! gap> ClusterList(tree);
#! [ rec( descl := [ [ 302004 ] ], ids := [ 3 ], path := [ 337, 1363 ], size := 1,
#!        tests := [ "CocList", "" ]),
#!   rec( descl := [ [ 302004 ] ], ids := [ 8 ], path := [ 337, 46760 ], size := 1,
#!        tests := [ "CocList", ""  ]),
#!   rec( descl := [ [ 104003 ] ], ids := [ 5 ], path := [ 32173, 1214 ],
#!        size := 1, tests := [ "CocList", ""  ] ),
#!   rec( descl := [ [ 104003 ], [ 40204005 ] ], ids := [ 6 ],
#!        path := [ 32173, 16, 20792 ], size := 1, tests := [ "CocList", ""  ] ),
#!   rec( descl := [ [ 104003 ], [ 40204005 ] ], ids := [ 7 ],
#!        path := [ 32173, 16, 46881 ], size := 1, tests := [ "CocList", ""  ] ) ]
#! @EndExampleSession
DeclareGlobalFunction("CocTestOnClusterList");


#! @Arguments CL, order, maxl
#! @Returns A list consisting of pairs of a list of ids and a record containing the
#! parameters for a random presentation test via `ID_GROUP_FUNCS[18]`.
#! @Description
#! Determines the needed parameters for the groups of size <A>order</A> in the
#! clusters <A>cl</A> of <A>CL</A>.
#! Creates the clusters of conjugcy classes and alters them accordingly to the
#! <A>cl.descl</A>. Afterwards minimal generators for all groups and their position
#! among the clusters of conjugacy classes. If the positions do not coincide, the
#! positions of the generators of the first group are selected and the generators
#! of the other groups are selected from the same clusters. Otherwise the positions
#! and generators are sorted by the positions. Sequently the function tries to refine
#! the corresponding clusters to limit the choices to choose from and repeat the process
#! until either the number of refinments is equal or larger than <A>maxl</A> or no more
#! refinments could be found.
#! @BeginExampleSession
#! gap> ParametersRandPresentTest([rec(descl:=[], ids:=[1367, 1371])], 512, 0);
#! [ [ [ 1367, 1371 ], rec( descl := [  ],
#!      fp := [ 39080, 80814 ], func := 18, pos := [ 8, 10 ] ) ] ]
#! gap> ParametersRandPresentTest([rec(descl:=[], ids:=[1367, 1371])], 512, 1);
#! [ [ [ 1367, 1371 ], rec( descl := [ 106003 ],
#!      fp := [ 39080, 80814 ], func := 18, pos := [ 9, 11 ] ) ] ]
#! @EndExampleSession
DeclareGlobalFunction("ParametersRandPresentTest");
