#
# IdPGroup: Implements identification functions for different $p$-groups.
#
# Implementations
#


#####################################################################################
##
## returns an integer that encodes the content of the provided list
##
InstallGlobalFunction(IdPGroup_Pack, function(list)
    local r, i;

    if Length(list) = 0 then
        return 0;
    fi;
    list := Flat(list);
    r := list[1] mod 99661;
    for i in list{[2..Length(list)]} do
        r := (r*10+i) mod 99661;
    od;
    return r;
end);


#####################################################################################
##
##  Computes all conjugacyclasses of the group G. All classes of the same length and
##  the same order of its elements are then saved in a list. All these list are then
##  stored in an additional list and returned.
##
InstallGlobalFunction(ClusterConjClasses, function(G)
    local asList, classes, classtyps, sclasstyps, coc, i, j;

    asList := AttributeValueNotSet(AsSSortedList, G);

    classes := OrbitsDomain(G, asList);
    classtyps := List(classes, x->[Order(x[1]), Length(x)]);
    sclasstyps := Set(classtyps);
    #coc is clusters of conjugacy classes
    coc := List(sclasstyps, x->[ ]);
    for i in [1..Length( sclasstyps)] do
        for j in [1..Length(classes)] do
            if sclasstyps[i] = classtyps[j] then
                Add(coc[i], classes[j]);
            fi;
        od;
    od;

    return coc;
end);


#####################################################################################
##
## Returns the cycle-structure of the permutation on the elements of coc induced by
## the powermap x->x^n. First we determine the permutation within a cluster. Classes
## of a cluster that are fixed are examined afterwards on their own.
##
InstallGlobalFunction(PowerMapCocCycSt, function(coc, n)
    local L, l, im, pi, r, i, CSP;

    L:=[];

    #Determine permutation for each cluster of conjugacy classes
    for l in [2..Size(coc)] do
        L[l-1]:=[];
        #Determine indices of powered classes in cluster
        im := List([1..Size(coc[l])], i ->
        Filtered([1..Size(coc[l])],  j -> coc[l][i][1]^n in coc[l][j]));
        pi := MappingPermListList([1..Size(coc[l])], Flat(im));
        for i in [1..Size(coc[l])] do
            if i^pi = i then
                #Determine permuation within fixed classes
                Add(L[l-1], PermListList(coc[l][i],List(coc[l][i],c->c^n)));
            fi;
        od;
        Add(L[l-1], pi);
    od;

    #Turn permutations into integers by CycleStructurePerm and replace unbind with 0
    for l in [1..Size(L)] do
        for r in [1..Size(L[l])] do
            CSP := CycleStructurePerm(L[l][r]);
            L[l][r] := List([1..Size(CSP)],i->GetWithDefault(CSP,i,0));
        od;
    od;
    return L;
end);


#####################################################################################
##
##  Returns a list of all clusters of groups in a given tree. When initializing the
##  only required argument is tree. The information stored for each cluster include
##  the size of the cluster, the path through the tree, a lists of descriptions for
##  performed coc-tests and the ids of the groups.
##
InstallGlobalFunction(ClusterList, function(arg...)
    local CL, tree, opt, cl, LG, LpC, Lgen, newopt, i;
    CL:=[];

    tree := arg[1];

    if Length(arg) > 1 then
        opt := arg[2];
        if not IsBound(opt.path) then opt.path := []; fi;
        if not IsBound(opt.descl) then opt.descl := []; fi;
        if not IsBound(opt.tests) then opt.tests := []; fi;
        if not IsBound(opt.pClassAndRank) then opt.pClassAndRank := false; fi;
    else
        opt := rec(path := [], descl := [], tests := [], pClassAndRank := false);
    fi;

    #If a cluster is found, summarise all gathered information and return as record
    if not IsRecord(tree) then
        cl := rec(path := opt.path,
                  descl := opt.descl,
                  tests := opt.tests,
                  ids := tree);

        if IsInt(tree) then
            cl.ids := [tree];
        else
            cl.ids := tree;
        fi;

        cl.size := Size(cl.ids);

        if opt.pClassAndRank and cl.size > 1 then
            LG := List(tree, id -> SmallGroup(512,id));
            LpC := List(LG, G -> Size(PCentralSeries(G))-1);
            if Size(DuplicateFreeList(LpC)) <> 1 then
                cl.pClass := LpC;
            else
                cl.pClass := LpC[1];
            fi;

            Lgen := List(LG, G -> Size(MinimalGeneratingSet(G)));
            if Size(DuplicateFreeList(Lgen)) <> 1 then
                cl.rank := Lgen;
            else
                cl.rank := Lgen[1];
            fi;
        fi;
        return cl;

    elif IsBound(tree.func) and tree.func <> 12 then
        cl := rec(path := opt.path,
                  descl := opt.descl,
                  tests := Concatenation(opt.tests, [tree.func]));

        if IsBound(tree.next) then
            cl.ids := tree.next;
            cl.fp := tree.fp;
        else
            cl.ids := tree.fp;
        fi;
        cl.size := Size(cl.ids);

        if IsBound(tree.pos) then cl.pos := tree.pos; fi;

        return cl;

    else
        #If we still have branches to follow, gather relevant info and proceed
        for i in [1..Size(tree.next)] do
            newopt := rec(path := ShallowCopy(opt.path),
                          descl := ShallowCopy(opt.descl),
                          tests := ShallowCopy(opt.tests),
                          pClassAndRank := opt.pClassAndRank);
            Add(newopt.path, tree.fp[i]);
            if IsBound(tree.desc) then
                Add(newopt.descl, tree.desc);
            fi;
            if IsBound(tree.test) then
                Add(newopt.tests, tree.test);
            elif IsBound(tree.func) then
                Add(newopt.tests, tree.func);
            else
                Add(newopt.tests,"");
            fi;
            Add(CL, ClusterList(tree.next[i], newopt));
        od;
    fi;

    return Flat(CL);
end);


#####################################################################################
##
##  Performs a test on the group G of size order.
##  This function accepts a record opt of options with the following content
##  - pack: A boolean that determines if IdPGroup_Pack() should be applied to the result
##  The default value is opt.pack := true.
##
InstallGlobalFunction(TestOnGroup, function(G, test, opt...)
    local order, fp, CS, asList, coc, M, p, C, Q, z, CCS, L, T, N, A, O, i;

    #Process handled options
    if Size(opt) = 0 then
        #If not options are given, create default options
        opt := rec(pack := true);
    elif IsRecord(opt[1]) then
        #If options are given, fill unbound otions with default values
        opt := opt[1];
        if not IsBound(opt.pack) then opt.pack := true; fi;
    else
        Error("Inadmissable option: opt must be empty or a record\n");
    fi;

    order := Order(G);

    if not IsPcGroup(G) then G := Image(IsomorphismPcGroup(G)); fi;

    if test = "Parent" then
        #Identify the parent of G
        CS := PCentralSeries(G);
        fp :=  IdGroup(FactorGroupNC(G, CS[Size(CS)-1]));

    elif test = "Rank" then
        fp := Rank(G);

    elif test = "PClass" then
        fp := PClassPGroup(G);

    elif test = "Center" then
        fp := AbelianInvariants(Center(G));

    elif test = "AbelInv" then
        #Calculate abelian invaraints
        fp := List(DerivedSeriesOfGroup(G),x -> [Size(x), AbelianInvariants(x)]);

    elif test = "Weights" then
        fp :=  LGWeights(SpecialPcgs(Pcgs(G)));

    elif test = "LCSId" then
        #Identify the subgroups of lower-central series
        CS := LowerCentralSeries(G);
        fp := List(CS{[2..Size(CS)]}, IdGroup);

    elif test = "UCSId" then
        #Identify the subgroups of lower-central series
        CS := UpperCentralSeries(G);
        fp := List(CS{[2..Size(CS)]}, IdGroup);

    elif test = "PCSId" then
        #Identify the subgroups of p-lower-central series
        CS := PCentralSeries(G);
        fp := List(CS{[2..Size(CS)]}, IdGroup);

    elif test = "ElmOrds" then
        #Collect the orders of all elements of G
        asList := AttributeValueNotSet(AsSSortedList, G);
        fp := Collected(List(asList, Order));

    elif test = "CocList" then
        #Collect all length of conjugacy classes and order of their elements
        coc := ClusterConjClasses(G);
        fp := List(coc{[2..Length(coc) ]}, x->[Length(x[1]), Length(x)]);

    elif test = "PMCycSt" then
        #Examine the cyclestructure of a powermap on clusters in coc
        if not IsBound(coc) then coc := ClusterConjClasses(G); fi;
        fp := Flat(PowerMapCocCycSt(coc, 3));

    elif test = "SpSubId" then
        #Identifies the Frattini and proper subgoups of lower and upper central series
        fp := [IdGroup(FrattiniSubgroup(G))];
        Add(fp,List(Filtered(LowerCentralSeries(G),x->Order(x)<order),IdGroup));
        Add(fp,List(Filtered(UpperCentralSeries(G),x->Order(x)<order),IdGroup));

    elif test = "MaxSubId" then
        #Identify and collect the maximal subgroups
        M := MaximalSubgroups(G);
        fp := [];
        for i in [1..Size(M)] do
            if IdGroupsAvailable(Order(M[i])) then
                Add(fp, IdGroup(M[i]));
            else
                #This is just for using this test in the 'OutId'-test
                Add(fp, [Order(M[i]),0]);
            fi;
        od;
        fp := Collected(fp);

    elif test = "SubId" then
        #Identify conjugacyclasses of subgroups
        CCS := Filtered(ConjugacyClassesSubgroups(G),c->Size(c[1])<order);
        fp := Collected(List(CCS,c->[Size(c), IdGroup(c[1])]));

    elif test = "MaxFactId" then
        #Identify and collect the maximal factors
        p := PrimePGroup(G);
        C := Center(G);
        M := List(Filtered(AllSubgroups(C), x -> Size(x)=p), x -> G/x);
        fp := [];
        for i in [1..Size(M)] do
            if IdGroupsAvailable(Order(M[i])) then
                Add(fp, IdGroup(M[i]));
            else
                #This is just for using this test in the 'OutId'-test
                Add(fp, [Order(M[i]),0]);
            fi;
        od;
        fp := Collected(fp);

    elif test = "CentQuot" then
        #Identify and collcet the central quotients of G
        C := Filtered(Center(G),z -> Order(z)>1);
        Q := List(C,z -> FactorGroupNC(G,Group(z)));
        fp := [];
        for i in [1..Size(Q)] do
            if IdGroupsAvailable(Order(Q[i])) then
                Add(fp, IdGroup(Q[i]));
            else
                #This is just for using this test in the 'OutId'-test
                Add(fp, [Order(Q[i]),0]);
            fi;
        od;
        fp := Collected(fp);

    elif test = "LCSFactId" then
        CS := PCentralSeries(G);
        C := Filtered(CS[Size(CS)-1], c -> c <> One(G));
        fp := List(C, c -> IdGroup(FactorGroupNC(G, Group(c)))[2]);
        fp := Collected(fp);

    elif test = "FactId" then
        #Identify all proper factors
        N := Filtered(NormalSubgroups(G),x->Size(x)>1);
        fp := Collected(List(N,n->IdGroup(FactorGroupNC(G,n))));

    elif test = "OutId" then
        #Identify, if possible, outer automorphism group of G
        A := PcGroupAutPGroup(AutomorphismGroupPGroup(G));
        O := A/InnerAutGroupPGroup(A);
        if IdGroupsAvailable(Size(O)) then
            fp := IdGroup(O);
        elif Order(O) = order then
            fp := [Size(O),
            TestOnGroup(O, "ElmOrds", rec(pack:=false)),
            TestOnGroup(O, "CocList", rec(pack:=false)),
            TestOnGroup(O, "MaxSubId",rec(pack:=false)),
            TestOnGroup(O, "CentQuot",rec(pack:=false))];
        else
            fp := [Size(O),
            TestOnGroup(O, "ElmOrds", rec(pack:=false)),
            TestOnGroup(O, "CocList", rec(pack:=false))];
        fi;

    elif test = "LattEqv" then
        #Identify conjugacyclasses of subgroups and their maximalsubgroups and minimal
        #supergroups
        L := LatticeSubgroups(G);
        CCS := ConjugacyClassesSubgroups(L);
        fp := List(CCS,x->0);
        #Identify conjugacyclasses of subgroups
        for i in [1..Size(CCS)] do
            if Size(Representative(CCS[i])) < order then
                fp[i] := [[IdGroup(Representative(CCS[i])), Size(CCS[i])]];
            else
                fp[i] := [[[order, 0], 1]];
            fi;
        od;
        M := [];
        M[1] := MaximalSubgroupsLattice(L);
        M[2] := MinimalSupergroupsLattice(L);
        #Identify maximal subgroups and minimal supergroups respectivly
        for i in [1..Size(fp)] do
            T := Collected(List(M[1][i],x->x[1]));
            Add(fp[i], Collected(List(T,t->fp[t[1]][1])));
            T := Collected(List(M[2][i],x->x[1]));
            Add(fp[i], Collected(List(T,t->fp[t[1]][1])));
        od;
        fp := SortedList(fp);

    else
        Error("Please enter a valid test! ", test, " is not recognized.");
    fi;

    if opt.pack and not IsInt(fp) then fp := IdPGroup_Pack(fp); fi;

    return fp;
end);

#####################################################################################
##
##  Performs a test on the groups of clusters in the list CL. The tests are performed
##  by TestOnGroup. CL could either be a cluster list produced by ClusterList
##  or be a list of lists containing ids. In the former case the output is a list of
##  pairs containg the path of a cluster and the subbrunch resulting from the test. In
##  the latter case only a list of subbranches is returned.
##  This function accepts a record opt of options with the following content
##  - pack: a boolean that is handed to TestOnGroup
##  - ign1cl: a boolean that determines if clusters of size 1 should be ignored
##  - order: an integer giving the order of the groups with ids in CL
##  - verbose: an boolean that determines if a progress should be printed
##  The default value is pack:=true, ign1cl:=true, order:=512, verbose:=true.
##
InstallGlobalFunction(TestOnClusterList, function(CL, test, opt...)
    local TR, cl, fp, id, G, PCS, asList, coc, M, C, Q, z, CCS, N, A, O, branch, i, pos, prog, IdList;

    #Process provided options
    if Size(opt) = 0 then
        #If not options are given, create default options
        opt := rec(pack := true, ign1cl := true, order := 512, verbose := true,
                   notetest := true);
    elif IsRecord(opt[1]) then
        #If options are given, fill unbound otions with default values
        opt := opt[1];
        if not IsBound(opt.pack) then opt.pack := true; fi;
        if not IsBound(opt.ign1cl) then opt.ign1cl := true; fi;
        if not IsBound(opt.order) then opt.order := 512; fi;
        if not IsBound(opt.verbose) then opt.verbose := true; fi;
        if not IsBound(opt.notetest) then opt.notetest := true; fi;
    else
        Error("Inadmissable option: opt must be empty or a record\n");
    fi;

    #Check if CL is just a list of ids and replace them accordingly
    for i in [1..Size(CL)] do
        if not IsRecord(CL[i]) then
            CL[i] := rec(size := Length(CL[i]), ids := CL[i], path := []);
        fi;
    od;

    TR := [];
    prog := 0;
    IdList := Flat(List(CL,cl->cl.ids));

    for cl in CL do
        if opt.ign1cl and cl.size = 1 then continue; fi;

        branch := rec(fp:=[], next:=[]);

        for id in cl.ids do
            #Print progress if opt.verbose=true
            if opt.verbose and prog <> QuoInt(Position(IdList,id)*10,Size(IdList)) then
                prog := QuoInt(Position(IdList,id)*10,Size(IdList));
                Print(prog, "0% \n");
            fi;

            G := SmallGroup(opt.order, id);
            fp := TestOnGroup(G, test, opt);

            #Find position to insert current group in branch
            pos := Position(branch.fp, fp);
            if pos = fail then
                #If fp is new, create new entries in .fp and .next of branch
                Add(branch.fp, fp);
                Add(branch.next, []);
                pos := Length(branch.next);
            fi;
            #Insert id according to pos of fp in branch
            Add(branch.next[pos], id);
        od;

        #If the used test should be noted, we omit clusters, that do not split
        if opt.notetest then
           if Size(branch.fp) = 1 then continue; fi;
           branch.test := test;
        fi;

        #If the current cluster is not part of a search tree (has no path in it),
        #simply return the constructed branch otherwise return pair of path and branch
        if Size(cl.path) = 0 then
            Add(TR, branch);
        else
            Add(TR, [cl.path, branch]);
        fi;
    od;

    #Chatch case of initializing search tree
    if Size(TR) = 1 and IsRecord(TR[1]) then
        TR := TR[1];
    fi;

    #Print results into file with opt.filename if wanted
    if IsBound(opt.filename) and opt.filename <> "" then
        PrintTo(StringFormatted("{}_{}.txt", opt.filename, test), "TR:=", TR, ";");
    fi;

    return TR;
end);

#####################################################################################
##  Extends tree by the test results stored in TR. TR is a list that a path and a
##  branch (a tree of depth one), extending the corresponding cluster.
##
InstallGlobalFunction(AddClusterTestResults, function(tree, TR)
    local tr, branch, fp, pos;

    for tr in TR do
        branch := tree;

        #Follow path to cluster
        for fp in tr[1]{[1..Size(tr[1])-1]} do
            pos := Position(branch.fp, fp);
            if IsBool(pos) then Error("Path not contained in tree!\n"); fi;
            branch := branch.next[pos];
        od;

    #Replace old cluster with extension
    branch.next[Position(branch.fp, tr[1][Size(tr[1])])] := tr[2];
    od;

    return tree;
end);

#####################################################################################
##
##  Builds a search tree for the groups with ids in N or the first N groups, if N is
##  a integer, of size order, using the tests with TestOnClusterList.
##
InstallGlobalFunction(BuildSearchTree, function(N, order, tests)
    local tree, test, CL, TR;

    if IsInt(N) then N:=[[1..N]]; fi;
    if not IsList(N[1]) then N:=[N]; fi;

    tree := TestOnClusterList(N, tests[1], rec(order := order, verbose := false));

    for test in tests{[2..Size(tests)]} do
        CL := ClusterList(tree);
        TR := TestOnClusterList(CL, test, rec(order := order, verbose := false));
        AddClusterTestResults(tree, TR);
    od;

    return tree;
end);

#####################################################################################
##
##  Does a parameter search for desc such that evaluating EvalFpCoc on all clusters
##  of Coc results into at least 2 different values. Therefore using desc as an
##  invaraint in a search tree shrinks down the size of a leaf made of Coc.
##
InstallGlobalFunction(FindParametersForCocTest, function(Coc, paralist, it, maxit, opt...)
    local Para, N, level, target, ord, len, ind, paral, para, lfp, NCoc, res;

    N := Size(Coc[1]);

    if Length(opt) = 0 then
        opt := rec();
        opt.target := [2..N];
        opt.maxlevel := 5;
    else
        opt := opt[1];
        if not IsBound(opt.target) then opt.target := [2..N]; fi;
        if not IsBound(opt.maxlevel) then opt.maxlevel := 5; fi;
    fi;

    Para := [];
    level := 1;
    target := Intersection([2..N], opt.target);
    ord := List(Coc[1], x -> Order(x[1][1]));
    len := List(Coc[1], x -> Size(x[1]));
    ind := Filtered([2..N], j -> len[j]>1);
    paral := [];

    #Go through all kinds of parameters seperatly
    while level <= opt.maxlevel  do
        if level = 1 then
            #Check if raising rep. of coc[i] to odd power  lands in original class
            Para := Concatenation(List(Filtered(target, i -> ord[i] > 2), i ->
            List(Filtered([2..ord[i]],j->Gcd(ord[i],j)=1), j -> [1,i,j])));

        elif level = 2 then
            #Check if rep. of coc[i] are roots of elements in coc[j]
            Para := Concatenation(List(target, i ->
            List(Filtered([2..N], j -> ord[j] < ord[i] and len[j] <= len[i]), j -> [2,i,j])));

        elif level = 3 then
            #Check if rep. of coc[i] are powers of elements in coc[j]
            Para := Concatenation(List(target, i ->
            List(Filtered([2..N], j -> ord[j] > ord[i] and len[j] >= len[i]), j -> [3,i,j])));

        elif level = 4 then
            #Check if rep. is the word [a,b]a^2 made of elements of coc[]
            Para := Concatenation(List(target, i -> Concatenation(List(ind, j -> List(ind, l -> [4,i,j,l])))));

        elif level = 5 then
            Para := Concatenation(List(target, i -> Concatenation(List(ind, j -> List(ind, l -> [5,i,j,l])))));
        fi;

        #Test if subset of possible parameters has a 'good' element
        for para in Para do
            lfp := List(Coc, coc -> EvalFpCoc(coc, para));
            if it > 0 and Size(DuplicateFreeList(List(lfp,fp -> IdPGroup_Pack(Collected(fp))))) > 1 then
                Add(paralist, para);
                return [List(lfp,fp -> IdPGroup_Pack(Collected(fp))), paralist];
            fi;

            if Size(DuplicateFreeList(lfp[1])) > 1 then
                Add(paral, para);
            fi;
        od;
        level := level + 1;
    od;

    if it = 0 then return paral; fi;

    if it < maxit then
        #Iterate through parameters that split a cluster
        for para in paral do
            lfp := List(Coc, coc -> EvalFpCoc(coc, para));
            NCoc:= List([1..Size(Coc)], i -> AlterCocAccordingToFp(Coc[i], para, lfp[i]));
            res := FindParametersForCocTest(NCoc, Concatenation(paralist, [para]),
                                        it+1, maxit, opt);
            if res <> fail then
                return res;
            fi;
        od;
    fi;

    #If no parameter yields an improvment raise warning and return fail
    Print("Warning: No suitable parameter found!\n");
    return fail;
end);

#####################################################################################
##
##  De- or encodes the description desc for EvalFPCoc, depending if youe provide
##  an integer (decodes to list) or a list of integers (encodes to int)
##
InstallGlobalFunction(DeEncodeDesc, function(desc)
    local ldesc;

    if IsList(desc) then
        while Length(desc) > 2 do
            desc[1]:= Remove(desc, 1) * 100 + desc[1];
        od;
        desc:= desc[1] * 1000 + desc[2];

    elif IsInt(desc) then
        ldesc := [desc mod 1000];
        desc := QuoInt(desc, 1000);
        while desc > 0 do
            Add(ldesc, desc mod 100);
            desc := QuoInt(desc, 100);
        od;
        desc := Reversed(ldesc);
    fi;
    return desc;
end);

#####################################################################################
##
##  Alters coc according the result fp from EvalFPCoc evaluated with desc.
##
InstallGlobalFunction(AlterCocAccordingToFp, function(coc, desc, fp)
    local sfp, newcls, l, j;

    #Alter coc according to fp
    sfp := Set(fp);
    newcls := List(sfp, l -> []);
    for l in [1..Size(sfp)] do
        for j in [1..Size(fp)] do
            if sfp[l] = fp[j] then
                Add(newcls[l], coc[desc[2]][j]);
            fi;
        od;
    od;
    #Replace cluster desc[2] in coc by subclusters
    coc := Concatenation(coc{[1..desc[2]-1]}, newcls, coc{[desc[2]+1..Size(coc)]});

    return coc;
end);

#####################################################################################
##
##  Build a 1-level serachtree to distinguish the groups of order 512 with id
##  in Ids based on there behavior under EvalFpCoc. Past tests with EvalFpCoc
##  which altered the clusters of conjugacyclasses can be recreated via the
##  list desc. The function returns a record made of fp, next and desc.
##
InstallGlobalFunction(CocSplitRoutine, function(Ids, order, desclist, iterate)
    local Coc, i, descl, res, Lfp, tree, pos, desc;

    if Size(Ids) = 1 then return Ids; fi;

    #Build list of cocs according to previous tests documented in desclist
    Coc := List(Ids, id -> ClusterConjClasses(SmallGroup(order, id)));
    for i in [1..Size(Coc)] do
        for desc in desclist do
            desc := DeEncodeDesc(desc);
            Coc[i] := AlterCocAccordingToFp(Coc[i], desc, EvalFpCoc(Coc[i], desc));
        od;
    od;

    #Find 'good' parameters and calculate EvalFpCoc together
    res := FindParametersForCocTest(Coc, [], 1, iterate);

    #If parametersearch fails return list of ids
    if res = fail then return Ids; fi;

    Lfp := res[1]; descl := res[2];

    #Transfer results of EvalFpCoc into tree
    tree := rec(fp:=[], next:=[], desc:=[]);

    for i in [1..Size(Ids)] do
        pos := Position(tree.fp, Lfp[i]);
        if IsBool(pos) then
            Add(tree.fp, Lfp[i]);
            tree.next[Position(tree.fp, Lfp[i])] := [Ids[i]];
        else
            Add(tree.next[pos], Ids[i]);
        fi;
    od;

    #Encode description of test
    for desc in descl do
        Add(tree.desc, DeEncodeDesc(desc));
    od;

    for i in [1..Size(tree.next)] do
        tree.next[i] := CocSplitRoutine(tree.next[i], order,
                        Concatenation(desclist, tree.desc), iterate);
    od;
    return tree;
end);

#####################################################################################
##
##  Tries to split the clusters of clusters in the list CL via CocSplitRoutine.
##  CL needs to be a cluster list produced by ClusterList. The output is a list of
##  pairs containg the path of a cluster and the subbrunch resulting from the test.
##  This function accepts a record opt of options with the following content
##  - pack: a boolean that is handed to TestOnGroup
##  - order: an integer giving the order of the groups with ids in CL
##  - verbose: an boolean that determines if a progress should be printed
##  The default value is pack:=true, ign1cl:=true, order:=512, verbose:=true.
##
InstallGlobalFunction(CocTestOnClusterList, function(CL, opt...)
    local prog, TR, cl, tree;

    #Process handled options
    if Size(opt) = 0 then
        #If not options are given, create default options
        opt := rec(pack := true, order := 512, iterate := 1, verbose := true);
    elif IsRecord(opt[1]) then
        #If options are given, fill unbound otions with default values
        opt := opt[1];
        if not IsBound(opt.pack) then opt.pack := true; fi;
        if not IsBound(opt.order) then opt.order := 512; fi;
        if not IsBound(opt.iterate) then opt.iterate := 1; fi;
        if not IsBound(opt.verbose) then opt.verbose := true; fi;
    else
        Error("Inadmissable option: opt must be empty or a record\n");
    fi;

    prog := 0;
    TR := [];

    for cl in CL do

        #Print progress if opt.verbose=true
        if opt.verbose and prog <> QuoInt(Position(CL,cl)*10,Size(CL)) then
            prog := QuoInt(Position(CL,cl)*10,Size(CL));
            Print(prog, "0% \n");
        fi;

        #Ignore clusters of size one
        if cl.size = 1 then continue; fi;

        #Split a cluster and save resulting tree
        tree := CocSplitRoutine(cl.ids, opt.order, Flat(cl.descl), opt.iterate);

        #If result is a list (of ids), the cluster couldn't be
        #splited and result is omitted
        if IsList(tree) then continue; fi;

        Add(TR, [cl.path, tree]);
    od;

   if IsBound(opt.filename) then
        opt.filename := StringFormatted("CocTest_{}.txt", opt.filename);
        PrintTo(opt.filename, "TR:=", TR, ";");
    else
        return TR;
    fi;
end);

#####################################################################################
##
##  Determine the parameters for a random presentation test for the groups in the
##  clusters of CL
##
InstallGlobalFunction(ParametersRandPresentTest, function(CL, order, maxl)
    local TR, prog, cl, G, gens, Coc, desc, descl, stop, pos, perm, p, para, fp, i;
    TR := [];
    prog := 0;

    for cl in CL do
        #if cl.size = 1 then continue; fi;

        #if prog <> QuoInt(Position(CL,cl)*10,Size(CL)) then
        #    prog := QuoInt(Position(CL,cl)*10,Size(CL));
        #    Print(prog, "0% \n");
        #fi;

        G := List(cl.ids, id-> SmallGroup(order, id));
        gens := List(G, MinimalGeneratingSet);

        #Alternate Coc according to performed tests
        Coc := List(G,ClusterConjClasses);
        for desc in Flat(cl.descl) do
            desc := DeEncodeDesc(desc);
            fp := EvalFpCoc(Coc[1], desc);
            for i in [1..Size(Coc)] do
                Coc[i] := AlterCocAccordingToFp(Coc[i], desc, fp);
            od;
        od;

        descl := [];

        repeat
            stop := true;

            #Determine position of generators in clusters of conjugacy classes
            pos := List([1..Size(gens)],
                i -> Flat(List(gens[i],
                    gen -> Filtered([1..Size(Coc[i])], j -> gen in Flat(Coc[i][j])))));

            #Check if positions coincide (not necessarly in the same order)
            if Size(DuplicateFreeList(List(pos,Collected))) > 1 then
                Print("Positions of generating elements do not coincide!\n");
                #If positions do not coincide, use pos[1] and select new generators for remaining
                pos := List([1..Size(pos)],i -> pos[1]);
                for i in [2..Size(gens)] do
                    repeat
                        gens[i] := List(pos[i], j -> Random(Flat(Coc[i][j])));
                    until Size(GroupByGenerators(gens[i])) = Size(G[i]);
                od;

            else
                #If positions coincide, sort them and generators
                for i in [1..Size(gens)] do
                    perm := Sortex(pos[i]);
                    gens[i] := Permuted(gens[i], perm);
                od;
            fi;

            pos := pos[1];

            #Iterate through positions of generators from larges to smallest
            for p in Reversed(SortedList(pos)) do

                #Check if maximal length of descl is reached
                if Length(descl) >= maxl then break; fi;

                #Look for parameters that split Coc[p]
                para := FindParametersForCocTest(Coc, [], 0, 0, rec(targer:=[]));

                if Size(para) > 0 then
                    stop := false;
                    Add(descl, para[1]);
                    fp := EvalFpCoc(Coc[1], para[1]);
                    for i in [1..Size(Coc)] do
                        Coc[i] := AlterCocAccordingToFp(Coc[i], para[1], fp);
                    od;
                fi;
            od;

        until stop;

        #Determine fingerprints of presentation that results from pcgs out of gens
        fp:=List([1..Size(G)],i -> CodeGenerators(gens[i], SpecialPcgs(G[i])).code mod 99661);

        Add(TR, [cl.ids, rec(fp:=fp, pos:=pos, func := 18, descl := List(descl, DeEncodeDesc))]);
    od;

    return TR;
end);

#####################################################################################
##
##  Loads the saved serachtree ID_GROUP_512_TREE
##
Read(Filename(DirectoriesPackageLibrary("idpgroup",""),"data/Searchtree/ID_GROUP_512_TREE.g"));

Read(Filename(DirectoriesPackageLibrary("idpgroup",""),"data/ID_GROUP_512_INFOREC_F18.g"));

InstallGlobalFunction(LoadTotalTree, function()
    local LoadBranches;

    LoadBranches := function(folder, tree)
        local i;

        if not IsString(tree) and IsList(tree) then
            return tree;
        else
            for i in [1..Size(tree.next)] do
                if IsString(tree.next[i]) then
                    Read(Concatenation(folder, "/", tree.next[i]));
                fi;
                tree.next[i] := LoadBranches(folder, tree.next[i]);
            od;
        fi;
        return tree;
    end;

    return LoadBranches(Filename(DirectoriesPackageLibrary("idpgroup",""),"data/Searchtree/"), ID_GROUP_512_TREE);
end);


#####################################################################################
##
##  Identifies the group G of Order 512.
##
InstallGlobalFunction(IdGroup512 , function(G, opt...)
    local branch, fp, desc, pos, coc, res, CG, CT, GT, id, L, inforec;

    #Process handled options
    if Size(opt) = 0 then
        #If not options are given, create default options
        opt := rec(anupq := false, path := false);
    elif IsRecord(opt[1]) then
        #If options are given, fill unbound otions with default values
        opt := opt[1];
        if not IsBound(opt.anupq) then opt.anupq := false; fi;
        if not IsBound(opt.path) then opt.path := false; fi;
    else
        Error("Inadmissable option: opt must be empty or a record\n");
    fi;

    if opt.path then opt.path := rec(fp:=[], tests:=[], pos:=[]); fi;

    if not IsBound(opt.tree) then
        if not IsBound(ID_GROUP_512_TREE) then
            Print("Loading 'ID_GROUP_512_TREE'\n");
            ID_GROUP_512_TREE := rec(fp:=[],next:=[]);
            Read(Filename(DirectoriesPackageLibrary("idpgroup",""),"data/Searchtree/ID_GROUP_512_TREE.g"));
        fi;
        branch := ID_GROUP_512_TREE;
    else
        branch := opt.tree;
    fi;

    if not IsPcGroup(G) then
        G := Image(IsomorphismPcGroup(G));
    fi;

    #Iterate through tree as long we have not reached a leaf and we can test
    while IsRecord(branch) and (IsBound(branch.test) or IsBound(branch.desc)) do
        #Either perform a test on group or do coc-test
        if IsBound(branch.test) then
            fp := TestOnGroup(G, branch.test);
        else
            if not IsBound(coc) then coc := ClusterConjClasses(G); fi;
            for desc in branch.desc do
                fp := EvalFpCoc(coc, DeEncodeDesc(desc));
                coc := AlterCocAccordingToFp(coc, DeEncodeDesc(desc), fp);
            od;
            fp := IdPGroup_Pack(Collected(fp));
        fi;

        #Determine next branch to follow
        pos := Position(branch.fp, fp);

        if IsBool(pos) then
            Error("Group not found in tree.\n");
        fi;

        #Load next part of branch if necessary
        if IsString(branch.next[pos]) then
            Read(Filename(DirectoriesPackageLibrary("idpgroup",""),
            Concatenation("data/Searchtree/", branch.next[pos])));
        fi;


        if IsRecord(opt.path) then
            Add(opt.path.fp, fp);
            Add(opt.path.pos, pos);
            if IsBound(branch.test) then
                Add(opt.path.tests, branch.test);
            elif IsBound(branch.desc) then
                Add(opt.path.tests, branch.desc);
            fi;
        fi;

        branch := branch.next[pos];
    od;

    if Size(branch) = 1 then
        branch := branch[1];

    elif not opt.anupq then
        pos := Position(List(ID_GROUP_512_INFOREC_F18,x->x[1]),branch);
        if pos <> fail then
            branch := ID_GROUP_512_INFOREC_F18[pos];

            if not IsBound(coc) then coc := ClusterConjClasses(G); fi;

            if not IsBound(branch[2].descl) then branch[2].descl := []; fi;

            for desc in Flat(branch[2].descl) do
                desc := DeEncodeDesc(desc);
                fp := EvalFpCoc(coc, desc);
                coc := AlterCocAccordingToFp(coc, desc, EvalFpCoc(coc, desc));
            od;

            inforec := rec(coc := coc, branch := branch[2]);
            inforec := ID_GROUP_FUNCS[18](G, inforec);

            branch := branch[1][Position(branch[2].fp, inforec.fp)];
        else
            opt.anupq := true;
        fi;

    #Hardcoded non-brauer-pairs that can be distinguished by testing the charactertables
    elif branch in [[6316783, 6316787], [ 6537030, 6537041 ]] then
        CT := CharacterTable(SmallGroup(512, branch[1]));
        CG := CharacterTable(G);

        #Just test G and the first candidate
        if TransformingPermutationsCharacterTables(CG, CT) <> fail then
            branch := branch[1];
        else
            branch := branch[2];
        fi;


    elif opt.anupq and IsList(branch) and Size(branch) > 1 then
        for id in branch{[1..Size(branch)-1]} do
            GT := SmallGroup(512, id);
            if IsPqIsomorphicPGroup(G, GT) then
                branch := id;
            fi;
        od;

        if IsList(branch) then branch := Last(branch); fi;
    fi;

    if IsBool(opt.path) then
        return branch;
    else
        return [branch, opt.path];
    fi;
end);


InstallGlobalFunction(IdGroup512Exceptions, function()
    Read(Filename(DirectoriesPackageLibrary("idpgroup",""),"data/Id512Exceptions.g"));
    return BINS_OF_IDS;
end);


#####################################################################################
############################### Determining Siblings ################################
#####################################################################################

#####################################################################################
##
## Takes a list of bins with ids of groups of size order and performs test via
## TestOnGroup on them. Depending on the outcome a bin is split into smaller
##  bins according to the test.
##
InstallGlobalFunction(SplitBinsViaTest, function(Bins, order, test)
    local NewBins, bin, fps, newsubbins, id, G, M, i, fp, pos;

    NewBins := [];

    for bin in Bins do

        fps := [];
        newsubbins := [];

        for id in bin do
            G := SmallGroup(order, id);
            fp := TestOnGroup(G, test, rec(pack := false));

            pos := Position(fps, fp);
            if pos = fail then
                Add(fps, fp);
                Add(newsubbins, []);
                pos := Length(fps);
            fi;
            Add(newsubbins[pos], id);
        od;
        Append(NewBins, newsubbins);
    od;

    return NewBins;
end);


#####################################################################################
##
## Performs all necessary tests on all groups of size order to determine all sets of subgroup- and
## factor-equivalent (SFeq) groups.
##
InstallGlobalFunction(CalculateSiblings, function(order, verbose...)
    local Bins,tests, test, NewBins;

    if Length(verbose) = 0 then
        verbose := true;
    else
        verbose := verbose[1];
    fi;

    Bins := [[1..NumberSmallGroups(order)]];

    tests := ["MaxSubId", "SpSubId", "SubId", "MaxFactId", "FactId"];

    for test in tests do
        NewBins := SplitBinsViaTest(Bins, order, test);
        Bins := Filtered(NewBins, bin -> Size(bin) > 1);
        if verbose then
            Print("Test '", test, "' found following bins of size greater one:",
                  Collected(List(Bins,Size)), "\n");
        fi;

        if Size(Bins) = 0 then return Bins; fi;
    od;

    return Bins;
end);

#####################################################################################
##
##  Loads and returns a list of ids of subgroup- and factor-equivalent groups of
##  order size if available
##
InstallGlobalFunction(SiblingsIds, function(args...)
    local size, filename, ind;

    size := args[1];

    if size < 256 and not size in [60,120,128,160,168,180,189,192,240,243] then
        #Print("There are no siblings of order ", size, ".\n");
        return [];
    elif List(Collected(Factors(size)),x->x[2]) in [[1], [2], [3], [1,1]] then
        return [];
    elif size = 243 then
        return [[19, 20], [44, 45]];
    elif Size(Collected(Factors(size))) = 1 and Collected(Factors(size))[1][2] = 4 then
        return [[9, 10]];
    elif size in [128, 256, 512, 729] then
        filename := Concatenation("Siblings_", String(size),".g");
        filename := Concatenation("data/SiblingsData/",filename);
        Read(Filename(DirectoriesPackageLibrary("idpgroup",""), filename));

        if Length(args) = 1 then
            ind := [1..Length(BINS_OF_IDS)];
        elif Length(args) = 2 and IsList(args[2]) then
            ind := args[2];
            if not IsSubset([1..Length(BINS_OF_IDS)], ind) then
                Error("Please choose a subset of [1..", Length(BINS_OF_IDS),"] as the list of indicies");
            fi;
        else
            Error("SiblingsIds only expects at most 2 arguments");
        fi;

        return BINS_OF_IDS{ind};
    else
        Print("Siblings of size ", size, " are not documented yet.\n");
        return fail;
    fi;
end);

#####################################################################################
##
##  Loads and returns a list siblings of order size if available
##
InstallGlobalFunction(Siblings, function(args...)
    local Ids;

    if Length(args) = 1 then
        Ids := SiblingsIds(args[1]);
    else
        Ids := SiblingsIds(args[1], args[2]);
    fi;

    if Ids = fail then return fail; fi;

    return List(Ids, ids -> List(ids, id -> SmallGroup(args[1], id)));
end);


#####################################################################################
##
## Determines the Brauer pairs among the bins of ids of groups of size order listet in Bins.
##
InstallGlobalFunction(DetermineBrauerPairs, function(Bins, order)
    local BPs, bin, BP, CT, i, j, bp;
    BPs := [];


    for bin in Bins do
        if Size(bin) = 1 then continue; fi;

        BP := [[1]];
        CT := List(bin, id -> CharacterTable(SmallGroup(order, id)));

        for i in [2..Size(bin)] do
            for j in [1..Size(BP)] do
                if TransformingPermutationsCharacterTables(CT[i], CT[BP[j][1]]) <> fail then
                    #If CT[i] is equivalent to a known CT[j], add i to the Brauer pair BP[j]
                    Add(BP[j], i);
                    break;
                fi;

                #If CT[i] is not equivalent to known CTs, create new potential pair
                if j = Size(BP) then
                    Add(BP,[i]);
                fi;
            od;
        od;

        #Remove all 'Brauer pairs' of size one
        BP := Filtered(BP,x-> Size(x) > 1);

        for bp in BP do
            #Write ids of found Brauer pairs into list of all found Brauer pairs
            Add(BPs, bin{bp});
        od;
    od;

    return BPs;
end);


InstallGlobalFunction(CalculateStrongSiblings, function(order, verbose...)
    local bins;

    if Length(verbose) = 0 then
        verbose := true;
    else
        verbose := verbose[1];
    fi;

    bins := CalculateSiblings(order, verbose);
    return DetermineBrauerPairs(bins, order);
end);


#####################################################################################
##
##  Loads and returns a list of ids of subgroup- and factor-equivalent Brauer
##  pairs of groups of order size if available.
##
InstallGlobalFunction(StrongSiblingsIds, function(args...)
    local size, filename, ind;

    size := args[1];

    if size in List([1..7],i->2^i) then
        return [];
    elif size in [256, 512] then
        filename := Concatenation("StrongSiblings_", String(size),".g");
        filename := Concatenation("data/SiblingsData/",filename);
        Read(Filename(DirectoriesPackageLibrary("idpgroup",""), filename));

        if Length(args) = 1 then
            ind := [1..Length(BINS_OF_IDS)];
        elif Length(args) = 2 and IsList(args[2]) then
            ind := args[2];
            if not IsSubset([1..Length(BINS_OF_IDS)], ind) then
                Error("Please choose a subset of [1..", Length(BINS_OF_IDS),"] as the list of indicies");
            fi;
        else
            Error("StrongSiblingsIds only expects at most 2 arguments");
        fi;

        return BINS_OF_IDS{ind};
    else
        Print("Strong siblings of size ", size, " are not documented yet.\n");
        return fail;
    fi;
end);


#####################################################################################
##
##  Loads and returns a list strong siblings of order size if available
##
InstallGlobalFunction(StrongSiblings, function(args...)
    local Ids;

    if Length(args) = 1 then
        Ids := StrongSiblingsIds(args[1]);
    else
        Ids := StrongSiblingsIds(args[1], args[2]);
    fi;

    if Ids = fail then return fail; fi;

    return List(Ids, ids -> List(ids, id -> SmallGroup(args[1], id)));
end);

#####################################################################################
##
##  Splits list of ids of groups of size order in Bin, if their outer automorphism groups
##  are isomorphic, via IsPqIsomorphicPGroup from the anupq package
InstallGlobalFunction(SplitExactOutEqv, function(Bin, order)
    local OutEq, G, Aut, Out, OE, i, j, oe;

    OutEq := [];

    G := List(Bin, id -> SmallGroup(order, id));
    Aut := List([1..Size(G)], i -> PcGroupAutPGroup(AutomorphismGroupPGroup(G[i])));
    Out := List([1..Size(Aut)], i -> Aut[i]/InnerAutGroupPGroup(Aut[i]));

    OE := [[1]];

    for i in [2..Size(Bin)] do
        for j in [1..Size(OE)] do
            if IsPqIsomorphicPGroup(Out[i], Out[j]) = true then
                Add(OE[j], i);
                break;
            fi;

            #If CT[i] is not equivalent to known CTs, create new potential pair
            if j = Size(OE) then
                Add(OE,[i]);
            fi;
        od;
    od;

    #Remove all 'Brauer pairs' of size one
    OE := Filtered(OE, x -> Size(x) > 1);

    for oe in OE do
            #Write ids of found Brauer pairs into list of all found Brauer pairs
        Add(OutEq, Bin{oe});
    od;

    return OutEq;
end);

#####################################################################################
##
## Takes a list of bins with ids of groups of size order and evaluates which are outer-
## automorphism equivalent. If exact = true, sets of groups which could not be ruled out to
## be equivalent are testet via SplitExactOutEqv. Otherwise, these are simply included.
##
InstallGlobalFunction(BinsOfOutEqGroups, function(Bins, order, exact)
    local NewBins, bin, fps, newsubbins, potential, id, G, M, i, fp, pos;

    NewBins := [];

    for bin in Bins do

        fps := [];
        newsubbins := [];
        potential := [];

        for id in bin do
            G := SmallGroup(order, id);

            fp := TestOnClusterList(G, "OutId");

            pos := Position(fps, fp);

            if pos = fail then
                Add(fps, fp);
                Add(newsubbins, []);
                pos := Length(fps);
            fi;

            Add(newsubbins[pos], id);

            #Note if two or more groups of bin could not be ruled out
            if Size(fp) = 4 and Size(newsubbins[pos]) > 1 then Add(potential, pos); fi;
        od;

        if exact then
            for i in [1..Size(newsubbins)] do
                if Size(newsubbins[i]) = 1 then continue; fi;
                if i in potential then
                    Append(NewBins, SplitExactOutEqv(newsubbins[i], order));
                else
                    Add(NewBins, newsubbins[i]);
                fi;
            od;
        else
            if Size(potential) > 0  then
                #Warning that groups could not be ruled out.
                Print("The sets ", newsubbins{Set(potential)}, " are not necessarly equivalent, but could not be ruled out.\n");
            fi;
            Append(NewBins, Filtered(newsubbins, b -> Size(b) > 1));
        fi;
    od;

    return NewBins;
end);

#####################################################################################
##
##  Creates a list of records that can be exported into latex code
##
InstallGlobalFunction(TableOfGroupInvariants, function(Bins, order)
    local rows, ids, newrow, G, A, O, OutEqv;

    rows := [];

    for ids in SortedList(Bins) do

        newrow := rec(ids := ids);
        G := List(ids, id -> SmallGroup(order, id));

        #Check if all groups in the bin have same rank
        newrow.rank := DuplicateFreeList(List([1..Size(G)], i -> Rank(G[i])));
        if Length(newrow.rank) > 1 then Error("Not matching ranks"); fi;
        newrow.rank := newrow.rank[1];

        #Check if all groups in the bin have same p-class
        newrow.pclass := DuplicateFreeList(List([1..Size(G)], i -> Length(PCentralSeries(G[i]))-1));
        if Length(newrow.pclass) > 1 then Error("Not matching p-classes"); fi;
        newrow.pclass := newrow.pclass[1];

        A := List([1..Size(G)], i -> PcGroupAutPGroup(AutomorphismGroupPGroup(G[i])));

        #Check if all groups in the bin have equal sized automorphism groups
        newrow.SizeAut := DuplicateFreeList(List([1..Size(G)], i -> Size(A[i])));
        if Length(newrow.SizeAut) > 1 then Error("Not matching sizes of Aut"); fi;
        newrow.SizeAut := newrow.SizeAut[1];

        #Check groups of outer automorphisms
        OutEqv := List([1..Size(G)], i -> TestOnGroup(G[i], "OutId", rec(pack:=false)));

        if Length(DuplicateFreeList(OutEqv)) > 1 then
            #If groups yield different fingerprint, they are not equivalent
            newrow.OutEqv := "no";
        elif Length(OutEqv[1]) = 2 then
            #If they yield same fingerprint and that used IdGroup, they are equivalent
            newrow.OutEqv := "yes";
        else
            if Size(newrow.ids) = 2 then
                #If onyl check a pair of groups check them with anupq. That could take a while.
                O := List([1..Size(G)], i -> A[i]/InnerAutGroupPGroup(A[i]));
                if IsPqIsomorphicPGroup(O[1],O[2]) then
                    newrow.OutEqv := "yes";
                else
                    newrow.OutEqv := "no";
                fi;
            else
                newrow.OutEqv := fail;
            fi;
        fi;

        #Since isoclinism and mip take a while, exclude them here.
        newrow.isoclinic := "";
        newrow.mip := "";

        Add(rows, newrow);
    od;

    return rows;

end);



InstallGlobalFunction(MergeTablesOfInvariants, function(tab1, tab2)
    local tab, row, pos, new, name;

    tab := [];

    if Size(tab1) <> Size(tab2) then Error("Both provided tables must have the same length"); fi;

    for row in tab1 do
        pos := Position(List(tab2, t -> t.ids), row.ids);

        if pos = fail then
            Error(Position(tab1, row), "th row of tab1 has no correspondance in tab2");
        fi;

        new := rec(ids := [], rank := 0, pclass:=0, isoclinic:="", SizeAut:=0, OutEqv:="", MIP:="");

        #Check for all entries of new, if tab1 and tab2 are equal or one of them is on default
        for name in RecNames(new) do
            if \.(row, RNamObj(name)) = \.(tab2[pos], RNamObj(name)) then
                \.\:\=( new, RNamObj(name), \.(row, RNamObj(name)));
            elif \.(row, RNamObj(name)) in [[],0,""] then
                \.\:\=(new, RNamObj(name), \.(tab2[pos], RNamObj(name)));
            elif \.(tab2[pos], RNamObj(name)) in [[],0,""] then
                \.\:\=(new, RNamObj(name), \.(row, RNamObj(name)));
            else
                Error("I am not sure what happend");
            fi;
        od;

        Add(tab, new);
    od;

    return tab;
end);


InstallGlobalFunction(PrintTableToFile, function(rows, filename)
    local head, row, i;
    filename := Concatenation(filename, "_table.txt");
    head := "Pair & Rank & $p$-class& Isoclinic & Size of Aut & Out-equiv & MIP \\\\ \n";

    PrintTo(filename, head);

    for row in rows do

        AppendTo(filename, "(",row.ids[1]);
        for i in [2..Size(row.ids)] do AppendTo(filename, ", ", row.ids[i]); od;
        AppendTo(filename, ") & ");

        AppendTo(filename, row.rank, " & ",
                           row.pclass, " & ",
                           row.isoclinic, " & ",
                           row.SizeAut, " & ",
                           row.OutEqv, " & ",
                           row.mip,
                           " \\\\ \n");
    od;
end);
