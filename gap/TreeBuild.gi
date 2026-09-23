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
FindParametersForCocTest := function(Coc, paralist, it, maxit, opt...)
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
end;


#####################################################################################
##
##  Build a 1-level serachtree to distinguish the groups of order 512 with id
##  in Ids based on there behavior under EvalFpCoc. Past tests with EvalFpCoc
##  which altered the clusters of conjugacyclasses can be recreated via the
##  list desc. The function returns a record made of fp, next and desc.
##
CocSplitRoutine := function(Ids, order, desclist, iterate)
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
end;


#####################################################################################
##
##  Tries to split the clusters of clusters in the list CL via CocSplitRoutine.
##  CL needs to be a cluster list produced by ClusterList. The output is a list of
##  pairs containg the path of a cluster and the subbrunch resulting from the test.
##  This function accepts a record opt of options with the following content
##  - pack: a boolean that is handed to TestOnGroup
##  - order: an integer giving the order of the groups with ids in CL
##  - iterate: an integer determining how many iterations the parameter search should ##    do in the worst case.
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
