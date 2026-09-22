#
# IdPGroup: Implements identification functions for different $p$-groups.
#
# Implementations
#


#####################################################################################
##
## returns an integer that encodes the content of the provided list
##
IdPGroup_Pack := function(list)
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
end;


#####################################################################################
##
##  Computes all conjugacyclasses of the group G. All classes of the same length and
##  the same order of its elements are then saved in a list. All these list are then
##  stored in an additional list and returned.
##
ClusterConjClasses := function(G)
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
end;


#####################################################################################
##
## Returns the cycle-structure of the permutation on the elements of coc induced by
## the powermap x->x^n. First we determine the permutation within a cluster. Classes
## of a cluster that are fixed are examined afterwards on their own.
##
PowerMapCocCycSt := function(coc, n)
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
end;


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
##  De- or encodes the description desc for EvalFPCoc, depending if youe provide
##  an integer (decodes to list) or a list of integers (encodes to int)
##
DeEncodeDesc := function(desc)
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
end;

#####################################################################################
##
##  Alters coc according the result fp from EvalFPCoc evaluated with desc.
##
AlterCocAccordingToFp := function(coc, desc, fp)
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
end;


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
InstallGlobalFunction(IdGroup512, function(G, opt...)
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

    SetIdGroup(G, [512, branch]);

    if IsBool(opt.path) then
        return branch;
    else
        return [branch, opt.path];
    fi;
end);


InstallMethod( IdSmallGroup,
    "for groups of order 512, via IdGroup512",
    [ IsGroup and IsFinite ],
    SUM_FLAGS,
        function(G)
        local n;
        n := Size( G );
        if n <> 512 then
            TryNextMethod();
        else
            return [512, IdGroup512(G)];
        fi;
end );


InstallGlobalFunction(IdGroup512Exceptions, function()
    Read(Filename(DirectoriesPackageLibrary("idpgroup",""),"data/Id512Exceptions.g"));
    return BINS_OF_IDS;
end);
