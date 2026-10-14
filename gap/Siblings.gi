####################
## Info Levels:
##
DeclareInfoClass("InfoSiblings");
SetInfoLevel(InfoSiblings, 0);


#####################################################################################
##
## Takes a list of bins with ids of groups of size order and performs test via
## TestOnGroup on them. Depending on the outcome a bin is split into smaller
##  bins according to the test.
##
SplitBinsViaTest := function(Bins, order, test)
    local NewBins, IdList, prog, bin, fps, newsubbins, id, G, M, i, fp, pos;

    NewBins := [];
    IdList := Flat(Bins);
    prog := 0;

    Info(InfoSiblings, 1, "Performing '", test, "' on ", Size(IdList), " groups");

    for bin in Bins do

        fps := [];
        newsubbins := [];

        for id in bin do

            if prog <> QuoInt(Position(IdList,id)*10,Size(IdList)) then
                prog := QuoInt(Position(IdList,id)*10,Size(IdList));
                Info(InfoSiblings, 1, "Progress: ", prog, "0%");
            fi;
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
end;


#####################################################################################
##
## Performs all necessary tests on all groups of size order to determine all sets of subgroup- and
## factor-equivalent (SFeq) groups.
##
InstallGlobalFunction(CalculateSiblings, function(order)
    local Bins,tests, test, NewBins;

    Bins := [[1..NumberSmallGroups(order)]];

    tests := ["MaxSubId", "SpSubId", "MaxFactId", "FactId", "SubId"];

    for test in tests do
        NewBins := SplitBinsViaTest(Bins, order, test);
        Bins := Filtered(NewBins, bin -> Size(bin) > 1);

        Info(InfoSiblings, 1, "Test '", test, "' created bins of following size greater one: ", Collected(List(Bins,Size)));

        if Size(Bins) = 0 then return Bins; fi;
    od;

    return Bins;
end);


#####################################################################################
##
##  Loads and returns a list of ids of subgroup- and factor-equivalent groups of
##  order size if available
##
InstallGlobalFunction(Siblings, function(args...)
    local ids, size, filename, ind;

    ids := [];
    size := args[1];
    if Size(args) = 1 then args[2] := false; fi;

    if size < 256 and not size in [60,120,128,160,168,180,189,192,240,243] then
        #Print("There are no siblings of order ", size, ".\n");
        ids := [];
    elif List(Collected(Factors(size)),x->x[2]) in [[1], [2], [3], [1,1]] then
        ids := [];
    elif size = 243 then
        ids := [[19, 20], [44, 45]];
    elif Size(Collected(Factors(size))) = 1 and Collected(Factors(size))[1][2] = 4 then
        ids := [[9, 10]];
    elif size in [128, 256, 512, 729] then
        filename := Concatenation("Siblings_", String(size),".g");
        filename := Concatenation("data/SiblingsData/",filename);
        Read(Filename(DirectoriesPackageLibrary("idpgroup",""), filename));

        if Length(args) = 2 then
            ind := [1..Length(BINS_OF_IDS)];
        elif Length(args) = 3 and IsList(args[3]) then
            ind := args[3];
            if not IsSubset([1..Length(BINS_OF_IDS)], ind) then
                Error("Please choose a subset of [1..", Length(BINS_OF_IDS),"] as the list of indicies");
            fi;
        else
            Error("SiblingsIds only expects at most 2 arguments");
        fi;

        ids := BINS_OF_IDS{ind};
    else
        Print("Siblings of size ", size, " are not documented yet.\n");
        return fail;
    fi;

    if args[2] then
        return ids;
    else
        return List(ids, id -> List(id, i -> SmallGroup(size, i)));
    fi;
end);


InstallGlobalFunction(CalculateStrongSiblings, function(order, arg...)
    local Bins, BPs, prog, bin, BP, CT, i, j, bp;

    if Length(arg) = 0 then
        Info(InfoSiblings, 1, "Start by calculating siblings of order ", order);
        Bins := CalculateSiblings(order);
    else
        Info(InfoSiblings, 1, "Use provided siblings ");
        Bins := arg[1];
    fi;

    Info(InfoSiblings, 1, "Find Brauer pairs among the found siblings ");

    BPs := [];
    prog := 0;

    for bin in Bins do
        if Size(bin) = 1 then continue; fi;

        BP := [[1]];
        CT := List(bin, id -> CharacterTable(SmallGroup(order, id)));

        for i in [2..Size(bin)] do
            if prog <> QuoInt(Position(Flat(Bins),bin[i])*10,Size(Flat(Bins))) then
                prog := QuoInt(Position(Flat(Bins),bin[i])*10,Size(Flat(Bins)));
                Info(InfoSiblings, 1, "Progress: ", prog, "0%");
            fi;
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


#####################################################################################
##
##  Loads and returns a list of ids of subgroup- and factor-equivalent Brauer
##  pairs of groups of order size if available.
##
InstallGlobalFunction(StrongSiblings, function(args...)
    local ids, size, filename, ind;

    ids := [];
    size := args[1];

    if Size(args) = 1 then args[2] := false; fi;

    if size in List([1..7],i->2^i) then
        ids := [];
    elif size in [256, 512] then
        filename := Concatenation("StrongSiblings_", String(size),".g");
        filename := Concatenation("data/SiblingsData/",filename);
        Read(Filename(DirectoriesPackageLibrary("idpgroup",""), filename));

        if Length(args) = 2 then
            ind := [1..Length(BINS_OF_IDS)];
        elif Length(args) = 3 and IsList(args[3]) then
            ind := args[3];
            if not IsSubset([1..Length(BINS_OF_IDS)], ind) then
                Error("Please choose a subset of [1..", Length(BINS_OF_IDS),"] as the list of indicies");
            fi;
        else
            Error("StrongSiblingsIds only expects at most 2 arguments");
        fi;

        ids := BINS_OF_IDS{ind};
    else
        Print("Strong siblings of size ", size, " are not documented yet.\n");
        return fail;
    fi;

    if args[2] then
        return ids;
    else
        return List(ids, id -> List(id, i -> SmallGroup(size, i)));
    fi;
end);


#####################################################################################
##
##  Splits list of ids of groups of size order in Bin, if their outer automorphism groups
##  are isomorphic, via IsPqIsomorphicPGroup from the anupq package
SplitExactOutEqv := function(Bin, order)
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
end;

#####################################################################################
##
## Takes a list of bins with ids of groups of size order and evaluates which are outer-
## automorphism equivalent. If exact = true, sets of groups which could not be ruled out to
## be equivalent are testet via SplitExactOutEqv. Otherwise, these are simply included.
##
BinsOfOutEqGroups := function(Bins, order, exact)
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
end;


#####################################################################################
##
##  Creates a list of records that can be exported into latex code
##
TableOfGroupInvariants := function(Bins, order)
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
end;


MergeTablesOfInvariants := function(tab1, tab2)
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
end;


PrintTableToFile := function(rows, filename)
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
end;
