InstallGlobalFunction(DetermineMIPInTable, function(rows, prime, power)
    local row, tt;
    for row in rows do
        if Size(row.ids) = 1 then continue; fi;
        tt := MIPSplitGroupsByAlgebras(prime, power, row.ids);
        if Length(tt.bins) = 0 then
            row.mip := "no";
        else
            row.mip := "yes";
        fi;
        AppendTo("MIP_temp.txt", tt, "\n");
    od;
    PrintTo("MIP_rows.txt", rows);
    return rows;
end);


InstallGlobalFunction(DetermineIsoclinicInTable, function(rows, order, exclude)
    local row, pos, G, isocl;

    for row in rows do
        if Size(row.ids) = 1 then continue; fi;

        pos := Position(List(exclude, l -> l[1]), row.ids);
        if pos <> fail then
            row.isoclinic := exclude[pos][2];
            continue;
        fi;

        G := List(row.ids, id -> SmallGroup(order, id));

        isocl := Isoclinism(G[1], G[2]);

        if isocl = fail then
            row.isoclinic := "no";
        else
            row.isoclinic := "yes";
        fi;

        AppendTo("IP_temp.txt", [row.ids, isocl]);
    od;

    PrintTo("Ip_rows.txt", rows, ";");

    return rows;
end);
