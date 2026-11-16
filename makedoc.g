#
# IdPGroup: Implements identification functions for different $p$-groups.
#
# This file is a script which compiles the package manual.
#
if fail = LoadPackage("AutoDoc", "2018.02.14") then
    Error("AutoDoc version 2018.02.14 or newer is required.");
fi;


AutoDoc(rec(
        autodoc := true,
        scaffold := rec(
            MainPage := true,
            bib := "bib.xml",
            entities := rec(SmallGrps := "<Package>SmallGrp</Package>",
                            Anupq := "<Package>Anupq</Package>",
                            ModIsom := "<Package>ModIsom</Package>",
                            XMod := "<Package>XMod</Package>")
        )
    )
);
