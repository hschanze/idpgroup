#
# IdPGroup: Implements identification functions for different $p$-groups.
#
# This file is a script which compiles the package manual.
#
if fail = LoadPackage("AutoDoc", "2018.02.14") then
    Error("AutoDoc version 2018.02.14 or newer is required.");
fi;


AutoDoc( rec( scaffold := true, autodoc := true ) );


AutoDoc( rec(
    gapdoc := rec(
        LaTeXOptions := rec( EarlyExtraPreamble := """
            \usepackage{a4wide}
            \newcommand{\bbZ}{\mathbb{Z}}
        """ )
    ),
    scaffold := rec(
        includes := [ "_AutoDocMainFile.xml"],
        entities := rec(SmallGrps := "<Package>SmallGrps</Package>",
                        Anupq := "<Package>Anupq</Package>",
                        ModIsom := "<Package>ModIsom</Package>",
                        XMod := "<Package>XMod</Package>")
    )
));
