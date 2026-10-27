#
# Ident512: Implements identification functions for the groups for different $p$-groups.
#
# This file contains package meta data. For additional information on
# the meaning and correct usage of these fields, please consult the
# manual of the "Example" package as well as the comments in its
# PackageInfo.g file.
#
SetPackageInfo( rec(

PackageName := "IdPGroup",
Subtitle := "Identification functions for different p-groups",
Version := "1.0",
Date := "11/08/2026", # dd/mm/yyyy format
License := "GPL-2.0-or-later",

Persons := [
  rec(
    FirstNames := "Henrik",
    LastName := "Schanze",
    WWWHome := "https://www.iaa.tu-bs.de/henschan",
    Email := "henrik.schanze@tu-braunschweig.de",
    IsAuthor := true,
    IsMaintainer := true,
    PostalAddress := "Universitaetsplatz 2",
    Place := "Braunschweig, Germany",
    Institution := "TU Braunschweig",
  ),
],

SourceRepository := rec( Type := "git", URL := "https://github.com/hschanze/idpgroup" ),
IssueTrackerURL := Concatenation( ~.SourceRepository.URL, "/issues" ),
PackageWWWHome := "https://github.com/hschanze/idpgroup",
PackageInfoURL := Concatenation( ~.PackageWWWHome, "PackageInfo.g" ),
README_URL     := Concatenation( ~.PackageWWWHome, "README.md" ),
ArchiveURL     := Concatenation( ~.PackageWWWHome,
                                 "/", ~.PackageName, "-", ~.Version ),

ArchiveFormats := ".tar.gz",

AbstractHTML   :=  "",

PackageDoc := rec(
  BookName  := "IdPGroup",
  ArchiveURLSubset := ["doc"],
  HTMLStart := "doc/chap0_mj.html",
  PDFFile   := "doc/manual.pdf",
  SixFile   := "doc/manual.six",
  LongTitle := "Identification functions for different p-groups",
),

Dependencies := rec(
  GAP := ">= 4.13",
  NeededOtherPackages := [["smallgrp","1.5.3"],["anupq", "3.3.1"]],
  SuggestedOtherPackages := [],#[["modisom","2.5.4"], ["xmod", "2.92"]],
  ExternalConditions := [ ],
),

Extensions := [
  rec(
    needed := [["modisom","2.5.4"], ["xmod", "2.92"]],
    filename := "gap/ModIsomIsoclinExt.gi",
  )
],

AvailabilityTest := ReturnTrue,

TestFile := "tst/testall.g",

#Keywords := [ "TODO" ],

));


