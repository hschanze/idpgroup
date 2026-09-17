#
# Ident512: Implements an identification routine for the groups of order 512.
#
# This file runs package tests. It is also referenced in the package
# metadata in PackageInfo.g.
#
LoadPackage( "IdPGroup" );

TestDirectory(DirectoriesPackageLibrary( "IdPGroup", "tst" ),
  rec(exitGAP := true));

FORCE_QUIT_GAP(1); # if we ever get here, there was an error
