# The GAP package IdPGroup

This package implements an identification routine for the groups of order 512 (=2^9). The identified groups are characterised by the id of the isomorphic group of the SmallGroups Libray. Furthermore this package includes data and code to calculate so called (strong) siblings complementing the paper ["The group identification problem for p-groups of small order"](https://gcc.episciences.org/18584/pdf).

## Installation

Unpack `IdPGroup.tar.gz` in the `pkg`subdirectory of the GAP root directory.
From with in GAP load the package with

```gap
gap>LoadPackage("idpgroup").
```

**Some functions of this package rely on the SmallGroups Library and the Anupq-Package. Thus having these installed is mandatory.**

## Example

```gap
gap> ### get random group
gap> id := Random(1, NumberSmallGroups(512));
746776
gap> G := SmallGroup(512, id);;
gap> H:=Subgroup(G,SmallGeneratingSet(G));;
gap> ### determine id
gap> IdSmallGroup(5);
[ 512, 746776 ]
```

## Tests

```gap
gap> TestPackage("idp5");
```

runs the test suite in `tst/` (about one and a half minute)

## Contact

The IdPGroup Package has been developed by

Henrik Schanze<br/>
Institut fuer Analysis und Algebra<br/>
Technische Universitaet Braunschweig<br/>
Universitaetsplatz 2<br/>
38106 Braunschweig<br/>
Germany<br/>

E-mail: henrik.schanze@tu-bs.de<br/>
Homepage: https://www.iaa.tu-bs.de/henschan

## License

The idpgroup package is licensed under the GNU General Public License v2.0 or later. A copy of this license is included.
