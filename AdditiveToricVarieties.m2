newPackage(
        "AdditiveToricVarieties",
        AuxiliaryFiles => true,
        Version => "1.0", 
        Date => "20 October 2025",
        Authors => {
            {Name => "Fabián Levicán", 
            Email => "fabian.levican@univie.ac.at"},
            {Name => "Pedro Montero", 
            Email => "pedro.montero@usm.cl"}
            },
        Headline => "methods for additive actions on complete toric varieties",
	Keywords => {"Additive Actions", "Toric Varieties", "Algebraic Geometry"},
        PackageImports => {"NormalToricVarieties", "Polyhedra"},
        PackageExports => {"NormalToricVarieties", "Polyhedra"}
        )

export {
    "demazureRoots",
    "additiveActions",
    "listAdditiveSmoothFanoToricVarieties",
    "listUniquelyAdditiveSmoothFanoToricVarieties",
    "getCompleteCollection",
    "checkIfUniquelyAdditive",
    "fanIsComplete",
    "fanIsSmooth"
    }

classifier := new List from [];
classifier = append(classifier, {{0, true, {{-1}}, true}});
for n from 2 to 6 do(
    fileName := concatenate {currentFileDirectory, "AdditiveToricVarieties/classifier-", toString n, ".csv"};
    fileLines := lines get fileName;
    classifier = append(classifier, apply(fileLines, value));
);

isP1timesP1 = method();

isP1timesP1 List := fanRays -> (
    ray := fanRays#0;
    return member((-1)*ray, fanRays) and (abs det matrix {delete((-1)*ray, delete(ray, fanRays))#0, ray}) == 1;
);

demazureRoots = method();

demazureRoots(List, List) := (fanRays, ray) -> (
    if #ray == 1 then return {{-1}};
    ray = (1/(gcd ray))*ray;
    fanRays = apply(fanRays, r -> (1/(gcd r))*r);
    if not member(ray, fanRays) then error "expected a lattice vector generating a ray of the fan";
    otherFanRays := matrix delete(ray, fanRays);
    P := polyhedronFromHData((-1)*(otherFanRays), 0*otherFanRays_{0}, matrix {ray}, matrix {{-1}});
    if isEmpty P then return {};
    if not isCompact P then error "expected a bounded polyhedron -- a possible cause is that the fan is not complete";
    latticePointsP := latticePoints P;
    return apply(latticePointsP, x -> if x == 0 then {0} else flatten entries transpose x);
);

demazureRoots(Fan, List) := (F, ray) -> demazureRoots(entries transpose rays F, ray);

demazureRoots List := fanRays -> (
    demazureRootsHashTable := new MutableHashTable;
    apply(fanRays, r -> demazureRootsHashTable#r = demazureRoots(fanRays, r));
    return demazureRootsHashTable;
);

demazureRoots Fan := F -> demazureRoots entries transpose rays F;

additiveActions = method(Options => {
    getCompleteCollection => true,
    checkIfUniquelyAdditive => true,
    fanIsComplete => null,
    fanIsSmooth => null
});

additiveActions Fan := o -> F -> (
    fanIsComplete := o.fanIsComplete;
    if fanIsComplete === null then (
        fanIsComplete = isComplete F;
    );
    if not fanIsComplete then error "expected a complete fan";
    fanIsSmooth := o.fanIsSmooth;
    if fanIsSmooth === null then (
        fanIsSmooth = isSmooth F;
    );

    isAdditiveValue := false;
    completeCollectionValue := {};
    isUniquelyAdditiveValue := false;

    n := dim F;
    if n == 1 then return new HashTable from {
        "isAdditive" => true,
        "completeCollection" => {{-1}},
        "isUniquelyAdditive" => true
    };
    fanRays := entries transpose rays F;
    fanRays = apply(fanRays, r -> (1/(gcd r))*r);
    nFanRays := #fanRays;
    if not o.getCompleteCollection then (
        pic := nFanRays - n;
        if fanIsSmooth and pic == 2 then (
            if o.checkIfUniquelyAdditive then (
                isUniquelyAdditiveValue = false;
                if n == 2 and nFanRays == 4 and (isP1timesP1 fanRays) then (
                    isUniquelyAdditiveValue = true;
                );
            );
            return new HashTable from {
                "isAdditive" => true,
                "completeCollection" => completeCollectionValue,
                "isUniquelyAdditive" => isUniquelyAdditiveValue
            };
        );
    );
    fanMaxCones := maxCones F;
    fanRaySubsets := apply(fanMaxCones, c -> apply(c, i -> fanRays#i));
    if o.checkIfUniquelyAdditive then isUniquelyAdditiveValue = false;
    for i from 0 to #fanRaySubsets - 1 do (
        s := fanRaySubsets#i;
        nS := #s;
        matrixS := matrix s;
        flag := true;
        if fanIsSmooth or nS == n and (abs det matrixS) == 1 then (
            for j from 0 to nFanRays - 1 do (
                r := fanRays#j;
                if not member(r, s) then (
                    matrixR := transpose matrix {r};
                    coeffs := (inverse transpose matrixS) * matrixR;
                    for k from 0 to n - 1 do (
                        p := coeffs_(k, 0);
                        if p > 0 then (
                            flag = false;
                            break;
                        );
                    );
                    if not flag then break;
                );
            );
            if not flag then continue;
        ) else continue;
        isAdditiveValue = true;
        if o.getCompleteCollection then (
            completeCollectionValue = entries ((-1)*(inverse transpose matrixS));
        );
        if o.checkIfUniquelyAdditive then (
            isUniquelyAdditiveValue = true;
            for j from 0 to nS - 1 do (
                r := s#j;
                if #demazureRoots(fanRays, r) > 1 then (
                    isUniquelyAdditiveValue = false;
                    break;
                );
            ); 
        );
        break;
    );

    return new HashTable from {
        "isAdditive" => isAdditiveValue,
        "completeCollection" => completeCollectionValue,
        "isUniquelyAdditive" => isUniquelyAdditiveValue
    };
);

additiveActions NormalToricVariety := o -> X -> additiveActions(fan X,
    getCompleteCollection => o.getCompleteCollection,
    checkIfUniquelyAdditive => o.checkIfUniquelyAdditive,
    fanIsComplete => o.fanIsComplete,
    fanIsSmooth => o.fanIsSmooth
);

additiveActions Polyhedron := o -> P -> (
    if not (isLatticePolytope P) then error "expected a lattice polytope";
    if not (isFullDimensional P) then error "expected a full-dimensional polytope";
    return additiveActions(normalFan P,
        getCompleteCollection => o.getCompleteCollection,
        checkIfUniquelyAdditive => o.checkIfUniquelyAdditive,
        fanIsComplete => true,
        fanIsSmooth => o.fanIsSmooth
    );
);

additiveActions(ZZ, ZZ) := o -> (n, i) -> (
    if (n <= 0 or n >= 7) then error "expected n = 1, ..., 6";
    if (n == 1 and i != 0) then error "expected i == 0";
    if (n == 2 and (i <= -1 or i >= 5)) then error "expected i = 0, ..., 4";
    if (n == 3 and (i <= -1 or i >= 18)) then error "expected i = 0, ..., 17";
    if (n == 4 and (i <= -1 or i >= 124)) then error "expected i = 0, ..., 123";
    if (n == 5 and (i <= -1 or i >= 866)) then error "expected i = 0, ..., 865";
    if (n == 6 and (i <= -1 or i >= 7622)) then error "expected i = 0, ..., 7622";
    return new HashTable from {
        "isAdditive" => classifier#(n - 1)#i#1,
        "completeCollection" => classifier#(n - 1)#i#2,
        "isUniquelyAdditive" => classifier#(n - 1)#i#3,
    };
);

listAdditiveSmoothFanoToricVarieties = method();

listAdditiveSmoothFanoToricVarieties ZZ := n -> (
    if (n <= 0 or n >= 7) then error "expected n = 1, ..., 6";
    return for x in classifier#(n - 1) list (
        if not x#1 then continue;
        new HashTable from {
            "databaseIndex" => x#0,
            "completeCollection" => x#2,
            "isUniquelyAdditive" => x#3
        }
    );
);

listUniquelyAdditiveSmoothFanoToricVarieties = method();

listUniquelyAdditiveSmoothFanoToricVarieties ZZ := n -> (
    if (n <= 0 or n >= 7) then error "expected n = 1, ..., 6";
    return for x in classifier#(n - 1) list (
        if not x#3 then continue;
        new HashTable from {
            "databaseIndex" => x#0,
            "completeCollection" => x#2
        }
    );
);

beginDocumentation();

doc ///
  Key
    AdditiveToricVarieties
  Headline
    Methods for additive actions on complete toric varieties
  Description
   Text
     {\bf Overview:}

     {\it AdditiveToricVarieties} is a package with various methods for working with additive actions
     on complete toric varieties. For more details and applications, see [1].

     Let $X$ be an irreducible algebraic variety over an algebraically closed field $K$. An additive action on $X$ is
     an effective regular action of the commutative unipotent group $G_a^n(K)$ on $X$ with a dense open orbit.
     $X$ is {\it additive} if it admits an additive action and {\it uniquely additive} if any such action is isomorphic to
     the normalized one.

     You can use this package to check if a given complete toric variety admits an additive action. This is done by
     using the results described in [1], [2] and [3]. The input can be a @TO Fan@, a @TO NormalToricVariety@,
     a @TO Polyhedron@ or the database index of a @TO smoothFanoToricVariety@. 

     You can also use this package to get the Demazure roots of a @TO Fan@, to get complete collections of
     Demazure roots, to check if a given complete toric variety is uniquely additive, to get a list of all
     additive smooth Fano toric varieties of a given dimension and to get a list of all uniquely additive smooth Fano
     toric varieties of a given dimension.
     
     Several optimizations have been implemented, see [1]. In particular, the database in @TO smoothFanoToricVariety@
     has been pre-processed and included in the package. There are 4 additive smooth Fano toric surfaces, 14 threefolds,
     79 fourfolds, 470 fivefolds and 3428 sixfolds. Of these, 2, 2, 4, 4 and 8, respectively, are uniquely additive. 
    
     {\bf References:}

     [1]: Levicán, F. and Montero, P. (2025). AdditiveToricVarieties -- A Macaulay2 package for working with additive complete toric varieties. arXiv.

     [2]: Arzhantsev, I. and Romaskevich, E. (2017). Additive actions on toric varieties. Proc. Amer. Math. Soc., 145(5):1865-1879.
     
     [3]: Dzhunusov, S. (2022). On uniqueness of additive actions on complete toric varieties. Journal of Algebra, 609:642-656.
///

doc ///
  Key
    demazureRoots
    (demazureRoots, List, List)
    (demazureRoots, Fan, List)
    (demazureRoots, List)
    (demazureRoots, Fan)
  Headline
    get the Demazure roots of a complete fan
  Usage
    demazureRoots(fanRays, ray)
    demazureRoots(F, ray)
    demazureRoots(fanRays)
    demazureRoots(F)
  Inputs
    fanRays:List
        the generating rays of the fan
    ray:List
        a generating ray of the fan
    F:Fan
        a complete fan
  Outputs
    :List
        if the input {\tt ray} is given, a list containing the Demazure roots corresponding to {\tt ray}
    :HashTable
        if the input {\tt ray} is not given, a hash table with keys the generating rays of the fan and values the corresponding Demazure roots
  Description
   Text
     Gets the Demazure roots of a complete fan.

     The projective plane has six Demazure roots:
   Example
     F = fan toricProjectiveSpace 2;
     demazureRootsF = demazureRoots F;
     flatten values demazureRootsF
   Text
     There are two roots corresponding to {\tt e1}:
   Example
     e1 = {1, 0};
     demazureRootsF#e1
   Text
     Alternatively, this can also be computed directly:
   Example
     demazureRoots(F, e1)
///

doc ///
  Key
    additiveActions
    (additiveActions, Fan)
    (additiveActions, NormalToricVariety)
    (additiveActions, Polyhedron)
    (additiveActions, ZZ, ZZ)
  Headline
    check if a complete toric variety admits an additive action
  Usage
    additiveActions(F)
    additiveActions(X)
    additiveActions(P)
    additiveActions(n, i)
  Inputs
    F:Fan
        a complete fan
    X:NormalToricVariety
        a complete toric variety
    P:Polyhedron
        a full-dimensional lattice polytope
    n:ZZ
        the dimension ({\tt n} = 1, ..., 6)
    i:ZZ
        the database index of a smooth Fano toric variety in @TO smoothFanoToricVariety@
    getCompleteCollection => Boolean
        {\tt true} if the output must include a complete collection of Demazure roots, {\tt false} if not
    checkIfUniquelyAdditive => Boolean
        {\tt true} if the output must include whether the variety is uniquely additive, {\tt false} if not
    fanIsComplete => Boolean
        {\tt true} if the fan is known to be complete, {\tt false} if the fan is known not to be complete
    fanIsSmooth => Boolean
        {\tt true} if the fan is known to be smooth, {\tt false} if the fan is known not to be smooth
  Outputs
    :HashTable
        a hash table with keys {\tt "isAdditive"}, {\tt "completeCollection"} and {\tt "isUniquelyAdditive"}
  Description
   Text
     Checks if a complete toric variety admits an additive action. If the input is {\tt (n, i)}, the method fetches
     the output from a pre-processed database.

     Setting {\tt getCompleteCollection} or {\tt checkIfUniquelyAdditive} to {\tt false},
     or {\tt fanIsComplete} or {\tt fanIsSmooth} to {\tt true}, may dramatically increase performance, especially if the
     variety is high-dimensional.

     The output is a hash table with the following keys and values:

     {\tt "isAdditive"}: {\tt true} if the variety is additive, {\tt false} if not

     {\tt "completeCollection"}: a list containing a complete collection of Demazure roots if the variety is additive and {\tt getCompleteCollection} is {\tt true}

     {\tt "isUniquelyAdditive"}: {\tt true} if the variety is uniquely additive and {\tt checkIfUniquelyAdditive} is {\tt true}, {\tt false} if not
     
     The projective plane is additive but not uniquely additive:
   Example
     PP2 = toricProjectiveSpace 2;
     additiveActions PP2
   Text
     The projective variety corresponding to the Del Pezzo polygon does not admit an additive action:
   Example
     V = transpose matrix {{1, 0}, {0, 1}, {-1, 0}, {0, -1}, {1, 1}, {-1, -1}};
     P = convexHull V;
     additiveActions P
///

doc ///
  Key
    listAdditiveSmoothFanoToricVarieties
    (listAdditiveSmoothFanoToricVarieties,ZZ)
  Headline
    generate a list of all additive smooth Fano toric varieties of a given dimension
  Usage
    listAdditiveSmoothFanoToricVarieties(n)
  Inputs
    n:ZZ
        the dimension ({\tt n} = 1, ..., 6)
  Outputs
    :List
        a list containing hash tables with keys {\tt "databaseIndex"} (the database index in @TO smoothFanoToricVariety@), {\tt "isAdditive"} and {\tt "completeCollection"}
  Description
   Text
     Generates a list of all additive smooth Fano toric varieties of a given dimension. The method fetches the output
     from a pre-processed database.

     The following is the two-dimensional case:
   Example
     listAdditiveSmoothFanoToricVarieties 2
   Text
     The smooth Fano toric surface with database index 4 is not additive:
   Example
     additiveActions(2, 4)
   Text
     There are 470 additive Smooth fano toric fivefolds:
   Example
     #(listAdditiveSmoothFanoToricVarieties 5)
///

doc ///
  Key
    listUniquelyAdditiveSmoothFanoToricVarieties
    (listUniquelyAdditiveSmoothFanoToricVarieties,ZZ)
  Headline
    generate a list of all uniquely additive smooth Fano toric varieties of a given dimension
  Usage
    listUniquelyAdditiveSmoothFanoToricVarieties(n)
  Inputs
    n:ZZ
        the dimension ({\tt n} = 1, ..., 6)
  Outputs
    :List
        a list containing hash tables with keys {\tt "databaseIndex"} (the database index in @TO smoothFanoToricVariety@) and {\tt "completeCollection"}
  Description
   Text
     Generates a list of all additive smooth Fano toric varieties of a given dimension. The method fetches the output
     from a pre-processed database.

     The following is the two-dimensional case:
   Example
     listUniquelyAdditiveSmoothFanoToricVarieties 2
   Text
     There are 4 uniquely additive smooth Fano toric fivefolds:
   Example
     #(listUniquelyAdditiveSmoothFanoToricVarieties 5)
///

TEST ///
fanRays = {{1, 0}, {0, 1}, {-1, 0}, {0, -1}};
assert(#(demazureRoots fanRays) == 4);
///

TEST ///
fanRays = {{1, 0}, {0, 1}, {-1, 0}, {0, -1}};
e1 = {1, 0};
assert(demazureRoots(fanRays, e1) == {{-1, 0}});
///

TEST ///
count = 0;
for i from 0 to 4 do(
    if (additiveActions(smoothFanoToricVariety(2, i), getCompleteCollection => false, checkIfUniquelyAdditive => false, fanIsComplete => true, fanIsSmooth => true))#"isAdditive" then(
        count = count + 1;
    );
);
assert(count == 4);
///

TEST ///
count = 0;
for i from 0 to 17 do(
    if (additiveActions(smoothFanoToricVariety(3, i), getCompleteCollection => false, checkIfUniquelyAdditive => false, fanIsComplete => true, fanIsSmooth => true))#"isAdditive" then(
        count = count + 1;
    );
);
assert(count == 14);
///

TEST ///
count = 0;
for i from 0 to 4 do(
    if (additiveActions(2, i))#"isAdditive" then(
        count = count + 1;
    );
);
assert(count == 4);
///

TEST ///
count = 0;
for i from 0 to 17 do(
    if (additiveActions(3, i))#"isAdditive" then(
        count = count + 1;
    );
);
assert(count == 14);
///

TEST ///
count = 0;
for i from 0 to 123 do(
    if (additiveActions(4, i))#"isAdditive" then(
        count = count + 1;
    );
);
assert(count == 79);
///

TEST ///
count = 0;
for i from 0 to 865 do(
    if (additiveActions(5, i))#"isAdditive" then(
        count = count + 1;
    );
);
assert(count == 470);
///

TEST ///
assert(#(listAdditiveSmoothFanoToricVarieties 1) == 1);
assert(#(listAdditiveSmoothFanoToricVarieties 2) == 4);
assert(#(listAdditiveSmoothFanoToricVarieties 3) == 14);
assert(#(listAdditiveSmoothFanoToricVarieties 4) == 79);
assert(#(listAdditiveSmoothFanoToricVarieties 5) == 470);
assert(#(listAdditiveSmoothFanoToricVarieties 6) == 3428);
///

TEST ///
assert(#(listUniquelyAdditiveSmoothFanoToricVarieties 1) == 1);
assert(#(listUniquelyAdditiveSmoothFanoToricVarieties 2) == 2);
assert(#(listUniquelyAdditiveSmoothFanoToricVarieties 3) == 2);
assert(#(listUniquelyAdditiveSmoothFanoToricVarieties 4) == 4);
assert(#(listUniquelyAdditiveSmoothFanoToricVarieties 5) == 4);
assert(#(listUniquelyAdditiveSmoothFanoToricVarieties 6) == 8);
///


end
