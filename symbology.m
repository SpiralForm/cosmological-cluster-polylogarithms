(* ::Package:: *)

(* symbology.m -- generic MPL and symbol operations.  (Renamed from cosmo.m, 2026-07-28.)

   This file holds ONLY kinematics-independent machinery:
     * G <-> Li converters (GToLi, LiToG, LiToPolyLog, GShuffleRegulate, gRegG,
       gToLiOne, gLonghand, gShorthand, gTailZeros)
     * function-level products (GShuffleProduct/GShuffleRelation and
       LiStuffleProduct/LiStuffleRelation) and terminal-one stuffle
       regularization (Li1reg)
     * depth-raising Li replacement rule (to1moredepthli)
     * I <-> G converters (GToIH, IHToG, GToMPLG)
     * twist operations (TwistedIHsingle, Twisted, TwistedCloseIH, TwistedCloseIHsingle)
     * the symbol grammar in the NumPolyLog.m convention (the symbol is
       Tensor[l1,...,ln]; reduce a result with ToSymbol): Tensor, ExpandTensor,
       CiTi, ShuffleCiTi, CiTiShuffle, shuf2, shufWords, ShuffleProduct, ProductProjector,
       shuffleexpand
     * PSLQCoeff

   Kinematics-specific material is kept in separate domain packages.

   Li ORDERING: the increasing convention; see the boxed note
   at LiToG.  NumPolyLog.m's numLi uses the opposite order -- that is the one remaining
   inconsistency in the package set, and it is deliberate (NumPolyLog.m is never edited).

   Load after NumPolyLog.m:  Get["symbology.m"]
   Load NumPolyLog.m and any domain-specific prerequisites before this file. *)

(* ===================== section 0: basic functions ===================== *)

(* 0. basic functions: *)

(* ansatz for functions: *)
TwistedIHsingle[functionIH_, ktwist_Integer] := functionIH /. IH[list__] :> Block[{len = Length[{list}], weights}, weights = Flatten[Permutations /@ (IntegerPartitions[ktwist + len, {len}] - 1), 1]; Total[((Times @@ #1 & )[Reverse[Join[{0}, Range[0, len - 2]] /. 0 -> eps]^#1 /. eps -> 0]*IH @@ Flatten[(Table @@ #1 & ) /@ Transpose[{{list}, #1 + 1}]] & ) /@ weights]];
GToIH[function_] := function /.
  G[word_List, endpoint_] :> IH[0, Sequence @@ Reverse[word], endpoint];
IHToG[function_] := function /. IH[list__] :> Block[{mid = Delete[{list}, {{1}, {-1}}], last = Last[{list}], first = First[{list}]}, G[Reverse[mid - first], last - first]];
GToMPLG[function_] := function /. G[seq_List, var_] :> MPLG[seq, var];

(* ---------- G <-> Li : multiple polylogarithms in the classical notation ----------
   Self-contained (no PolyLogTools); uses the same list-form G[{a1,...,an}, y] as
   IHToG/GToMPLG above, and the same Li convention as NumPolyLog's numLi, so
   numLi[m, x] is the numerical value of Li[m, x].

     Li[{m1,...,mk}, {x1,...,xk}]
        = Sum_{n1>n2>...>nk>=1} x1^n1 ... xk^nk / (n1^m1 ... nk^mk)      (inert head)

   dictionary (a_j = the j-th non-zero letter, preceded by m_j - 1 zeros):
     G[{0^(m1-1), a1, ..., 0^(mk-1), ak}, y]
        = (-1)^k Li[{m1,...,mk}, {y/a1, a1/a2, ..., a(k-1)/ak}]
     Li[{m1,...,mk}, {x1,...,xk}]
        = (-1)^k G[{0^(m1-1), x2 x3...xk, ..., 0^(mk-1), 1}, x1 x2...xk]
   with G[{0^n}, y] = Log[y]^n/n!, and
   G[{a1,...,an}, y] = G[{a1/y,...,an/y}, 1] in the scaling gauge.  *)

gTailZeros[z_List] := LengthWhile[Reverse[z], PossibleZeroQ];
gShorthand[z_List] := With[{p = Flatten[Position[z, e_ /; ! PossibleZeroQ[e], {1}, Heads -> False]]},
  {Differences[Prepend[p, 0]], z[[p]]}];
gLonghand[m_List, w_List] := With[{av = Accumulate[m]},
  Normal@SparseArray[Thread[av -> w], Last[av]]];

(* shuffle-regularize trailing zeros: G[{...,0},y] -> Log[y]'s times convergent G's *)
gRegG[z_List, y_] := gRegG[z, y] = Which[
   z === {}, 1,
   ! PossibleZeroQ[Last[z]], G[z, y],
   True, Expand@With[{kk = gTailZeros[z], len = Length[z]},
     1/kk (If[y === 1, 0, Log[y] gRegG[Most[z], y]] -
        Total@Array[gRegG[Join[z[[1 ;; #1 - 1]], {0}, z[[#1 ;; len - kk - 1]],
             {z[[len - kk]]}, ConstantArray[0, kk - 1]], y] &, len - kk])]];
GShuffleRegulate[function_] := function /. G[z_List, y_] :> gRegG[z, y];

gToLiOne[z_List, y_] := Which[
   z === {}, 1,
   AllTrue[z, PossibleZeroQ], Log[y]^Length[z]/Length[z]!,
   True, With[{ma = gShorthand[z]},
     With[{m = First[ma], a = Last[ma]},
      (-1)^Length[m] Li[Reverse[m],
        Reverse[Prepend[Table[a[[j - 1]]/a[[j]], {j, 2, Length[a]}], y/a[[1]]]]]]]];

GToLi[function_] := GShuffleRegulate[function] /.
   {G[z_List, y_] :> gToLiOne[z, y], MPLG[z_List, y_] :> gToLiOne[z, y]};

(* ---------------------------------------------------------------------------
   Li ORDERING CONVENTION  (changed 2026-07-28).

   GToLi / LiToG use the INCREASING nesting convention, i.e. the same one as
   PolyLogTools and the project's analytic MPL expressions:

       Li[{m1,...,mk},{z1,...,zk}]  =  sum over  0 < n1 < n2 < ... < nk
                                         of  z1^n1 ... zk^nk / (n1^m1 ... nk^mk)

   equivalently PolyLogTools 1904.07279 eq. (3.6),
       G(0^{m1-1},a1,...,0^{mk-1},ak ; z) = (-1)^k Li_{mk,...,m1}(a_{k-1}/a_k,...,a1/a2,z/a1).

   WHY: the subscripted objects Subscript[Li, n0, m...][c...] carry this convention,
   and their conversion rules hand those objects straight to LiToG.  Before the
   change LiToG read them in the opposite (decreasing) convention, so those three
   functions were silently WRONG from depth 2 on.  Verified: Li0ToG of
   Subscript[Li,0,2,1][x,y] gave G({0,y,1},xy) but must give G({x,0,1},xy).

   *** THE ONE REMAINING INCONSISTENCY IN THE PACKAGE SET ***
   NumPolyLog.m's numLi[m, x] keeps the OPPOSITE (decreasing) convention:

       numLi[{m1,...,mk},{x1,...,xk}]  =  sum over  n1 > n2 > ... > nk > 0

   NumPolyLog.m is deliberately not modified.  To move between the two, reverse
   BOTH lists:   Li[{m...},{x...}]  ==  numLi[Reverse[{m...}], Reverse[{x...}]].
   Depth 1 is unaffected; the difference starts at depth 2.
   Verified numerically to 25 digits, 2026-07-28 (depths 2 and 3).
   --------------------------------------------------------------------------- *)

LiToG[function_] := function /.
  Li[m_List, x_List] /; Length[m] === Length[x] :>
   (-1)^Length[m] G[gLonghand[Reverse[m],
      Table[Times @@ Reverse[x][[j + 1 ;; -1]], {j, Length[x]}]], Times @@ x];

(* depth-1 Li's as the built-in classical polylogarithms (readability / numerics) *)
LiToPolyLog[function_] := function /. {Li[{1}, {x_}] :> -Log[1 - x], Li[{m_}, {x_}] :> PolyLog[m, x]};

(* ---------- function-level shuffle and stuffle relations ----------

   These routines return the RIGHT-HAND SIDE of the relevant product identity;
   the corresponding *Relation routine returns lhs == rhs.

   G shuffle (common endpoint z):
     G[u,z] G[v,z] = Sum_{w in u shuffle v} G[w,z].

   Li stuffle uses this file's increasing-index convention

     Li[{m1,...},{x1,...}] = Sum_{0<n1<...} x1^n1 .../(n1^m1 ...).

   Thus decorated letters {m,x} quasi-shuffle with
     {m,x} o {n,y} = {m+n,x y}.

   Multiplicities are retained: for example, shuffling or stuffling an object
   with itself produces the appropriate factor of 2.  No PolyLogTools code is
   loaded or used. *)

ClearAll[symbologyShuffleWordLists, GShuffleProduct, GShuffleRelation,
  symbologyStuffleWords, symbologyStuffleWordLists,
  LiStuffleProduct, LiStuffleRelation, symbologyLi1RegWord, Li1reg];

symbologyShuffleWordLists[words_List] := Fold[
  Function[{acc, next},
    Flatten[(Function[word, NumPolyLog`Shuffle[word, next]] /@ acc), 1]],
  {First[words]}, Rest[words]];

GShuffleProduct[g1_G, g2_G, rest___G] /;
    SameQ @@ (Last[List @@ #] & /@ {g1, g2, rest}) := Module[
  {gs = {g1, g2, rest}, words, endpoint},
  words = First[List @@ #] & /@ gs;
  endpoint = Last[List @@ g1];
  Total[G[#, endpoint] & /@ symbologyShuffleWordLists[words]]
  ];

GShuffleRelation[g1_G, g2_G, rest___G] /;
    SameQ @@ (Last[List @@ #] & /@ {g1, g2, rest}) :=
  Times @@ {g1, g2, rest} == GShuffleProduct[g1, g2, rest];

symbologyStuffleWords[{}, word_List] := {word};
symbologyStuffleWords[word_List, {}] := {word};
symbologyStuffleWords[{{m_, x_}, tail1___}, {{n_, y_}, tail2___}] := Join[
  (Prepend[#, {m, x}] &) /@
    symbologyStuffleWords[{tail1}, {{n, y}, tail2}],
  (Prepend[#, {n, y}] &) /@
    symbologyStuffleWords[{{m, x}, tail1}, {tail2}],
  (Prepend[#, {m + n, x y}] &) /@
    symbologyStuffleWords[{tail1}, {tail2}]
  ];

symbologyStuffleWordLists[words_List] := Fold[
  Function[{acc, next},
    Flatten[(Function[word, symbologyStuffleWords[word, next]] /@ acc), 1]],
  {First[words]}, Rest[words]];

LiStuffleProduct[li1_Li, li2_Li, rest___Li] /;
    AllTrue[{li1, li2, rest},
      MatchQ[#, Li[m_List, x_List] /; Length[m] == Length[x]] &] := Module[
  {lis = {li1, li2, rest}, words},
  words = (Transpose[List @@ #] &) /@ lis;
  Total[(Li[#[[All, 1]], #[[All, 2]]] &) /@
    symbologyStuffleWordLists[words]]
  ];

LiStuffleRelation[li1_Li, li2_Li, rest___Li] /;
    AllTrue[{li1, li2, rest},
      MatchQ[#, Li[m_List, x_List] /; Length[m] == Length[x]] &] :=
  Times @@ {li1, li2, rest} == LiStuffleProduct[li1, li2, rest];

LiStuffleDecompose[func_]:=FixedPoint[(Expand[#]//.(f1_Li*f2_Li):>LiStuffleProduct[f1,f2])&,func]

(* Stuffle reduction at a terminal variable 1.

   (i) Li[{...,1,...,1},{...,1,...,1}] is genuinely divergent and uses the
       regularized value Li[{1},{1}]_reg.

   (ii) For an arbitrary nonempty terminal block T whose variables are all 1,
        write the word as P T with the last variable of P different from 1.
        Solve the stuffle product Li[P] Li[T] for Li[P T] and drop the product,
        consistently with this project's standing convention of working
        modulo products.  Every other stuffle has a shorter terminal block of
        variable-1 letters, so recursive reduction terminates.

   The default tangential prescription is Li[{1},{1}]_reg = 0.  More
   generally Li1reg[expr,t] assigns it the formal value t.  If a word has k
   terminal {1,1} decorated letters, stuffling its prefix with Li[{1},{1}]
   produces that word with multiplicity k.  Solving that relation recursively
   lowers the number of terminal ones and therefore terminates. *)

symbologyLi1RegWord[{}, li1value_] := 1;
symbologyLi1RegWord[word_List, li1value_] := Module[
  {terminalVariablesOne, terminalOnes, prefix, tail, prefixLi, tailLi,
   targetLi, stuffle, targetMultiplicity, otherTerms},
  terminalVariablesOne =
    LengthWhile[Reverse[word], SameQ[#[[2]], 1] &];
  terminalOnes = LengthWhile[Reverse[word], SameQ[#, {1, 1}] &];

  (* A depth-one endpoint value cannot be moved to an earlier slot. *)
  If[Length[word] == 1,
    Return[If[SameQ[First[word], {1, 1}], li1value,
      Li[{word[[1, 1]]}, {word[[1, 2]]}]]]
    ];

  (* Reduce the entire terminal variable-1 block at once.  Since prefix ends
     in a non-1 variable, the concatenation prefix.tail occurs exactly once. *)
  If[0 < terminalVariablesOne < Length[word],
    prefix = Take[word, Length[word] - terminalVariablesOne];
    tail = Take[word, -terminalVariablesOne];
    prefixLi = Li[prefix[[All, 1]], prefix[[All, 2]]];
    tailLi = Li[tail[[All, 1]], tail[[All, 2]]];
    targetLi = Li[word[[All, 1]], word[[All, 2]]];
    stuffle = LiStuffleProduct[prefixLi, tailLi];
    targetMultiplicity = Coefficient[stuffle, targetLi];
    otherTerms = Expand[stuffle - targetMultiplicity targetLi];
    Return[Expand[-Li1reg[otherTerms, li1value]/targetMultiplicity]]
    ];

  If[terminalOnes == 0,
    Return[Li[word[[All, 1]], word[[All, 2]]]]
    ];
  prefix = Most[word];
  If[prefix === {}, Return[li1value]];
  prefixLi = Li[prefix[[All, 1]], prefix[[All, 2]]];
  targetLi = Li[word[[All, 1]], word[[All, 2]]];
  stuffle = LiStuffleProduct[prefixLi, Li[{1}, {1}]];
  targetMultiplicity = Coefficient[stuffle, targetLi];
  otherTerms = Expand[stuffle - targetMultiplicity targetLi];
  Expand[(li1value symbologyLi1RegWord[prefix, li1value] -
      Li1reg[otherTerms, li1value])/targetMultiplicity]
  ];

Li1reg[expr_, li1value_: 0] := expr /.
  Li[m_List, x_List] /; Length[m] == Length[x] :>
    symbologyLi1RegWord[Transpose[{m, x}], li1value];

(* Raise the depth of Li[{1,...,1,m},vars] by one, using the generalized
   leading-index Li1ToG conversion.  This is a replacement rule, intended for
   use as expr /. to1moredepthli.  Li1ToG is supplied by the higher-polylog
   layer and is resolved only when the delayed rule is actually applied. *)
to1moredepthli =
  Li[mlist_List, varlist_List] /;
      AllTrue[mlist[[1 ;; -2]], (# == 1) &] :>
    Block[{li1tog =
       GToLi[Li1ToG[
         Subscript[Li,
           Sequence @@ Join[{Last[mlist] - 1}, mlist[[1 ;; -2]], {1}]] @@
          varlist]],
      licand =
       Li[Join[{Last[mlist] - 1}, mlist[[1 ;; -2]], {1}], varlist],
      coeff},
     coeff = Coefficient[li1tog, Li[mlist, varlist]];
     Expand[(licand - li1tog)/coeff + Li[mlist, varlist]]
     ];

Twisted[function_, totalktwist_Integer] := (Coefficient[#1, vep, totalktwist] & )[function /. IH[list___] :> Sum[TwistedIHsingle[IH[list], iktwist]*vep^iktwist, {iktwist, 0, totalktwist}]]
TwistedCloseIHsingle[functionIH_, ktwist_Integer] := functionIH /. IH[list__] :> Block[{len = Length[{list}], weights}, weights = Flatten[Permutations /@ (IntegerPartitions[ktwist + len, {len}] - 1), 1]; Total[((Times @@ #1 & )[Reverse[Range[0, len - 1] /. 0 -> eps]^#1 /. eps -> 0]*IH @@ Flatten[(Table @@ #1 & ) /@ Transpose[{{list}, #1 + 1}]] & ) /@ weights]];
TwistedCloseIH[function_, totalktwist_Integer] := (Coefficient[#1, vep, totalktwist] & )[function /. IH[list___] :> Sum[TwistedCloseIHsingle[IH[list], iktwist]*vep^iktwist, {iktwist, 0, totalktwist}]]
TwistedCloseIHsingle[IH[list___], alphaset_, ktwist_Integer] /; Length[{list}] === Length[alphaset] + 1 := Block[{len = Length[{list}], weights, alphaorderset = Table[Total[alphaset[[ii ;; All]]], {ii, Length[alphaset]}]}, weights = Cases[Flatten[Permutations /@ (IntegerPartitions[ktwist + len, {len}] - 1), 1], {___, 0}]; Total[((Times @@ #1 & )[alphaorderset^#1[[1 ;; -2]]]*IH @@ Flatten[(Table @@ #1 & ) /@ Transpose[{{list}, #1 + 1}]] & ) /@ weights]];
TwistedCloseIH[function_, alphaset_, totalktwist_Integer] /; AllTrue[MonomialList[function], Exponent[#1 /. IH[___] :> ih, ih] == 1 & ] := (Coefficient[#1, vep, totalktwist] & )[function /. IH[list___] :> Sum[TwistedCloseIHsingle[IH[list], alphaset, iktwist]*vep^iktwist, {iktwist, 0, totalktwist}]]

(* other functions: *)
PSLQCoeff[list_List] := Block[{vars = Variables[list], coeflist}, coeflist = (Coefficient[#1, vars] & ) /@ list; If[AllTrue[Flatten[coeflist], NumberQ], NullSpace[Transpose[coeflist]], "Failed: not linear function"]];


(* ===================== symbol-grammar bridge (NumPolyLog) ===================== *)
(* PolyLogTools CiTi  ->  NumPolyLog Tensor ; the symbol product (ShuffleCiTi, which auto-
   shuffles under Times) is supplied here via NumPolyLog's Shuffle. *)
SetAttributes[Tensor, Flat];   (* nested Tensor[Tensor[..],..] auto-flattens (twist letters splice in) *)

(* NumPolyLog.m keeps ExpandTensor hidden/unreliable in some load contexts.
   Keep only Global`ExpandTensor public here; all helpers stay local. *)
ClearAll[Global`ExpandTensor];
Global`ExpandTensor[exp_] := Module[{alphabet, rules, tensor, normalizeTensor},
  alphabet = Cases[exp, Tensor[y__] :> y, Infinity];
  rules = Dispatch[DeleteCases[(# -> Factor[#] &) /@ alphabet, Rule[xx_, xx_]]];

  normalizeTensor[expr_] := Module[{tensor},
    tensor[___, 1 | -1, ___] := 0;
    tensor[x___, 1/y_, w___] := -tensor[x, y, w];
    tensor[x___, y_^a_Integer, w___] := a tensor[x, y, w];
    tensor[x___, y_, w___] /; y =!= 0 && y === First@Sort[{-y, y}] :=
      tensor[x, -y, w];
    Expand[expr /. Tensor -> tensor, _tensor] /. tensor -> Tensor
    ];

  normalizeTensor[exp /. aa_Tensor :> Replace[aa, rules, 1] /.
    Tensor[x___] :> Distribute[Tensor[x], Times, Tensor, Plus]]
  ];
ShuffleCiTi /: ShuffleCiTi[a__] ShuffleCiTi[b__] := Total[ShuffleCiTi @@@ Shuffle[{a}, {b}]];
ShuffleCiTi /: ShuffleCiTi[a__]^2 := Total[ShuffleCiTi @@@ Shuffle[{a}, {a}]];

(* ---------- CiTi grammar (PolyLogTools convention) ----------
   A symbol is CiTi[l1,...,lw].  CiTiShuffle merges a product of region symbols into the
   shuffle; it stays inert while CloseChain factors are unevaluated and fires once they
   become CiTi's. *)
shufWords[a_List,b_List]:=Which[a==={},{b},b==={},{a},True,
  Join[Prepend[#,First[a]]&/@shufWords[Rest[a],b],Prepend[#,First[b]]&/@shufWords[a,Rest[b]]]];
shuf2[a_,b_]:=shp[a,b]//.{
  shp[u_+v_,y_]:>shp[u,y]+shp[v,y], shp[y_,u_+v_]:>shp[y,u]+shp[y,v],
  shp[c_ x_,y_]/;FreeQ[c,CiTi]:>c shp[x,y], shp[y_,c_ x_]/;FreeQ[c,CiTi]:>c shp[y,x],
  shp[CiTi[p__],CiTi[q__]]:>Total[CiTi@@@shufWords[{p},{q}]],
  shp[CiTi[p__],c_]/;FreeQ[c,CiTi]:>c CiTi[p], shp[c_,CiTi[q__]]/;FreeQ[c,CiTi]:>c CiTi[q],
  shp[c_,d_]/;FreeQ[{c,d},CiTi]:>c d};
CiTiShuffle[x_]:=x;
CiTiShuffle[xs__]/;FreeQ[{xs},CloseChain]:=Fold[shuf2,First[{xs}],Rest[{xs}]];


(* ---------- ShuffleProduct: one head, both grammars ----------
   1. arguments contain CloseChain          -> stays INERT (fires after CloseChain resolves)
   2. arguments contain NumPolyLog Tensor's -> Tensor shuffle
   3. arguments contain CiTi symbols        -> CiTiShuffle
   4. nothing symbolic                      -> plain product                                *)
Clear[ShuffleProduct];
ShuffleProduct[x_] := x;
ShuffleProduct[xs__] /; FreeQ[{xs}, CloseChain] && ! FreeQ[{xs}, Tensor] :=
  Expand[Times[xs]] //. {
   HoldPattern[Times[pre___, Tensor[x__], mid___, Tensor[y__], post___]] :>
       Expand[Times[pre, mid, post] Total[Tensor @@@ Shuffle[{x}, {y}]]],
   HoldPattern[Power[Tensor[x__], n_Integer] /; n >= 2] :>
       Expand[Power[Tensor[x], n - 2] Total[Tensor @@@ Shuffle[{x}, {x}]]]};
ShuffleProduct[xs__] /; FreeQ[{xs}, CloseChain] && FreeQ[{xs}, Tensor] && ! FreeQ[{xs}, CiTi] :=
  CiTiShuffle[xs];
ShuffleProduct[xs__] /; FreeQ[{xs}, CloseChain] && FreeQ[{xs}, Tensor] && FreeQ[{xs}, CiTi] :=
  Times[xs];


(* ---------- Product projector on symbols ----------

   Duhr--Dulat, arXiv:1904.07279, eqs. (7.10)--(7.11):

     rho(a1...an) = rho(a1...a(n-1)) an - rho(a2...an) a1,
     Pi(w) = rho(w)/Length[w].

   The kernel of Pi is the span of non-trivial shuffle products.  This is a
   native implementation in the NumPolyLog Tensor grammar and has no
   PolyLogTools dependency.  Tensor products are shuffle-expanded before Pi
   is applied; weight-zero terms are discarded.  Accepted representations:

     Tensor expression                        -> Tensor expression
     {{coefficient,{letters...}},...}          -> symbol list
     Association[{letters...}->coefficient]    -> Association                 *)

ClearAll[symbologyMergeWordAssociations, symbologyAppendWord,
  symbologyRhoWord, symbologyProjectWordAssociation,
  symbologyShuffleTensorProducts, symbologyTensorWordAssociation,
  symbologyWordAssociationTensor, ProductProjector];

symbologyMergeWordAssociations[as_List] :=
  If[as === {}, Association[], DeleteCases[Merge[as, Total], 0]];

symbologyAppendWord[assoc_Association, letter_] :=
  Association[KeyValueMap[Append[#1, letter] -> #2 &, assoc]];

symbologyRhoWord[{a_}] := Association[{a} -> 1];
symbologyRhoWord[word_List] /; Length[word] > 1 :=
  symbologyRhoWord[word] = symbologyMergeWordAssociations[{
    symbologyAppendWord[symbologyRhoWord[Most[word]], Last[word]],
    Map[-# &, symbologyAppendWord[symbologyRhoWord[Rest[word]], First[word]]]
  }];

symbologyProjectWordAssociation[words_Association] :=
  symbologyMergeWordAssociations[
    KeyValueMap[Function[{word, coefficient},
      If[Length[word] == 0, Association[],
        Map[coefficient #/Length[word] &, symbologyRhoWord[word]]]], words]];

symbologyShuffleTensorProducts[expr_] := FixedPoint[
  Expand[# /. {
    HoldPattern[Tensor[a___] Tensor[b___]] :>
      Total[Tensor @@@ NumPolyLog`Shuffle[{a}, {b}]],
    HoldPattern[Power[Tensor[a___], n_Integer] /; n >= 2] :>
      Tensor[a]^(n - 2) Total[Tensor @@@ NumPolyLog`Shuffle[{a}, {a}]]
  }] &, Expand[expr]];

symbologyTensorWordAssociation[expr_] := Module[
  {expanded = symbologyShuffleTensorProducts[expr], terms, pieces},
  terms = If[Head[expanded] === Plus, List @@ expanded, {expanded}];
  pieces = Map[Function[term, Module[{tensors, coefficient},
      tensors = Cases[{term}, Tensor[a__] :> {a}, Infinity];
      If[Length[tensors] === 1,
        coefficient = term /. _Tensor -> 1;
        Association[tensors[[1]] -> coefficient],
        Association[]]]], terms];
  symbologyMergeWordAssociations[pieces]];

symbologyWordAssociationTensor[words_Association] :=
  Total[KeyValueMap[#2 Tensor @@ #1 &, words]];

ProductProjector[words_Association] :=
  symbologyProjectWordAssociation[words];

ProductProjector[symbol_List] /;
    AllTrue[symbol, MatchQ[#, {_, _List}] &] :=
  KeyValueMap[{#2, #1} &,
    symbologyProjectWordAssociation[
      symbologyMergeWordAssociations[
        Map[Association[#[[2]] -> #[[1]]] &, symbol]]]];

ProductProjector[expr_] :=
  symbologyWordAssociationTensor[
    symbologyProjectWordAssociation[
      symbologyTensorWordAssociation[expr]]];



shuffleexpand = {Tensor[a__] :> ShuffleCiTi[a], Tens[a__] :> ShuffleCiTi[a], ElTens[ax__] :> ax, (sct1_)*((sct2___) + ShuffleCiTi[cc___]) :> Expand[sct1*(sct2 + ShuffleCiTi[cc])]}; 


Clear[FindInd,FindNull];
FindNull[listred_List]:=Block[{var=Variables[listred],nullvec,solvedset,len},len=Length[listred];((Coefficient[#,var]&/@listred)//Transpose//NullSpace)];
FindInd[listraw_List,listred_List]/;Length[listraw]===Length[listred]:=Block[{var=Variables[listred],nullvec,len},len=Length[listraw];nullvec=FindNull[listred];If[nullvec==={},listraw,Block[{solvedset,nullvecneat},nullvecneat=nullvec//RowReduce//DeleteCases[#,{0...}]&;solvedset=First[Position[#,1]][[1]]&/@nullvecneat;Table[listraw[[ii]]-If[MemberQ[solvedset,ii],nullvecneat[[Position[solvedset,ii][[1,1]]]] . listraw,0],{ii,len}]]]];


Clear[CombineLog];

CombineLog[expr_]:=Module[{e,terms,logterms,rest,data,splitcoef},e=Expand[expr];
terms=If[Head[e]===Plus,List@@e,{e}];
splitcoef[c_]:=Module[{fac,num,pref},fac=If[Head[c]===Times,List@@c,{c}];
num=Times@@Select[fac,NumericQ];
pref=Times@@Select[fac,Not@*NumericQ];
{pref,num}];
logterms=Select[terms,MatchQ[#,_. Log[_]]&];
rest=Total@Select[terms,!MatchQ[#,_. Log[_]]&];
data=logterms/. c_. Log[x_]:>With[{sp=splitcoef[c]},{sp[[1]],sp[[2]],x}];
rest+Total[Map[Function[group,group[[1,1]] Log[Times@@Map[(#[[3]]^#[[2]])&,group]]],GatherBy[data,First]]]]
