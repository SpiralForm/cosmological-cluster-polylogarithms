(* ::Package:: *)

(* Ancillary code for
   "de Sitter Wavefunction from Quadrangular Polylogarithms: loops".

   QLiB is the B-type quadrangular polylogarithm defined in Section 3.
   Only the root-last ordering is included.
   QLip[n,mypg] is the A-type companion built from Tarp, with the
   weighted word reversed and n retained as the leading Li index.
   The original chain function QLi is not defined or required.

   QLiB[n] uses {1,...,2n,bar[1],...,bar[2n]}.
   QLiB[mypg] takes the full alternating, centrally symmetric vertex list.
   Integer labels specify parity; bar[i] has the parity of i.

   The output is Subscript[Li,m1,...,md][z1,...,zd], with the convention
   Sum[z1^n1 ... zd^nd/(n1^m1 ... nd^md), 0 < n1 < ... < nd].
   These multiple polylogarithms remain symbolic.
   Cross-ratios are expressed using Subscript[z,i], as in the source code.
   No external package is required.
*)

(* ::Section:: *)
(*Cross-ratios*)

ClearAll[Unbar, cr0, crstrp, ab, Joinab, Dotab, Qshab, Tarp,
  FindStripDissection, Reverseab, TarpB, Li, QLip, QLiB];

Unbar[expr_] := expr /. bar[i_Integer] :> i;


cr0[a_,b_,c_,d_]:=-(a-b)(c-d)/((a-d)(b-c))//Factor;

crstrp[list___] /; EvenQ[Length[{list}]/2] &&
    AllTrue[Differences[{list}] /. bar[ii_] :> ii, OddQ] :=
  If[EvenQ[First[{list}] /. bar[ii_] :> ii],
    crstrp @@ RotateLeft[{list}],
    With[{len = Length[{list}]},
      (-1)^(len/4)
       Product[Subscript[z, {list}[[2 ii]]] - Subscript[z, {list}[[2 ii + 1]]],
         {ii, 1, len/4}]/
       Product[Subscript[z, {list}[[2 ii - 1]]] - Subscript[z, {list}[[2 ii]]],
         {ii, 1, len/4}]]];



(* ::Section:: *)
(*Weighted words*)


ab[]:=Sequence[];


Joinab[ab1_]:=ab1;
Joinab[ab1_,ab2_]/;MonomialList[ab2]==={ab2}:=Inner[Join,First/@FactorList[ab1],First/@FactorList[ab2],Times]/.Join->Times;
Joinab[ab1_,abpoly_]:=Joinab[ab1,#]&/@MonomialList[abpoly]//Total;


Dotab[i_Integer,j_Integer]:=i j;
Dotab[ab[{phi1_,m1_Integer}],ab[{phi2_,m2_Integer}]]:=ab[{phi1*phi2,m1+m2}];
Dotab[ab[{phi1_,m1_Integer}],ab[{phi2_,m2_Integer},omegas__]]:=ab[{phi1*phi2,m1+m2},omegas];
Dotab[ab1_,ab2_]/;MonomialList[ab2]==={ab2}:=Inner[Dotab,First/@FactorList[ab1],First/@FactorList[ab2],Times];
Dotab[ab1_,abpoly_]:=Dotab[ab1,#]&/@MonomialList[abpoly]//Total;


Qshab[i_Integer,j_Integer]:=i j;
Qshab[]:=Sequence[];
Qshab[ab_]:=ab;
Qshab[ab[omega1_,omegas1___],ab[omega2_,omegas2___]]:=Joinab[ab[omega1],Qshab[ab[omegas1],Joinab[ab[omega2],ab[omegas2]]]]+Joinab[ab[omega2],Qshab[ab[omegas2],Joinab[ab[omega1],ab[omegas1]]]]+Joinab[Dotab[ab[omega1],ab[omega2]],Qshab[ab[omegas1],ab[omegas2]]];
Qshab[ab1_,ab2_]/;MonomialList[ab2]==={ab2}&&MonomialList[ab1]=={ab1}:=Inner[Qshab,First/@FactorList[ab1],First/@FactorList[ab2],Times];
Qshab[abpoly1_,abpoly2_]:=Outer[Qshab,MonomialList[abpoly1],MonomialList[abpoly2]]//Flatten//Total;





(* ::Section:: *)
(*Arborification*)


Tarp[a_,b_]/;IntegerQ[Unbar[a]]&&IntegerQ[Unbar[b]]:=Sequence[];
Tarp[a_,b_,c_,d_]/;And@@(IntegerQ/@Unbar[{a,b,c,d}])&&And@@(OddQ/@Unbar[{a-b,b-c,c-d}]):=If[EvenQ[Unbar[a]],ab[{cr0[Subscript[z, a],Subscript[z, b],Subscript[z, c],Subscript[z, d]],1}],-ab[{1/cr0[Subscript[z, a],Subscript[z, b],Subscript[z, c],Subscript[z, d]],1}]];
Tarp[list___]/;(#>4&&EvenQ[#]&[Length[{list}]])&&(OddQ/@Unbar[Table[({list}[[i]]-{list}[[i-1]]),{i,2,Length[{list}]}]]//And[##]&@@#&):=Block[{fir=First[{list}],las=Last[{list}],len=Length[{list}]},Sum[#[Tarp[fir,{list}[[i]],{list}[[j]],las],Qshab[Tarp[##]&@@({list}[[Range[i]]]),Qshab[Tarp[##]&@@({list}[[Range[i,j]]]),Tarp[##]&@@({list}[[Range[j,Length[{list}]]]])]]]&/@If[EvenQ[Unbar[fir]],{Joinab,Dotab},{Joinab}]//Total,{i,2,len,2},{j,i+1,len-1,2}]];


FindStripDissection[list___] :=
  Module[{fullList = {list}, n, half, centralHalfPositions,
      centralPositions, cyclicInterval, complementPolygons},
    n = Length[fullList];
    If[Mod[n, 4] =!= 0, Return[$Failed]];
    half = n/2;
    cyclicInterval[a_, b_] :=
      If[a <= b, Range[a, b], Join[Range[a, n], Range[1, b]]];
    centralHalfPositions =
      Select[Subsets[Range[half], {2, half, 2}],
        AllTrue[Differences[#], OddQ] &];
    Table[
      centralPositions = Join[pos, pos + half];
      complementPolygons = Table[
        cyclicInterval[centralPositions[[i]],
          centralPositions[[Mod[i, Length[centralPositions]] + 1]]],
        {i, Length[pos]}];
      complementPolygons = Select[complementPolygons, Length[#] > 2 &];
      {fullList[[centralPositions]], (fullList[[#]] &) /@ complementPolygons},
      {pos, centralHalfPositions}]];


Reverseab[expr_] :=
  expr /. HoldPattern[ab[omega___]] :> ab @@ Reverse[{omega}];


(* Append the central letter after reversing the complementary words. *)
TarpB[list___] /; Length[{list}] > 1 /; EvenQ[Length[{list}]/2] :=
  Module[{n = Length[{list}]/4, stripdislist = FindStripDissection[list]},
    Sum[
      With[{m = Length[dis[[1]]]/4,
          complement =
            Fold[Qshab, Tarp @@ # & /@ dis[[2]]] /.
              Fold[Qshab, {}] -> Sequence[]},
        Reverseab[
          Joinab[(-1)^n ab[{crstrp @@ dis[[1]], m}], complement]]],
      {dis, stripdislist}]];
TarpB[nn_Integer]:=TarpB@@Join[Range[2nn],bar/@Range[2nn]];

(* ::Section:: *)
(*B-type quadrangular polylogarithms*)


Li[ab[omega__]]:=Subscript[Li, ##&@@Last/@{omega}][##]&@@First/@{omega};
Li[-ab[omega__]]:=-Subscript[Li, ##&@@Last/@{omega}][##]&@@First/@{omega};
Li[0]:=0;   (* empty arborification -> zero function; also stops Li[0] self-recursion *)
Li[abpoly_]:=Li[#]&/@MonomialList[abpoly]//Total;

(* QLip uses Tarp; the original chain QLi uses a different arborification. *)
QLip[n_Integer,mypg_List]/;And@@(OddQ/@Unbar[mypg[[2;;]]-mypg[[;;-2]]]):=
  Li[Reverseab[Tarp@@mypg]]/.
    Subscript[Li,ns__][cs__]:>Subscript[Li,n,ns][cs];

QLiB[mypg_List]/;Length[mypg]>1/;EvenQ[Length[mypg]/2]:=
  Li[TarpB@@mypg];
QLiB[n_Integer]:=Li[TarpB[n]];


(* ::Section:: *)
(*Examples*)

(* QLiB[1] *)
(* QLiB[2] *)
(* QLiB[3] *)
(* QLiB[{1,2,3,4,bar[1],bar[2],bar[3],bar[4]}] *)
