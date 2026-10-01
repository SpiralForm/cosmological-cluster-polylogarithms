(* ::Package:: *)

(* orthoschemenew.m -- PolyLogTools-free rewrite of code/orthoscheme.m.
   Created 2026-07-28 from code/orthoscheme.m (2026-05-30) line by line.

   ---------------------------------------------------------------------------
   WHAT THIS FILE NEEDS
   ---------------------------------------------------------------------------
   * Nothing at all for the bulk of it (cross-ratios, the ab-algebra,
     arborification, the QLi family, polygon algebra, the ALi/li/IH coproducts,
     the orthoscheme geometry, Cr2Ort, CL, expandlog): built-in Mathematica only.
   * symbology.m -- ONLY for the three converters `per`, `Li0ToG`, `Li1ToG`, which
     call symbology.m's `LiToG` (and `GToLi`).  Load symbology.m first if you use them.
     Everything else in this file is independent of symbology.m and NumPolyLog.m.

   ---------------------------------------------------------------------------
   *** Li ORDERING: PolyLogTools (increasing) convention, shared with symbology.m
   since 2026-07-28.  Only NumPolyLog.m's numLi differs (decreasing).
   See the boxed note at the Li[ab[...]] definition below. ***

   ---------------------------------------------------------------------------
   NAME COLLISIONS (checked 2026-07-28 against symbology.m, NumPolyLog.m,
   HypExp.m, and the rest of the shared package stack)
   ---------------------------------------------------------------------------
   * No top-level definition is defined twice.  Zero conflicts.
   * Three heads are SHARED but with disjoint patterns, so they coexist:
       Li   -- here Li[ab[...]] and the 1-argument Li[abpoly_];
               symbology.m only ever uses the 2-argument Li[{m...},{x...}].
       IH   -- inert here too: the rule IH[x1_,x2_]:=1 of orthoscheme.m was
               DELETED on request, so IH never auto-evaluates.
       CiTi -- here only inside nice/nicest;  symbology.m carries the shuffle rules.
   * HypExp.m lives in its own context (HypExp`), so its Global`-looking names
     (per, norm, log, li, wd, ...) do not clash.
   * No duplicated top-level definitions with the shared core.

   ---------------------------------------------------------------------------
   WHAT WAS CHANGED RELATIVE TO orthoscheme.m
   ---------------------------------------------------------------------------
   * `SymbolFactor` (PolyLogTools) is replaced by the self-contained
     `SymbolFactorQ` defined below, used by nice/nicest.
   * DELETED (2026-07-28, on request): `perd`, `perr`, `persv`, `CLAS`, `CLD`
     -- they needed the PolyLogTools coproduct (`Delta`/`CT`) and
     `TranscendentalWeight`; and `ComplexPerLorentz`, `ComplexPerLorentzreal`
     -- they called the undefined `Sgn`.  All seven are unused in every
     notebook of this project (0 occurrences).  The originals remain in
     code/orthoscheme.m, which was not touched.

   ---------------------------------------------------------------------------
   KNOWN DANGLING SYMBOLS, inherited unchanged from orthoscheme.m
   ---------------------------------------------------------------------------
   * QLisym / QLiid produce the inert heads QQLi / QQLisym, which nothing
     defines.  That is by design (they are formal expressions to be rewritten
     later) -- both are heavily used in the notebooks.
   * Subscript[NLi,...] produces GLi[...].  GLi is defined nowhere in this
     project and PolyLogTools is not installed on this machine, so NLi cannot
     currently be evaluated.  NLi has 0 uses in the notebooks -- say the word
     and it goes too.
*)


(* ================= 0. blinding bar ================= *)


Unprotect[EvenQ,OddQ,IntegerQ];
EvenQ[expr_]/;!FreeQ[expr, bar[_Integer]]:=EvenQ[expr/.bar[i_Integer]:>i];
OddQ[expr_]/;!FreeQ[expr, bar[_Integer]]:=OddQ[expr/.bar[i_Integer]:>i];
IntegerQ[expr_]/;!FreeQ[expr, bar[_Integer]]:=IntegerQ[expr/.bar[i_Integer]:>i];
Protect[EvenQ,OddQ,IntegerQ];


Clear[Unbar];
Unbar[expr_]:=expr/.bar[i_Integer]:>i;


(* ================= 1. cross-ratios ================= *)
cr0[a_,b_,c_,d_]:=-(a-b)(c-d)/((a-d)(b-c))//Factor;
cr[list___]/;(And@@(IntegerQ/@{list}))&&EvenQ[Length[{list}]]:=Product[cr0[Subscript[z,{list}[[1]]],Subscript[z,{list}[[i-1]]],Subscript[z,{list}[[i]]],Subscript[z,{list}[[i+1]]]]^((-1)^({list}[[1]]//Unbar)),{i,3,Length[{list}]-1,2}];
cr[list___]:=cr[list]/.Subscript[z, i_]:>i;
cr[{list___}]:=cr[list];


crf[list___]:=1/cr[list];


crq[{list___}]:=crq[list];
crq[list___]/;EvenQ[Length[{list}]]:=Product[Subscript[z,{list}[[i]]]-Subscript[z,{list}[[i+1]]],{i,1,Length[{list}]-1,2}]/(Product[Subscript[z,{list}[[i]]]-Subscript[z,{list}[[i+1]]],{i,2,Length[{list}]-2,2}]*(Subscript[z,{list}[[1]]]-Subscript[z,{list}[[-1]]]));

(* ================= 2. weighted alphabet algebra ================= *)
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



(* ================= 3. arborification ================= *)


Tarb[a_,b_]/;IntegerQ[a]&&IntegerQ[b]:=Sequence[];
Tarb[a_,b_,c_,d_]/;And@@(IntegerQ/@{a,b,c,d})&&And@@(OddQ/@({a-b,b-c,c-d})):=If[EvenQ[a],-ab[{cr0[Subscript[z, a],Subscript[z, b],Subscript[z, c],Subscript[z, d]],1}],ab[{1/cr0[Subscript[z, a],Subscript[z, b],Subscript[z, c],Subscript[z, d]],1}]];
Tarb[list___]/;(#>4&&EvenQ[#]&[Length[{list}]])&&(OddQ/@Table[({list}[[i]]-{list}[[i-1]]),{i,2,Length[{list}]}]//And[##]&@@#&):=Block[{fir=First[{list}],las=Last[{list}],len=Length[{list}]},Sum[#[Tarb[fir,{list}[[i]],{list}[[j]],las],Qshab[Tarb[##]&@@({list}[[Range[i]]]),Qshab[Tarb[##]&@@({list}[[Range[i,j]]]),Tarb[##]&@@({list}[[Range[j,Length[{list}]]]])]]]&/@If[EvenQ[fir],{Joinab},{Joinab,Dotab}]//Total,{i,2,len,2},{j,i+1,len-1,2}]];

Tarp[a_,b_]/;IntegerQ[a]&&IntegerQ[b]:=Sequence[];
Tarp[a_,b_,c_,d_]/;And@@(IntegerQ/@{a,b,c,d})&&And@@(OddQ/@({a-b,b-c,c-d})):=If[EvenQ[a],ab[{cr0[Subscript[z, a],Subscript[z, b],Subscript[z, c],Subscript[z, d]],1}],-ab[{1/cr0[Subscript[z, a],Subscript[z, b],Subscript[z, c],Subscript[z, d]],1}]];
Tarp[list___]/;(#>4&&EvenQ[#]&[Length[{list}]])&&(OddQ/@Table[({list}[[i]]-{list}[[i-1]]),{i,2,Length[{list}]}]//And[##]&@@#&):=Block[{fir=First[{list}],las=Last[{list}],len=Length[{list}]},Sum[#[Tarp[fir,{list}[[i]],{list}[[j]],las],Qshab[Tarp[##]&@@({list}[[Range[i]]]),Qshab[Tarp[##]&@@({list}[[Range[i,j]]]),Tarp[##]&@@({list}[[Range[j,Length[{list}]]]])]]]&/@If[EvenQ[fir],{Joinab,Dotab},{Joinab}]//Total,{i,2,len,2},{j,i+1,len-1,2}]];



Tarbinq[a_Integer,b_Integer]:=Sequence[];
Tarbinq[a_Integer,b_Integer,c_Integer,d_Integer]/;(OddQ/@{a-b,b-c,c-d}//And[##]&@@#&):=If[EvenQ[a],-ab[{q[a,b,c,d],1}],ab[{q[b,c,d,a],1}]];
Tarbinq[list___]/;(#>4&&EvenQ[#]&[Length[{list}]])&&(OddQ/@Table[{list}[[i]]-{list}[[i-1]],{i,2,Length[{list}]}]//And[##]&@@#&):=Block[{fir=First[{list}],las=Last[{list}],len=Length[{list}]},Sum[#[Tarbinq[fir,{list}[[i]],{list}[[j]],las],Qshab[Tarbinq[##]&@@({list}[[Range[i]]]),Qshab[Tarbinq[##]&@@({list}[[Range[i,j]]]),Tarbinq[##]&@@({list}[[Range[j,Length[{list}]]]])]]]&/@If[EvenQ[fir],{Joinab},{Joinab,Dotab}]//Total,{i,2,len,2},{j,i+1,len-1,2}]];


ClearAll[TarbB];
ClearAll[crstrp, FindStripPolygon, FindStripDissection];

(* Strip cross-ratio in the ordering used in eqs. (3.39) and (3.43) of the
   loops draft.  A strip must be represented from an odd first label; an even
   first label is therefore rotated once before the weighted letter is made. *)
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

(* All Theta-symmetric strip polygons, together with the disconnected pieces
   of one half of their complement.  This is the one-fold strip sum appearing
   in the updated draft; the complement pieces are not dissected further. *)
FindStripPolygon[list___] /; Mod[Length[{list}], 4] === 0 :=
  Module[{len = Length[{list}]},
    (Join[{list}[[#]], {list}[[# + len/2]]] &) /@
      Select[Subsets[Range[len/2], {2, len/2, 2}],
        AllTrue[Differences[#], OddQ] &]];

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

TarbB[list___]/;Length[{list}]>1/;EvenQ[Length[{list}]/2]:=Module[{stripdislist=FindStripDissection[list]},Sum[Joinab[ab[{crstrp@@dis[[1]],Length[dis[[1]]]/4}],Fold[Qshab,Tarb@@#&/@dis[[2]]]/.Fold[Qshab,{}]->Sequence[]],{dis,stripdislist}]];
TarbB[nn_Integer]:=TarbB@@Join[Range[2nn],bar/@Range[2nn]];


ClearAll[TarpB];
ClearAll[Reverseab];
Reverseab[expr_] :=
  expr /. HoldPattern[ab[omega___]] :> ab @@ Reverse[{omega}];

(* Root-last, resummed quasi-quadrangulation formula.  Tarp produces the
   complementary A-type words in the opposite Li-argument ordering, so the
   reversal is performed here, at weighted-word level, rather than later in
   QLipB.  crstrp already contains the convention-dependent (-1)^m inside the
   strip argument.  Reversing the signs of all n-m complementary A-type
   quadrilaterals changes the external coefficient from (-1)^m to (-1)^n. *)
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


q2cr0=q[a_,b_,c_,d_]:>cr0[Subscript[z, a],Subscript[z, b],Subscript[z, c],Subscript[z, d]];


(* ================= 4. polylogarithm containers and weights ================= *)
(* ---------------------------------------------------------------------------
   Li ORDERING CONVENTION.

   Subscript[Li, n0, m1, ..., md][c1, ..., cd]  uses the INCREASING nesting
   convention,  sum over  0 < k1 < k2 < ... < kd,  i.e. PolyLogTools 1904.07279
   eq. (3.6).  Nothing in this file was changed.

   As of 2026-07-28 symbology.m's GToLi / LiToG were switched to this same
   convention, so per / Li0ToG / Li1ToG -- which hand Subscript[Li,...] objects
   straight to symbology.m's LiToG -- now agree with it again.  (While symbology.m used
   the opposite convention those three were silently wrong from depth 2 on.)

   THE ONE REMAINING INCONSISTENCY in the package set is NumPolyLog.m's
   numLi[m, x], which keeps the DECREASING convention, sum over
   k1 > k2 > ... > kd > 0.  NumPolyLog.m is deliberately never modified.
   Dictionary:  Li[{m...},{x...}] == numLi[Reverse[{m...}], Reverse[{x...}]].
   Depth 1 is unaffected; the difference starts at depth 2.
   --------------------------------------------------------------------------- --------------------------------------------------------------------------- *)

Li[ab[omega__]]:=Subscript[Li, ##&@@Last/@{omega}][##]&@@First/@{omega};
Li[-ab[omega__]]:=-Subscript[Li, ##&@@Last/@{omega}][##]&@@First/@{omega};
Li[0]:=0;   (* empty arborification -> zero function; also stops Li[0] self-recursion *)
Li[abpoly_]:=Li[#]&/@MonomialList[abpoly]//Total;


Liflip={Subscript[Li, w0_,m___][var___]/;Length[{m}]==Length[{var}]:>Subscript[Li, w0,Sequence@@Reverse[{m}]]@@Reverse[{var}],Li[{w0_,m___},{var___}]/;Length[{m}]==Length[{var}]:>Li[{w0,Sequence@@Reverse[{m}]},Reverse[{var}]],Subscript[Li, m___][var___]/;Length[{m}]==Length[{var}]:>Subscript[Li, Sequence@@Reverse[{m}]]@@Reverse[{var}],Li[{m___},{var___}]/;Length[{m}]==Length[{var}]:>Li[Reverse[{m}],Reverse[{var}]]};


Subscript[NLi, weight__][var__]/;(Length[{weight}]==Length[{var}]):=(-1)^Length[{weight}]*GLi[0,1,Sequence@@Flatten[Table[{Table[0,{weight}[[i]]-1],Product[{var}[[j]],{j,1,i}]},{i,Length[{weight}]}]]];


NGLi[a_,b_]:=1;
NGLi[list__]:=Block[{fir={list}//First,las={list}//Last,wei=Length[{list}]},Integrate[NGLi[Sequence@@Append[Delete[{list},{{-1},{-2}}],Subscript[tt, wei-2]]]/(Subscript[tt, wei-2]-{list}[[wei-1]]),{Subscript[tt, wei-2],fir,las}]]


ALi[ab[omega__]]:=Subscript[ALi, ##&@@Last/@{omega}][##]&@@First/@{omega};
ALi[-ab[omega__]]:=-Subscript[ALi, ##&@@Last/@{omega}][##]&@@First/@{omega};
ALi[abpoly_]:=ALi[#]&/@MonomialList[abpoly]//Total;


Subscript[ALi, weight__][var__]/;Length[{weight}]==Length[{var}]:=Block[{depth=Length@{weight}},(1/2^depth)Sum[Product[Subscript[eps, i],{i,depth}]Subscript[Li, weight][##]&@@Table[Subscript[eps, i]Sqrt[{var}[[i]]],{i,depth}],##]&@@Table[{Subscript[eps, i],{-1,1}},{i,depth}]];

(* per: needs LiToG from symbology.m -- the only outside dependency in this file *)
per[poly_]:=LiToG[poly/.Subscript[Li, m__][a__]:>Li[{m},{a}]];

PolylogWeight[li[abseq__]]:=Total[Last/@{abseq}];
PolylogWeight[ali[abseq__]]:=Total[Last/@{abseq}];


PolylogWeight[IH[xseq__]]:=Length[{xseq}]-2;
PolygonWeight[mypg[numseq__]]:=(Length[{numseq}]-2)/2;
PolygonWeight[mypgprod_]:=Block[{mypglist=(FactorList[mypgprod]//#1*#2&@@#&/@#&//Complement[#,{1}]&)/.num_ mypg[seq__]:>Sequence@@Table[mypg[seq],num]},(PolygonWeight/@mypglist//Total)];


(* ================= 5. polygon algebra ================= *)
ListShuffle[wd[list___]]:=wd[list];
ListShuffle[wd[list1___],wd[list2___]]:=If[Length[{list1}]==0,{wd[list2]},If[Length[{list2}]==0,{wd[list1]},{Join[wd[{list1}[[1]]],#]&/@ListShuffle[wd@@Delete[{list1},1],wd[list2]],Join[wd[{list2}[[1]]],#]&/@ListShuffle[wd@@Delete[{list2},1],wd[list1]]}//Flatten]];
ListShuffle[wdseq__]/;AllTrue[{wdseq},Head[#]==wd&]&&Length[{wdseq}]>2:=ListShuffle[#,{wdseq}//Last]&/@ListShuffle@@Delete[{wdseq},-1]//Flatten;


FindSubContinuousPolygon[{},mypg[numseq__]]:={{}};
FindSubContinuousPolygon[sizelist_,mypg[numseq__]]/;AllTrue[sizelist,EvenQ[#]&&#>=4&]&&Length[sizelist]>0&&(Total[sizelist-1]+1<=Length[{numseq}]):=Block[{len=Length[sizelist],insertslotlen=Length[{numseq}]-Total[sizelist-2]-1,insertpos,insertposr,ii,jj},insertpos=Subsets[Range[insertslotlen],{len}];insertposr=(Prepend[Delete[Accumulate[sizelist-2],-1],0]+#)&/@insertpos;(Inner[({numseq}[[Range[#1,#1+#2-1]]])&,#,sizelist,List])&/@insertposr]; (* subpolygon with certain even size *)
FindSubContinuousPolygon[mypg[numseq__]]/;Length[{numseq}]<=3:={{}};
FindSubContinuousPolygon[mypg[numseq__]]/;Length[{numseq}]>=4:=Join[{{}},Block[{numlen=Length[{numseq}],endlist,endlists},endlist=Select[Subsets[Range[numlen],{2}],(#[[2]]-#[[1]]>=3)&&OddQ[#[[2]]-#[[1]]]&];(Table[Join[{{numseq}[[endlists[[1]];;endlists[[2]]]]},#]&/@FindSubContinuousPolygon[mypg@@({numseq}[[endlists[[2]];;numlen]])],{endlists,endlist}])//Flatten[#,1]&]] (* subpolygons with general even size *)


FindSubOddokPolygon[{},mypg[numseq__]]:={{}};
FindSubOddokPolygon[sizelist_,mypg[numseq__]]/;AllTrue[sizelist,#>=3&]&&Length[sizelist]>0&&(Total[sizelist-1]+1<=Length[{numseq}]):=Block[{len=Length[sizelist],insertslotlen=Length[{numseq}]-Total[sizelist-2]-1,insertpos,insertposr,ii,jj},insertpos=Subsets[Range[insertslotlen],{len}];insertposr=(Prepend[Delete[Accumulate[sizelist-2],-1],0]+#)&/@insertpos;(Inner[({numseq}[[Range[#1,#1+#2-1]]])&,#,sizelist,List])&/@insertposr]; (* subpolygon with certain odd or even size *)


FindSubOddokPolygon[mypg[numseq__]]/;Length[{numseq}]<=2:={{}};
FindSubOddokPolygon[mypg[numseq__]]/;Length[{numseq}]>=3:=Join[{{}},Block[{numlen=Length[{numseq}],endlist,endlists},endlist=Select[Subsets[Range[numlen],{2}],(#[[2]]-#[[1]]>=2)&];(Table[Join[{{numseq}[[endlists[[1]];;endlists[[2]]]]},#]&/@FindSubOddokPolygon[mypg@@({numseq}[[endlists[[2]];;numlen]])],{endlists,endlist}])//Flatten[#,1]&]] (* subpolygons with general odd or even size *)


FindSubContinuousPolygonFixEnd[sizelist_,mypg[numseq__]]/;AllTrue[sizelist,EvenQ[#]&&#>=4&]:=Block[{netsizelist=Delete[sizelist,{{1},{-1}}],netnumseq=Sequence@@Take[{numseq},{First[sizelist],Length[{numseq}]-Last[sizelist]+1}],len=Length[{numseq}]},Join[{{numseq}[[Range[First@sizelist]]]},#,{{numseq}[[Range[len-Last[sizelist]+1,len]]]}]&/@FindSubContinuousPolygon[netsizelist,mypg[netnumseq]]]
FindSubContinuousPolygonFixEnd[mypg[numseq__]]:=Join[{{}},Block[{numlen=Length[{numseq}],endlist,endlists},endlist=Select[Subsets[Range[numlen],{2}],EvenQ[#[[1]]]&&(OddQ[#[[2]]]&&#[[1]]>=4)&&(Length[{numseq}]-#[[2]]>=3)&];Table[Join[{{numseq}[[1;;First[endlists]]]},#,{{numseq}[[Last[endlists];;numlen]]}]&/@FindSubContinuousPolygon[mypg@@{numseq}[[First[endlists];;Last[endlists]]]],{endlists,endlist}]//Flatten[#,1]&]]; (* subpolygons with certain of general even size and has the same starting and ending as the original polygon *)


(* ================= 6. ALi coproduct and full symbol on a polygon ================= *)
PolygonALiCoproduct[num1_,num2_]/;OddQ[num1-num2]:=wd[mypg[]];
PolygonALiCoproduct[numseq__]/;(And@@OddQ/@Table[{numseq}[[i]]-{numseq}[[i-1]],{i,2,Length[{numseq}]}])&&Length[{numseq}]>2&&EvenQ[Length[{numseq}]]:=Block[{len=Length[{numseq}],altlist=Select[Join[{First[{numseq}]},#,{Last[{numseq}]}]&/@Subsets[Delete[{numseq},{{-1},{1}}],{2,Length[{numseq}]-2,2}],(And@@OddQ/@Table[#[[i]]-#[[i-1]],{i,2,Length[#]}])&],altlisti,j},Table[wd[mypg@@altlisti,Times@@(mypg@@#&/@Table[Intersection[{numseq},Range[altlisti[[j]],altlisti[[j+1]]]],{j,Length[altlisti]-1}])/.mypg[ii_,jj_]:>1],{altlisti,altlist}]];(* the final equation on page 62 of Rudenko's paper: \[CapitalDelta]^HH coproduct of ALi[Subscript[T, P]] *)


PolygonALiCoproduct[{weight_},mypg[numseq__]]/;PolygonWeight[mypg@numseq]==weight:={wd[mypg[numseq]]};
PolygonALiCoproduct[weightlist_,mypg[numseq__]]/;(PolygonWeight[mypg[numseq]]==Total[weightlist])&&(Length[weightlist]>=2)&&AllTrue[weightlist,#>0&]:=Block[{lastwei=Last[weightlist],prewei=Delete[weightlist,-1],subpgsizeset=Flatten[Permutations/@IntegerPartitions[Last[weightlist]],1],subpgset,subpgs,word1},subpgset=FindSubContinuousPolygon[2#+2,mypg[numseq]]&/@subpgsizeset//Flatten[#,1]&;word1=Table[wd[mypg@@Complement[{numseq},Flatten[Map[Delete[#,{{1},{-1}}]&,subpgs,1]]],Times@@(mypg@@#&/@subpgs)],{subpgs,subpgset}];
word1/.wd[mypg1_,mypg2_]:>(Join[#,wd[mypg2]]&/@PolygonALiCoproduct[prewei,mypg1])//Flatten];(* the final equation on page 62 of Rudenko's paper: coproduct of ALi[Subscript[T, P]] order by order *)


PolygonALiSym[1]:={wd[]};
PolygonALiSym[mypg[numseq__]]:=PolygonALiSym[numseq];
PolygonALiSym[mypgprod_]:=Block[{mypglist=FactorList[mypgprod]//First/@#&//Complement[#,{1}]&},(Outer[ListShuffle,Sequence@@PolygonALiSym/@mypglist]//Flatten)/;AllTrue[Head/@mypglist,#===mypg&]];
PolygonALiSym[list__]/;(OddQ/@Table[{list}[[i]]-{list}[[i-1]],{i,2,Length[{list}]}]//And[##]&@@#&):=Block[{len=Length[{list}]},If[len<=2,{wd[]},Table[Join[wd[mypg@@({list}[[{1,i,j,len}]])],#]&/@Flatten[Outer[Flatten[Table[ListShuffle[wds,#3],{wds,ListShuffle[#1,#2]}]]&,PolygonALiSym@@({list}[[Range[i]]]),PolygonALiSym@@({list}[[Range[i,j]]]),PolygonALiSym@@({list}[[Range[j,len]]])]],{i,2,len-2,2},{j,i+1,len-1,2}]//Flatten]] (* the final equation on page 62 of Rudenko's paper: full symbol of ALi[Subscript[T, P]] *)


(* ================= 7. periods of a polygon ================= *)
RePer[mypg[numseq__]]:=Block[{weight=PolygonWeight[mypg[numseq]],par},par=Flatten[Permutations/@IntegerPartitions[weight],1];(Power[-1,If[#[[1]]==0,0,Length[#]-1]]Total[(2Pi)^weight PolygonALiCoproduct[#,mypg[numseq]]]/.wd[sym__]:>wd@@({sym}/(2Pi I)^#)/.wd[bb_,aa___]:>Re[aa//Times]Im[bb]/.{Im[aa_ bb_]:>Re[aa]Im[bb]+Re[bb]Im[aa],Re[cc_ dd_]:>Re[cc]Re[dd]-Im[cc]Im[dd]})&/@par];
ComplexPer[mypg[numseq__]]:=Block[{weight=PolygonWeight[mypg[numseq]],par},par=Flatten[Permutations/@IntegerPartitions[weight],1];(Power[-1,If[#[[1]]==0,0,Length[#]-1]]Total[(2Pi)^weight PolygonALiCoproduct[#,mypg[numseq]]]/.wd[sym__]:>wd@@({sym}/(2Pi I)^#)/.wd[bb_,aa___]:>Re[aa//Times]bb//.{Im[aa_ bb_]:>Re[aa]Im[bb]+Re[bb]Im[aa],Re[cc_ dd_]:>Re[cc]Re[dd]-Im[cc]Im[dd]})&/@par]; (* no shift *)
ComplexPernew[mypg[numseq__]]:=Block[{weight=PolygonWeight[mypg[numseq]],par},par=Flatten[Permutations/@IntegerPartitions[weight],1];((-1)^If[#1[[1]]==0,0,Length[#1]-1] Total[(2 \[Pi])^weight PolygonALiCoproduct[#1,mypg[numseq]]]/. wd[sym__]:>wd@@((1/(2*\[Pi]*I)^#1)({sym}-If[First[#]==1,Join[{-Pi I/2},Table[0,Length[{sym}]-1]],Table[0,Length[{sym}]]]))/. wd[bb_,aa___]:>Re[Times[aa]] bb//. {Im[aa_ bb_]:>Re[aa] Im[bb]+Re[bb] Im[aa],Re[cc_ dd_]:>Re[cc] Re[dd]-Im[cc] Im[dd]}&)/@par] (* trivial shift *)

(* ================= 8. coproducts for li / ali / IH ================= *)
SubLiabSeries[parentxseries_,zerolistofparent_,subxnumseries_]/;(Length[parentxseries]>=Max[subxnumseries]>=Length[subxnumseries]>=3)&&(First[parentxseries]===0)&&(subxnumseries[[1]]===1)&&(parentxseries[[subxnumseries[[2]]]]=!=0)&&(parentxseries[[Last[subxnumseries]]]=!=0)&&AllTrue[parentxseries[[zerolistofparent]]//Flatten,#===0&]:=Block[{nzlist=Complement[subxnumseries,zerolistofparent],nzlistlen,nzpos},nzlistlen=Length[nzlist];Table[{parentxseries[[nzlist[[nzpos+1]]]]/parentxseries[[nzlist[[nzpos]]]],Position[subxnumseries,nzlist[[nzpos+1]]][[1,1]]-Position[subxnumseries,nzlist[[nzpos]]][[1,1]]},{nzpos,Length[nzlist]-1}]]; (* finding the Subscript[x, I] series in and above (3.5) of Rudenko's paper. *)


DeltaHF[ab[]]:=wd[1,1];
DeltaHF[ab[abseq__]]:=Block[{xlist=FoldList[Times,1,First/@{abseq}],ablen=Length[{abseq}],pglen=Total[Last/@{abseq}]+2,nzlist=Accumulate[Prepend[Last/@{abseq},2]],x0list,subpgsets,subpg},x0list=Fold[Insert[#1,Sequence@@#2]&,Table[0,Last[nzlist]-ablen-1],List[xlist,nzlist]//Transpose];subpgsets=FindSubOddokPolygon[mypg@@Range[2,pglen]];Sum[If[subpg==={},wd[Times@@(IH@@x0list[[#]]&/@subpg),ab[abseq]],Block[{vertlb=Complement[Range[pglen],Map[Delete[#,{{1},{-1}}]&,subpg,{1}]//Flatten],nzvertlb,verti,vertj},nzvertlb=Intersection[nzlist,vertlb];(-1)^(ablen-Length[nzvertlb]+1) wd[Times@@(IH@@x0list[[#]]&/@subpg),{Table[x0list[[nzvertlb[[verti+1]]]]/x0list[[nzvertlb[[verti]]]],{verti,Length[nzvertlb]-1}],Table[Position[vertlb,nzvertlb[[vertj+1]]][[1,1]]-Position[vertlb,nzvertlb[[vertj]]][[1,1]],{vertj,Length[nzvertlb]-1}]}//Transpose//ab@@#&]]],{subpg,subpgsets}]];(* eq.(3.5) of Rudenko's paper: the HF coproduct of weighted alphabets *)


DeltaHH[ali[abseq__]]:=Block[{len=Length[{abseq}],ss},Sum[DeltaHF[ab@@({abseq}[[ss+1;;len]])]/.wd[wd1_,wd2_]:>wd[(ab@@({abseq}[[1;;ss]]))*wd1/.ab->ali,wd2/.ab->ali],{ss,0,len}]] (* Proposition 6.18 of Rudenko's paper: the HH coproduct of weighted alphabets associated with ALi *)


DeltaHs[{weight_},ali[abseq__]]/;PolylogWeight[ali[abseq]]==weight:=wd[ali[abseq]];
DeltaHs[weightlist_,ali[abseq__]]/;(PolylogWeight[ali[abseq]]==Total[weightlist])&&(Length[weightlist]>=2)&&AllTrue[weightlist,#>0&]:=Block[{xlist=FoldList[Times,1,First/@{abseq}],ablen=Length[{abseq}],pglen=Total[Last/@{abseq}]+2,nzlist=Accumulate[Prepend[Last/@{abseq},2]],x0list,lastwei=First[weightlist],prewei=Delete[weightlist,1],subpgsizeset=Flatten[Permutations/@IntegerPartitions[First[weightlist]],1],subpgset,subpgs,word1},x0list=Fold[Insert[#1,Sequence@@#2]&,Table[0,Last[nzlist]-ablen-1],List[xlist,nzlist]//Transpose];subpgset=Select[FindSubOddokPolygon[#+2,mypg@@Range[1,pglen]]&/@subpgsizeset//Flatten[#,1]&,If[First[#[[1]]]==1,MemberQ[nzlist,Last[#[[1]]]],True]&];Sum[Joinab[wd[If[subpgs[[1,1]]===1,ali@@SubLiabSeries[x0list,Complement[Range[pglen],nzlist],subpgs[[1]]],IH@@x0list[[subpgs[[1]]]]]*(Times@@(IH@@x0list[[#]]&/@Delete[subpgs,1]))],#]&/@MonomialList[(-1)^(ablen-Length[#])DeltaHs[prewei,(ali@@#)]&[SubLiabSeries[x0list,Complement[Range[pglen],nzlist],Complement[Range[pglen],Flatten[Map[Delete[#,{{1},{-1}}]&,subpgs,1]]]]]]//Total,{subpgs,subpgset}]];  (* Proposition 6.18 of Rudenko's paper: coproduct of ALi functions order by order *)


(* ::Subsubsection:: *)
(*symbol alphabets and coproducts for general multiple polylogarithms:*)


(* Li functions *)


DeltaHH[li[abseq__]]:=Block[{len=Length[{abseq}],ss},Sum[DeltaHF[ab@@({abseq}[[ss+1;;len]])]/.wd[wd1_,wd2_]:>wd[(ab@@({abseq}[[1;;ss]]))*wd1/.ab->li,wd2/.ab->li],{ss,0,len}]] (* eq.(3.20) of Rudenko paper: the HH coproduct of Li functions *)


DeltaHs[{weight_},li[abseq__]]/;PolylogWeight[li[abseq]]==weight:=wd[li[abseq]];
DeltaHs[weightlist_,li[abseq__]]/;(PolylogWeight[li[abseq]]==Total[weightlist])&&(Length[weightlist]>=2)&&AllTrue[weightlist,#>0&]:=Block[{xlist=FoldList[Times,1,First/@{abseq}],ablen=Length[{abseq}],pglen=Total[Last/@{abseq}]+2,nzlist=Accumulate[Prepend[Last/@{abseq},2]],x0list,lastwei=First[weightlist],prewei=Delete[weightlist,1],subpgsizeset=Flatten[Permutations/@IntegerPartitions[First[weightlist]],1],subpgset,subpgs,word1},x0list=Fold[Insert[#1,Sequence@@#2]&,Table[0,Last[nzlist]-ablen-1],List[xlist,nzlist]//Transpose];subpgset=Select[FindSubOddokPolygon[#+2,mypg@@Range[1,pglen]]&/@subpgsizeset//Flatten[#,1]&,If[First[#[[1]]]==1,MemberQ[nzlist,Last[#[[1]]]],True]&];Sum[Joinab[wd[If[subpgs[[1,1]]===1,li@@SubLiabSeries[x0list,Complement[Range[pglen],nzlist],subpgs[[1]]],IH@@x0list[[subpgs[[1]]]]]*(Times@@(IH@@x0list[[#]]&/@Delete[subpgs,1]))],#]&/@MonomialList[(-1)^(ablen-Length[#])DeltaHs[prewei,(li@@#)]&[SubLiabSeries[x0list,Complement[Range[pglen],nzlist],Complement[Range[pglen],Flatten[Map[Delete[#,{{1},{-1}}]&,subpgs,1]]]]]]//Total,{subpgs,subpgset}]];  (* eq.(3.20) of Rudenko paper: coproduct of Li functions order by order *)


(* Goncharov I functions: *)


(* DELETED 2026-07-28 on request:  IH[x1_,x2_]:=1;
   Setting the weight-0 iterated integral to 1 must NOT happen automatically --
   it collides with the way IH[...] is used as an inert head elsewhere. *)


DeltaHH[IH[xseq__]]:=Block[{subpgsets,subpg,xlen=Length[{xseq}]},subpgsets=FindSubOddokPolygon[mypg@@Range[1,xlen]];Sum[If[subpg==={},wd[1,IH[xseq]],Block[{vertlb=Complement[Range[xlen],Map[Delete[#,{{1},{-1}}]&,subpg,{1}]//Flatten]},wd[Times@@(IH@@{xseq}[[#]]&/@subpg),IH@@{xseq}[[vertlb]]]]],{subpg,subpgsets}]]; (* equation (2.5) of Rudenko's paper: the HH coproduct of Goncharov function *)


DeltaHs[{weight_},IH[xseq__]]/;PolylogWeight[IH[xseq]]==weight:=wd[IH[xseq]];
DeltaHs[weightlist_,IH[xseq__]]/;(PolylogWeight[IH[xseq]]==Total[weightlist])&&(Length[weightlist]>=2)&&AllTrue[weightlist,#>0&]:=Block[{subpgset,pglen=Length[{xseq}],subpgsizeset=Flatten[Permutations/@IntegerPartitions[First[weightlist]],1],subpgs,prewei=Delete[weightlist,1]},subpgset=FindSubOddokPolygon[#+2,mypg@@Range[1,pglen]]&/@subpgsizeset//Flatten[#,1]&;Sum[Joinab[wd[Times@@(IH@@{xseq}[[#]]&/@subpgs)],#]&/@MonomialList[DeltaHs[prewei,IH@@{xseq}[[Complement[Range[pglen],Flatten[Map[Delete[#,{{1},{-1}}]&,subpgs,1]]]]]]]//Total,{subpgs,subpgset}]] (* equation (2.5) of Rudenko's paper: coproduct of Goncharov function order by order *)


IH2Li[IH[xseries__]]/;{xseries}[[1]]===0:=If[Last[{xseries}]===0,0,Block[{len=Length[{xseries}],abseries},abseries=SubLiabSeries[{xseries},Position[{xseries},0]//Flatten,Range[len]];(-1)^Length[abseries] li@@abseries]];
IH2Li[IH[xseries__]]/;{xseries}[[1]]=!=0:=IH2Li[IH@@({xseries}-{xseries}[[1]])];
IH2Li[i_Integer IH[xseries__]]:=i IH2Li[IH[xseries]];

(* Li0ToG / Li1ToG: need LiToG from symbology.m.
   Generalized Li[n0;m1,...,md] has exactly one more index than variables and
   receives the trailing-zero conversion below.  Ordinary Li has equal numbers
   of indices and variables and is passed directly to LiToG.  All other arities
   stay inert.  Both converters preserve G[{a1,...,an}, endpoint]. *)
Li0ToG[func_] :=
 func /. Subscript[Li, seq___][vv___] /;
     Length[{seq}] === Length[{vv}] :> LiToG[Li[{seq}, {vv}]] /.
  Subscript[Li, a_, seq___][vv___] /;
    Length[{seq}] === Length[{vv}] :>
   (LiToG[Li[{seq}, {vv}]] /.
     G[vvv_List, end_] :> G[Join[vvv, Table[0, a]], end])
Li1ToG[func_] :=
 func /. Subscript[Li, seq___][vv___] /;
     Length[{seq}] === Length[{vv}] :> LiToG[Li[{seq}, {vv}]] /.
  Subscript[Li, a_, seq___][vv___] /;
    Length[{seq}] === Length[{vv}] :>
   (LiToG[Li[{seq}, {vv}]] /.
     G[vvv_List, end_] :> G[Join[vvv/end, Table[0, a]], 1])

(* ================= 9. cluster (quadrangular) polylogarithms ================= *)
QLi[n_Integer,mypg_]/;And@@OddQ/@(mypg[[2;;]]-mypg[[;;-2]]):=Li[Tarb@@mypg]/.Subscript[Li, ns__][cs__]:>Subscript[Li, n,ns][cs]
QLip[n_Integer,mypg_]/;And@@OddQ/@(mypg[[2;;]]-mypg[[;;-2]]):=Li[Tarp@@mypg]/.Subscript[Li, ns__][cs__]:>Subscript[Li, n,ns][cs]/.Liflip;


QeLi[M_,chain_]:=QLi[M,Range[0,Length[chain]-1]]/.Thread[Thread[Subscript[z,Range[0,Length[chain]-1]]]->Thread[Subscript[z,chain]]];
QeLi[M_,chain_,sub_List,mode_String:"Inside"]/;sub=!={}:=Module[{std=Range[0,Length[chain]-1]},
  QLiOn[M,std,sub/.Thread[chain->std],mode]/.Thread[(Subscript[z,#]&/@std)->(Subscript[z,#]&/@chain)]];
QoLi[M_,chain_]:=QLi[M,Range[Length[chain]]]/.Thread[Thread[Subscript[z,Range[Length[chain]]]]->Thread[Subscript[z,chain]]];
QoLi[M_,chain_,sub_List,mode_String:"Inside"]/;sub=!={}:=Module[{std=Range[Length[chain]]},
  QLiOn[M,std,sub/.Thread[chain->std],mode]/.Thread[(Subscript[z,#]&/@std)->(Subscript[z,#]&/@chain)]];
QfLi[M_,chain_]/;And@@OddQ/@(chain[[2;;]]-chain[[;;-2]]):=QLi[M,chain-1]/.Thread[Thread[Subscript[z,chain-1]]->Thread[Subscript[z,chain]]];


QeLip[M_,chain_]:=QLip[M,Range[0,Length[chain]-1]]/.Thread[Thread[Subscript[z,Range[0,Length[chain]-1]]]->Thread[Subscript[z,chain]]];
QeLip[M_,chain_,sub_List,mode_String:"Inside"]/;sub=!={}:=Module[{std=Range[0,Length[chain]-1]},
  QLipOn[M,std,sub/.Thread[chain->std],mode]/.Thread[(Subscript[z,#]&/@std)->(Subscript[z,#]&/@chain)]];
QoLip[M_,chain_]:=QLip[M,Range[Length[chain]]]/.Thread[Thread[Subscript[z,Range[Length[chain]]]]->Thread[Subscript[z,chain]]];
QoLip[M_,chain_,sub_List,mode_String:"Inside"]/;sub=!={}:=Module[{std=Range[Length[chain]]},
  QLipOn[M,std,sub/.Thread[chain->std],mode]/.Thread[(Subscript[z,#]&/@std)->(Subscript[z,#]&/@chain)]];


QLiq[n_Integer,mypg_]/;And@@OddQ/@(mypg[[2;;]]-mypg[[;;-2]]):=Li[Tarbinq@@mypg]/.Subscript[Li, ns__][cs__]:>Subscript[Li, n,ns][cs]


QeLiq[M_,chain_]:=QLiq[M,Range[0,Length[chain]-1]]/.q[seq__]:>q@@({seq}/.Thread[Range[0,Length[chain]-1]->chain]);
QoLiq[M_,chain_]:=QLiq[M,Range[Length[chain]]]/.q[seq__]:>q@@({seq}/.Thread[Range[Length[chain]]->chain]);
QfLiq[M_,chain_]/;And@@OddQ/@(chain[[2;;]]-chain[[;;-2]]):=QLiq[M,chain-1]/.q[a_,b_,c_,d_]:>q[a+1,b+1,c+1,d+1];


(* ---- restricted arborification (contribution of ONE quadrangulation) ----
   TarbOnGen[base,P,Q] is the piece of the arborification base@@P that comes from
   the single quadrangulation Q (a list of quads).  Summed over all Q in
   BquadDiss[P] it reproduces base@@P exactly (checked for Tarb and Tarbinq up to
   the 10-gon).  base is Tarb (z cross-ratios) or Tarbinq (formal q).            *)

TarbOnGen[base_, P_List, Q_List] /; Length[P] <= 2 := Sequence[];
TarbOnGen[base_, P_List, Q_List] /; Length[P] === 4 := base @@ P;
TarbOnGen[base_, P_List, Q_List] /; Length[P] >= 6 :=
  Module[{fir = First[P], las = Last[P], len = Length[P], root, pos, i, j},
   root = SelectFirst[Q, ContainsAll[#, {fir, las}] &];
   If[MissingQ[root], Return[0]];
   pos = Sort[Flatten[(FirstPosition[P, #, {0}, {1}] &) /@ root]];
   i = pos[[2]]; j = pos[[3]];
   Total[(#[base @@ P[[{1, i, j, len}]],
       Qshab[TarbOnGen[base, P[[1 ;; i]], Select[Q, ContainsAll[P[[1 ;; i]], #] &]],
        Qshab[TarbOnGen[base, P[[i ;; j]], Select[Q, ContainsAll[P[[i ;; j]], #] &]],
         TarbOnGen[base, P[[j ;; len]], Select[Q, ContainsAll[P[[j ;; len]], #] &]]]]] &) /@
     If[EvenQ[fir], {Joinab}, {Joinab, Dotab}]]];

(* keep only the quadrangulations matching (sub, mode); empty sub -> full arbor. *)
TarbOn[base_, P_List] := base @@ P;
TarbOn[base_, P_List, {}, ___] := base @@ P;
TarbOn[base_, P_List, sub_List, mode_String : "Inside"] :=
  Total[TarbOnGen[base, P, #] & /@ Select[BquadDiss[P], DissMatchQ[#, sub, mode] &]];

(* ---- tag partition of the arborification ----
   Tarbinq@@P is a sum over full quadrangulations: every ab-term's quadrangulation
   is recorded by the quads appearing as its q-factors (a weight-m letter
   q_{c1}*...*q_{cm} merges the quads c1..cm but still names them all).  QLiTag[t]
   reads that quadrangulation off; QLiTagFilter keeps the terms whose
   quadrangulation matches (sub, mode) via DissMatchQ.  Summed over full
   quadrangulations this reproduces the whole arborification exactly -- no signs,
   each term belongs to exactly one quadrangulation. *)

QLiTagQuads[cr_] := Sort /@ Cases[cr, q[x__] :> {x}, {0, Infinity}];
QLiTag[t_] := Module[{a = FirstCase[t, _ab, t, {0, Infinity}]},
   Sort[Join @@ (QLiTagQuads[First[#]] & /@ (List @@ a))]];
QLiTagFilter[arb_, sub_List, mode_String] :=
  Total[Select[If[Head[arb] === Plus, List @@ arb, {arb}],
     DissMatchQ[QLiTag[#], sub, mode] &]];

(* QLiOn[n,mypg,sub,mode] = the part of QLi[n,mypg] belonging to the
   quadrangulations that match (sub,mode).  When sub is a full quadrangulation
   this is exactly that quadrangulation's term; when sub is one quad (or several)
   it is the sum of all full quadrangulations containing it.  Output in z. *)
QLiOn[n_Integer, mypg_List] := QLi[n, mypg];
QLiOn[n_Integer, mypg_List, {}, ___] := QLi[n, mypg];
QLiOn[n_Integer, mypg_List, sub_List, mode_String : "Inside"] :=
  Li[QLiTagFilter[Tarbinq @@ mypg, sub, mode]] /.
     Subscript[Li, ns__][cs__] :> Subscript[Li, n, ns][cs] /. q2cr0;



QLisym[Nweight_Integer,mypglist_List]/;EvenQ[Length[mypglist]]&&Nweight>=(Length[mypglist]-2)/2:=Block[{nn=Length[mypglist]/2-1},Sum[(-1)^(nn-Length[subevenpg]-1)QQLi[Nweight-Length[subevenpg]+1,mypglist[[(Join[2subevenpg,2subevenpg+1]//Sort)+1]]],{subevenpg,Select[Subsets[Range[0,nn]],Length[#]>=2&]}]];
QLiid[nnnweight_Integer,NN_Integer]/;NN>=nnnweight+2:=Sum[(-1)^(Total[evensubpglist]+Length[evensubpglist]/2)*QQLisym[nnnweight,evensubpglist],{evensubpglist,Select[Subsets[Range[0,NN]],(Length[#]>=4&&EvenQ[Length@#])&]}];
QLiid[nnnweight_Integer,NNlist_List]/;Length[NNlist]>=nnnweight+3:=QLiid[nnnweight,Length[NNlist]-1]/.QQLisym[ww_,ll_]:>QQLisym[ww,ll/.Thread[Range[0,Length[NNlist]-1]->NNlist]];


Li2I[Subscript[Li, ns__][cs__]]/;Length[{ns}]-Length[{cs}]==1:=Block[{csl=Length[{cs}],nsl=Length[{ns}],cschain=Join[{0},Table[Product[{cs}[[i]],{i,1,j}],{j,0,Length[{cs}]}]],nschain=Table[Table[0,If[i==1,{ns}[[i]],{ns}[[i]]-1]],{i,1,Length[{ns}]}]},(-1)^csl IH@@Flatten[Riffle[cschain,nschain]]];
Li2I[Subscript[Li, ns__][cs__]]/;Length[{ns}]-Length[{cs}]==0:=Li2I[Subscript[Li, 0,ns][cs]];


QLicount[sitem_Integer,weightn_Integer]:=If[weightn==1,Binomial[sitem,4],Sum[Binomial[sitem-1,ii],{ii,3,weightn+1}]];


ClearAll[QLiB];
QLiB[mypg_List]/;Length[mypg]>1/;EvenQ[Length[mypg]/2]:=Li[TarbB@@mypg];

ClearAll[QLipB];
QLipB[mypg_List]/;Length[mypg]>1/;EvenQ[Length[mypg]/2]:=
  Li[TarpB@@mypg];
QLipB[n_Integer]:=Li[TarpB[n]];


(* ================= 10. M_{0,n+2} <-> orthoscheme coordinates ================= *)
Ort2Mo[i_Integer,j_Integer,n_Integer]/;(0<i<n+1)&&(0<j<n+1):=If[i<=j,(Subscript[z, 0]-Subscript[z, i])(Subscript[z, j]-Subscript[z, n+1])(Subscript[z, n+1]-Subscript[z, 0]),Ort2Mo[j,i,n]];
Ort2Cur[i_Integer,j_Integer,n_Integer]/;(0<i<n+1)&&(0<j<n+1):=Subscript[Gr, i]/Subscript[Gr, j];
Mo2Cur[mon_,n_Integer]:=mon//.{(Subscript[z, b_]-Subscript[z, a_]):>If[(0<a<n+1)&&(0<b<n+1),(Subscript[z, 0]-Subscript[z, n+1])(Subscript[Gr, a]^2-Subscript[Gr, b]^2)/(Subscript[Gr, a] Subscript[Gr, b]),If[b==0&&0<a<n+1,(Subscript[z, 0]-Subscript[z, n+1])Subscript[Gr, a],If[a==n+1&&0<b<n+1,(Subscript[z, 0]-Subscript[z, n+1])/Subscript[Gr, b],Subscript[z, b]-Subscript[z, a]]]]}; (* Subscript[Gr,a]/Subscript[Gr,b] <-> Subscript[Q,a,b]/Sqrt[Subscript[Q,a,a] Subscript[Q,b,b]], and Subscript[Gr,a]^2/Subscript[Gr,b]^2 <-> Subscript[Q,a,b]^2/(Subscript[Q,a,a] Subscript[Q,b,b]) for 0<a<b<n+1. *)

(* ================= 11. orthoscheme dissection ================= *)
OrthoQ[mat_]:=SymmetricMatrixQ[mat]&&Block[{len=Length[mat]},And@@Flatten[Table[Factor[mat[[i,j]]mat[[j,k]]]===Factor[mat[[j,j]]mat[[i,k]]],{i,len},{j,i+1,len},{k,j+1,len}]]];
DoubAsymQ[mat_]:=OrthoQ[mat]&&mat[[1,1]]==0&&Last[Last[mat]]==0;
DihedralAnglesCos[mat_]:=Block[{inv=Inverse[mat],len=Length[mat]},Table[inv[[i,j]]/Sqrt[inv[[i,i]]inv[[j,j]]],{i,len},{j,i+1,len}]//Flatten];
IsSphericalSimplex[mat_]:=SymmetricMatrixQ[mat]&&AllTrue[Flatten[Table[mat[[i,j]]^2/(mat[[i,i]]mat[[j,j]]),{i,Length[mat]},{j,Length[mat]}]],0<=#<=1&]&&AllTrue[DihedralAnglesCos[mat],-1<=#<=1&];
DihedralAngles[mat_]:=ArcCos/@DihedralAnglesCos[mat];
IsIdealSimplex[mat_]:=AllTrue[Diagonal[mat],#==0&];


FindFoot[mat_]/;SymmetricMatrixQ[mat]:=Block[{len=Length@mat,qfoot,matft},qfoot=Table[If[i==len,Subscript[Q, ft,i],Subscript[Q, i,ft]],{i,len}]/.Subscript[Q, j_,ft]:>zz mat[[j,len]];matft=Join[mat[[Range[len-1]]],{qfoot}];{qfoot,zz Subscript[Q, ft,len]}/.Solve[Table[Total[matft[[#,ii]]&/@Table[Range[len-1]/.iii->len,{iii,len-1}]//Det/@#&]==Det[matft[[Range[len-1],ii]]],{ii,Subsets[Range[len],{len-1}]}],{zz,Subscript[Q, ft,len]}]]//First;(* gives the list qfoot and Gram elements Subscript[Q, ft,ft] *)


OrthoDsec[Vol[mat_],i_Integer]:=OrthoDsec[sgn[1]Vol[mat],i];
OrthoDsec[sgn[fac_]Vol[mat_],1]/;SymmetricMatrixQ[mat]:=Block[{foot,len=Length[mat]},foot=FindFoot[mat];(Vol/@Table[Insert[Insert[mat,foot[[1]],-2]//Transpose,Insert[Sequence@@foot,-2],-2][[i,i]],{i,Complement[Range[len+1],{#}]&/@Range[len-1]}])*Table[sgn[fac*(Transpose[Insert[mat[[Delete[Range[len-1],i]]],foot[[1]],i]][[Range[len-1]]]//Det)/(mat[[Range[len-1],Range[len-1]]]//Det)],{i,len-1}]];


OrthoDSing[sgn[fac_]Vol[singmat_],i_Integer]/;(i>1):=Block[{len=Length@singmat,bas,foot,foota1},bas=singmat[[Join[Range[len-i],{len}],Join[Range[len-i],{len}]]];foot=FindFoot[bas];foota1=Fold[Insert[#1,#2,-2]&,foot[[1]],Table[singmat[[j,j]]foot[[1,len-i+1]]/singmat[[j,len]],{j,len-i+1,len-1}]];(Vol/@Table[Delete[#,ii]&/@Delete[Insert[Insert[singmat,foota1,len-i+1]//Transpose,Insert[foota1,foot[[2]],len-i+1],len-i+1],ii],{ii,Range[len-i]}])*Table[sgn[fac*(Transpose[Insert[singmat[[Delete[Range[len-i],ii],Join[Range[len-i],{len}]]],foot[[1]],ii]][[Range[len-i]]]//Det)/(singmat[[Range[len-i],Range[len-i]]]//Det)],{ii,len-i}]];
OrthoDsec[sgn[fac_]Vol[mat_],i_Integer]/;i>1:=Flatten[OrthoDSing[#,i]&/@OrthoDsec[sgn[fac]Vol[mat],i-1],1];
OrthoDsec[Vol[mat_]]:=OrthoDsec[Vol[mat],Length[mat]-2];
OrthoDsecVol[Vol[mat_]]:=OrthoDsec[Vol[mat]]/.sgn[__]:>1/.Vol->Join;
OrthoDsecSgn[Vol[mat_]]:=OrthoDsec[Vol[mat]]/.Vol[__]:>1;


Cr2Ort[sgn[fac_]Vol[ortmat_],funx_,n_Integer]/;Dimensions[ortmat]=={n,n}:=sgn[fac]Mo2Cur[funx,n]//.Power[Subscript[Gr,i_],m_]:>If[EvenQ[m],(Last[ortmat][[i]]^2/ortmat[[i,i]])^(m/2),Subscript[Gr,i]^m]//.Subscript[q,i_,j_]:>ortmat[[i,j]];
Cr2Ort[Vol[ortmat_],funx_,n_Integer]/;Dimensions[ortmat]=={n,n}:=Mo2Cur[funx,n]//.Power[Subscript[Gr,i_],m_]:>If[EvenQ[m],(Last[ortmat][[i]]^2/ortmat[[i,i]])^(m/2),Subscript[Gr,i]^m]//.Subscript[q,i_,j_]:>ortmat[[i,j]];
Cr2Ort[ortmat_,funx_,n_Integer]/;Dimensions[ortmat]=={n,n}:=Cr2Ort[Vol[ortmat],funx,n];


(* ================= 12. tidier symbol output ================= *)

(* SymbolFactorQ replaces PolyLogTools' SymbolFactor: split every tensor entry
   multiplicatively, CiTi[..,a b,..] -> CiTi[..,a,..] + CiTi[..,b,..],
   CiTi[..,a^n,..] -> n CiTi[..,a,..], and drop entries that are pure numbers. *)
SymbolFactorQ[expr_] := Expand[expr //. CiTi[e___] :> Module[{ent = {e}, k, fl},
    k = FirstPosition[ent, x_ /; ! MatchQ[Factor[x], _Symbol] &&
         Length[DeleteCases[FactorList[Together[x]], {_?NumericQ, _}]] =!= 1, Missing[], {1}];
    If[MissingQ[k], CiTi @@ ent,
     fl = DeleteCases[FactorList[Together[ent[[First[k]]]]], {_?NumericQ, _}];
     If[fl === {}, 0,
      Total[(#[[2]] CiTi @@ ReplacePart[ent, First[k] -> #[[1]]] &) /@ fl]]]]];

nice[poly__]/;MonomialList[poly]=!={poly}:=Total[nice/@MonomialList[poly]];
nice[i_Integer]:=i;
nice[CiTi[m__]]:=(Times[Sequence@@#2]CiTi[Sequence@@#1]&[##])&@@Transpose[norm/@{m}];
nice[i_Integer CiTi[m__]]:=i(Times[Sequence@@#2]CiTi[Sequence@@#1]&[##])&@@Transpose[norm/@{m}];
norm[expr_]:=Block[{var=Variables[expr],len,fae=Factor[expr]},len=Length[var];If[IntegerQ[Denominator[fae]]||((Abs[Re[#]]>=1||Im[#]>0)&[fae/.Table[var[[i]]->Prime[i+5],{i,len}]]),{fae,1},{Factor[Denominator[fae]/Numerator[fae]],-1}]];
nicest[wordpoly__]:=FixedPoint[nice[SymbolFactorQ[#]]&,wordpoly];

(* ================= 13. classical-polylogarithm rewrites, branch cuts ================= *)
CL[Subscript[Li, 1,1][x_,y_]]:=Subscript[Li, 2][(x y-y)/(1-y)]-Subscript[Li, 2][y/(y-1)]-Subscript[Li, 2][x y];
CL[Subscript[Li, 1,1,1][z_,y_,x_]]:=Subscript[Li, 2,1][z (1-y)/(z-1),1/(1-y)]-Subscript[Li, 2,1][z (1-y)/(z-1),(1-x y)/(1-y)]-log[1-x] Subscript[Li, 2][z/(z-1)]-log[1-z]Subscript[Li, 1,1][y,x]
CL[Subscript[Li, 2,1][x_,y_]]:=Subscript[Li, 3][1-x y]+Subscript[Li, 3][1-y]-Subscript[Li, 3][(1-y)/(1-x y)]-Subscript[Li, 3][x]+Subscript[Li, 3][(x-x y)/(1-x y)]-Subscript[Li, 3][1]-log[1-x y](Subscript[Li, 2][1]+Subscript[Li, 2][1-y])-log[(1-y)/(1-x y)]Subscript[Li, 2][x]+1/2log[x]log[1-x y]^2;
CL[Subscript[Li, 1,2][x_,y_]]:=Subscript[Li, 1][x]Subscript[Li, 2][y]-Subscript[Li, 2,1][y,x]-Subscript[Li, 3][x y];
CL[f_Plus]:=CL/@f;


(* ::Subsection:: *)
(*deforming the branch cut:*)


expandlog[exp_]:=Block[{a,b,x,i},exp/. {log[a_]:>Total[(#1[[2]] log[#1[[1]]]&)/@FactorList[a]]}/. {log[i_Integer]->log[Abs[i]],log[a_^x_]:>x log[a]}]/. log[1]->0//. log[a_]:>Block[{var=Variables[a]},If[(a/. Table[var[[i]]->i/(Length[var]+2),{i,Length[var]}])>0,log[a],log[-a]]];



(* ================================================================
   B-type cluster polylogarithms on the folded 4n-gon
   ================================================================
   Companion to the A-type Tarb/Tarbinq above, for section 4 "Algebra of
   cross-ratios" of the loops draft.

   Labels: physical 1..2n and barred bar[i]; the folded polygon is the 4n-gon
   (1,...,2n,bar 1,...,bar 2n) with the Theta involution i <-> bar i.

   CONVENTIONS
     * multiple Li's are written in the symbology.m two-list form
         Li[{m1,...,md},{x1,...,xd}],   weight = Sum m_i,  depth = d,
       which is the PolyLogTools / chain-paper (2605.06542) ordering -- NOT
       Rudenko's and NOT NumPolyLog's.  Convert with symbology`LiToG /
       LiToPolyLog.
     * the B-type QLi of a 4n-gon has weight n, full stop.  There is no extra
       Rudenko index: QLiB takes the polygon and nothing else.
*)

(* ---------------- folded minors and cross-ratios ---------------- *)

(* Delta on the folded polygon, eq (1.11):
     D_{a,abar} = 1,  D_{a,bbar} = D_{abar,b} = +-(1 - D_{a,b}),
     D_{abar,bbar} = D_{a,b},   and plain pairs are z-differences.        *)

dd[a_, b_] := ddRaw[a, b] //. {
    ddRaw[bar[x_], bar[y_]] :> ddRaw[x, y],
    ddRaw[bar[x_], y_] /; x =!= y :> Signature[{x, y}] (1 - ddRaw @@ Sort[{x, y}]),
    ddRaw[x_, bar[y_]] /; x =!= y :> Signature[{x, y}] (1 - ddRaw @@ Sort[{x, y}]),
    ddRaw[x_, bar[x_]] :> 1, ddRaw[bar[x_], x_] :> 1} /.
   ddRaw[x_, y_] :> Subscript[z, y] - Subscript[z, x];

(* crq extended to barred (folded) labels.  Same shape as the A-type crq above
   -- numerator on the odd-position pairs, denominator on the even ones times
   the closing minor -- so the two agree on plain labels.  PrependTo is used so
   that this branch is tried before the generic crq[list___].                 *)

crqFolded[L_List] := Module[{m = Length[L]},
   Product[dd[L[[i]], L[[i + 1]]], {i, 1, m - 1, 2}]/
    (Product[dd[L[[i]], L[[i + 1]]], {i, 2, m - 2, 2}] dd[L[[1]], L[[m]]])];

If[FreeQ[DownValues[crq], crqFolded],
  PrependTo[DownValues[crq],
    HoldPattern[crq[list___]] /; (EvenQ[Length[{list}]] && ! FreeQ[{list}, bar]) :>
      crqFolded[{list}]];
  PrependTo[DownValues[crq],
    HoldPattern[crq[{list___}]] /; (EvenQ[Length[{list}]] && ! FreeQ[{list}, bar]) :>
      crqFolded[{list}]]];

(* The DRAFT's q_P differs from crq only in the orientation of the closing
   minor, q_P = D_{a1a2}...  / (... D_{a2m,a1}) = -crq, for every length.
   It is q_P -- not crq -- that is a perfect square on a Theta-symmetric
   polygon, so this is the one that appears under the square roots.           *)

qfold[L_List] := -crq[L];

(* the half product: crqh[L]^2 = qfold[L] for Theta-symmetric L.  This branch
   is TL's convention  q^{1/2}_{1,2,1bar,2bar} = -D_{12}/D_{1bar,2},  i.e. it
   already carries YQZ's  sqrt(q_strip) = -sqrt(q_original).                  *)

crqh[L_List] := Module[{m = Length[L]/2, LL = Append[L, First[L]]},
   Product[dd[LL[[i]], LL[[i + 1]]], {i, 1, m - 1, 2}]/
    Product[dd[LL[[i]], LL[[i + 1]]], {i, 2, m, 2}]];

(* ---------------- labels ---------------- *)

BtoInt[n_][bar[i_]] := i + 2 n;
BtoInt[n_][i_Integer] := i;
BtoBar[n_][i_Integer] := If[i > 2 n, bar[i - 2 n], i];
BshiftLab[n_, k_][lab_] := BtoBar[n][Mod[BtoInt[n][lab] + k - 1, 4 n] + 1];
BshiftExpr[expr_, n_, k_] := expr /.
   {bar[i_Integer] :> BshiftLab[n, k][bar[i]],
    i_Integer /; 1 <= i <= 2 n :> BshiftLab[n, k][i]};

BpolyAll[n_] := Join[Range[2 n], bar /@ Range[2 n]];

(* ---------------- strips, windows, dissections ---------------- *)

(* A strip is a Theta-invariant quad {i,j,bar j,bar i}.  Its two complementary
   regions can be dissected into even-gons only when i-j is odd, which leaves
   n^2 strips (n=2: 4; n=3: 9 = 6 thin + 3 thick; n=4: 16; n=5: 25). *)

BstripPairs[n_] := Select[Subsets[Range[2 n], {2}], OddQ[#[[2]] - #[[1]]] &];
BstripQuad[{i_, j_}] := {i, j, bar[j], bar[i]};
BstripGaps[n_, {i_, j_}] := {Table[BtoBar[n][k], {k, i, j}],
   Table[BtoBar[n][k], {k, j, i + 2 n}]};

(* B-windows: a set S of 2w diameters out of 2n whose cyclic gaps are all odd,
   together with its bars -- the Theta-symmetric sub-polygon carrying QLi^B of
   weight w.  w = n is the whole 4n-gon, w = 1 are the strips. *)

BWindowSets[n_, w_] := Select[Subsets[Range[2 n], {2 w}],
   With[{g = Append[Differences[#], First[#] + 2 n - Last[#]]}, And@@OddQ/@g] &];
BWindowPoly[n_, S_List] := Join[BtoBar[n] /@ S, BtoBar[n] /@ (S + 2 n)];
BWindowGaps[n_, S_List] := Module[{SS = Append[S, First[S] + 2 n]},
   Table[Table[BtoBar[n][k], {k, SS[[a]], SS[[a + 1]]}], {a, Length[S]}]];

BevenDiss[v_List] /; OddQ[Length[v]] := {};
BevenDiss[v_List] /; Length[v] <= 2 := {{}};
BevenDiss[v_List] /; EvenQ[Length[v]] && Length[v] >= 4 := BevenDiss[v] =
  Module[{m = Length[v], out = {}},
   Do[With[{pos = Join[{1}, ss, {m}]},
      If[Length[pos] >= 4 &&(And@@OddQ/@Differences[pos]),
       Module[{gapD, combos},
        gapD = Table[BevenDiss[v[[pos[[a]] ;; pos[[a + 1]]]]], {a, Length[pos] - 1}];
        combos = Fold[Flatten[Table[Join[d1, d2], {d1, #1}, {d2, #2}], 1] &, {{}}, gapD];
        out = Join[out, (Prepend[#, v[[pos]]] &) /@ combos]]]],
    {ss, Subsets[Range[2, m - 1]]}];
   out];

BquadDiss[v_List] := Select[BevenDiss[v], AllTrue[#, Length[#] === 4 &] &];

(* ---------------- the B-type arborification ---------------- *)

(* ---- B-type restricted arborification ----
   TarbBTerms[n] lists (quad-set, contribution) over every (strip, gap-
   quadrangulation); it feeds QLiByQuad/QLiBByQuad (the per-quadrangulation
   split of the B-type arborification, checked n = 2, 3). *)

BgapArbOn[n_, gap_List, Qgap_List] :=
  TarbOnGen[Tarbinq, BtoInt[n] /@ gap, Map[BtoInt[n], Qgap, {2}]] /.
   q[a__] :> q @@ (BtoBar[n] /@ {a});

TarbBTerms[n_] := TarbBTerms[n] = Flatten[(Function[pr,
    Module[{gaps = Select[BstripGaps[n, pr], Length[#] >= 4 &], sq = BstripQuad[pr]},
     If[gaps === {}, {{{sq}, ab[{qh @@ sq, 1}]}},
      (Module[{cs = MapThread[BgapArbOn[n, #1, #2] &, {gaps, #}]},
         {Join[{sq}, Flatten[#, 1]], Joinab[ab[{qh @@ sq, 1}], Qshab @@ cs]}] &) /@
       Tuples[BquadDiss /@ gaps]]]] /@ BstripPairs[n]), 1];

(* QQLiB, QQeLi, QQoLi carry NO definitions on purpose: they are the frozen
   twins of QLiB, QeLi, QoLi, so that a whole psi can be assembled, counted and
   inspected without expanding a single polylog.  Thaw with BinertToFun. *)
(* Thawing.  The 2-argument heads are the plain functions; the 4-argument ones
   carry the (sub-polygon, mode) that selected them and thaw to the SAME
   function -- the keys are provenance, they annotate which selection produced
   the term, they do not further restrict the internal arborification of a
   single QLi.  (Restricting that would need the per-quadrangulation split of
   Tarbinq, which is a separate job.) *)
BinertToFun = {QQLiB[P_, s_, md_] :> QLiB[P, s, md], QQLiB[P_, s_] :> QLiB[P, s],
   QQLiB[P_] :> QLiB[P],
   QQeLi[m_, P_, s_, md_] :> QeLi[m, P, s, md], QQeLi[m_, P_, s_] :> QeLi[m, P, s],
   QQeLi[m_, P_] :> QeLi[m, P],
   QQoLi[m_, P_, s_, md_] :> QoLi[m, P, s, md], QQoLi[m_, P_, s_] :> QoLi[m, P, s],
   QQoLi[m_, P_] :> QoLi[m, P],
   QQLiBfun[w_, P_] :> QLiBfun[w, P], QQqRoot[S_] :> qRoot[S]};

(* ---------------- psi_{n-gon} for any n ---------------- *)

(* Updated eq. (3.41): psi_n is a sum over B-windows W and all allowed choices
   of disconnected even-gon parts in one half of the complement.  At n = 3
   this gives 1 full-window term, 6 octagon x quad terms and 27 strip-rooted
   terms (6 strip x hexagon plus 21 strip x quad x quad): 34 total. *)

(* SIGNS.  Read off eq (4.34) [= (3.34) after the renumbering], which is the only
   place the draft writes a complete assembly with product terms:

     -  QLi^B_3(12-gon)                                 k = 0  ->  minus
     +  QLi^B_2(octagon) QLi^A_1(quad)      (6 terms)   k = 1  ->  plus
     +  QLi^B_1(strip)   QLi^A_2(hexagon)   (6 terms)   k = 1  ->  plus
     -  QLi^B_1(strip)   QLi^A_1 QLi^A_1   (21 terms)   k = 2  ->  minus

   i.e. the sign depends only on the NUMBER of A-type pieces, (-1)^(k+1).

   CAVEAT: the v1 2-gon assembly (4.16)-(4.18) instead alternates +,-,+,- within
   its k = 1 family, because there the parity sits in the label ordering rather
   than in a +- superscript; and the v2 2-gon (4.24) = (3.24) alternates too,
   pairing QLi^{B,-,v2} with QLi_1^+ and QLi^{B,+,v2} with QLi_1^-.  So this rule
   reproduces (3.34) but NOT (3.24)/(4.16)-(4.18) -- those two use the +- decorated
   functions, which absorb the alternation.  Re-check against the current draft. *)

BtypeCoeff[n_, w_, S_, pieces_] := (-1)^(Length[pieces] + 1);

BrotOdd[n_, P_List] := RotateLeft[P,
   FirstPosition[P, x_ /; OddQ[BtoInt[n][x]], {1}][[1]] - 1];

BpsiTerms[n_Integer] := BpsiTerms[n] = Flatten[Table[
    Table[Module[{W = BrotOdd[n, BWindowPoly[n, S]],
        gaps = BWindowGaps[n, S]},
      Table[With[{pcs = Flatten[choice, 1]},
        <|"w" -> w, "S" -> S, "window" -> W, "pieces" -> pcs,
          "k" -> Length[pcs], "strip" -> (w === 1),
          "allQuads" -> AllTrue[pcs, Length[#] === 4 &]|>],
       {choice, Tuples[BevenDiss /@ gaps]}]],
     {S, BWindowSets[n, w]}],
    {w, 1, n}], 3];

(* term counts by any key of the term Association; the default grading is "w"
   for the loop (the B-window weight) and "k" for the chain (the number of
   non-root pieces), because those are the gradings the two papers use. *)
BpsiCounts[n_Integer] := BpsiCounts[n, "w"];
BpsiCounts[n_Integer, key_String] := KeySort[Counts[#[key] & /@ BpsiTerms[n]]];
BpsiCounts[n_Integer, poly_List, mode_String : "Inside"] :=
  KeySort[Counts[#["w"] & /@ BpsiSelect[n, poly, mode]]];

(* Keep the cyclic ordering inherited from the complementary region and choose
   QeLi/QoLi from that actual first label.  Rotating every A-piece to an even
   label changes the parity branch and fails the updated product formula already
   at two sites.  The first argument is QeLi/QoLi's own shifted index. *)

BpieceInert[n_, P_List] := Module[{Q = P, w},
   w = Length[P]/2 - 1;
   If[EvenQ[BtoInt[n][First[Q]]], QQeLi[w - Length[Q]/2 + 1, Q],
                                   QQoLi[w - Length[Q]/2 + 1, Q]]];

(* ---- when does a dissection "contain" a polygon? ----
   Three readings, all useful, none of them the obvious one on its own:

     "Exact"    poly is literally one of the pieces.
     "Inside"   poly sits inside some piece: its vertices are vertices of that
                piece and appear there in the same cyclic order.  A piece that
                has NOT been cut along poly still counts, because poly is still
                a sub-polygon of it.  ("Inside" contains "Exact".)
     "Coarser"  "Inside" but NOT "Exact": poly is subsumed by a STRICTLY larger
                piece.  Asking for the quadrangle {2,3,4,5} then picks up the
                term carrying the whole hexagon {1,2,3,4,5,6} and drops the term
                in which that hexagon was actually split into {2,3,4,5} and
                {1,2,5,6}.  This is the default.

   PolyInsideQ implements the cyclic-subpolygon test: read off the positions of
   poly's vertices inside piece, and check that the induced cyclic word is poly
   up to rotation. *)

PolyInsideQ[piece_List, poly_List] := Module[{pos},
   Length[poly] <= Length[piece] && SubsetQ[piece, poly] &&
    (pos = Sort[Flatten[(FirstPosition[piece, #, {0}, {1}] &) /@ poly]];
     FreeQ[pos, 0] &&
      MemberQ[NestList[RotateLeft, piece[[pos]], Length[poly] - 1], poly])];

PolyExactQ[piece_List, poly_List] :=
  Length[piece] === Length[poly] &&
   MemberQ[NestList[RotateLeft, piece, Length[piece] - 1], poly];

(* the subgon key may be one polygon {a,b,c,d} or several {{...},{...}}; in the
   latter case a dissection matches iff EVERY listed polygon matches. *)
subPolys[sub_List] := If[MatchQ[sub, {__List}], sub, {sub}];

DissMatchQ1[pieces_List, poly_List, mode_String] :=
  Switch[mode,
   "Exact",   AnyTrue[pieces, PolyExactQ[#, poly] &],
   "Inside",  AnyTrue[pieces, PolyInsideQ[#, poly] &],
   "Coarser", AnyTrue[pieces, PolyInsideQ[#, poly] && ! PolyExactQ[#, poly] &],
   _, $Failed];

DissMatchQ[pieces_List, sub_List, mode_String : "Inside"] :=
  AllTrue[subPolys[sub], DissMatchQ1[pieces, #, mode] &];

(* ---- selecting a sub-family of terms ----
   Every term of BpsiTerms carries
     "w"        weight of the B-window          "S"     its diameters
     "window"   the B-window polygon            "pieces" the A-type polygons
     "k"        number of A-pieces              "strip"  True when w = 1
     "allQuads" True when every A-piece is a quadrangle
   so a sub-family is just a predicate on that Association.  Examples:

     BpsiSelect[3, #["allQuads"] &]                     only full quadrangulations
     BpsiSelect[3, #["w"] === 1 &]                      only strip-rooted terms
     BpsiSelect[3, BpsiUses[#, {2,3,4,5}] &]            terms containing that quad
     BpsiSelect[3, MemberQ[#["S"], 1] &]                windows through diameter 1

   BpsiPart assembles just that sub-family (inert heads), so the pieces of psi
   can be inspected or matched one family at a time. *)

(* Two calling forms everywhere.  Either give a predicate on the term
   Association, or -- the common case -- give a polygon and (optionally) a mode,
   and the predicate is built for you from DissMatchQ:

       BpsiSelect[3, {2,3,4,5}, "Inside"]
       BpsiSelect[3, {2,3,4,5}]                     mode defaults to "Inside"

   To combine the polygon test with something else, call DissMatchQ yourself --
   it is the one composable primitive, shared by the chain and the loop:

       BpsiSelect[3, DissMatchQ[#["pieces"], {2,3,4,5}, "Inside"] && #["w"] === 1 &]

   The predicate form is pinned to Except[_List | _String] so the two calling
   forms never collide. *)

BpsiSelect[n_Integer, pred : Except[_List | _String]] := Select[BpsiTerms[n], pred];
BpsiSelect[n_Integer, poly_List, mode_String : "Inside"] :=
  BpsiSelect[n, DissMatchQ[#["pieces"], poly, mode] &];
BpsiTerms[n_Integer, pred : Except[_List | _String]] := BpsiSelect[n, pred];
BpsiTerms[n_Integer, poly_List, mode_String : "Inside"] := BpsiSelect[n, poly, mode];

(* one term as an expression, inert.  (It needs n as well as the term, because n
   is not recoverable from the term alone -- the chain's FchainTermValue does not.) *)
BpsiTermValue[n_Integer, t_Association] :=
  BtypeCoeff[n, t["w"], t["S"], t["pieces"]] QQLiB[t["window"]] *
   Times @@ (BpieceInert[n, #] & /@ t["pieces"]);

(* stamped variant: a frozen head is given the (sub-polygon, mode) that selected
   it ONLY when sub could actually sit inside that head's polygon.  A sibling
   factor whose polygon does not admit sub is left full, so stamping never zeroes
   a factor that should survive.  Thawing then restricts each stamped head's
   arborification to the matching quadrangulations. *)
(* the listed polygons that actually sit inside P; a factor is stamped only with
   those (empty -> left bare, so a sibling factor is never zeroed).  A single
   surviving polygon is stored as a plain polygon, several as a list. *)
BsubFor[P_, sub_] := Select[subPolys[sub], Length[#] <= Length[P] && PolyInsideQ[P, #] &];
(* mode "Inside" is the default, so it is dropped from the stamped head:
   QQeLi[m,P] -> QQeLi[m,P,sub]  when mode is Inside, else QQeLi[m,P,sub,mode]. *)
Bstamp[h_[a__, P_], sub_, mode_] := Module[{r = BsubFor[P, sub], sk},
   If[r === {}, h[a, P],
    sk = If[Length[r] === 1, First[r], r];
    If[mode === "Inside", h[a, P, sk], h[a, P, sk, mode]]]];
Bstamp[QQLiB[P_], sub_, mode_] := Module[{r = BsubFor[P, sub], sk},
   If[r === {}, QQLiB[P],
    sk = If[Length[r] === 1, First[r], r];
    If[mode === "Inside", QQLiB[P, sk], QQLiB[P, sk, mode]]]];

BpsiTermValue[n_Integer, t_Association, sub_List, mode_String : "Inside"] :=
  BpsiTermValue[n, t] /. {QQLiB[P_] :> Bstamp[QQLiB[P], sub, mode],
     QQeLi[m_, P_] :> Bstamp[QQeLi[m, P], sub, mode],
     QQoLi[m_, P_] :> Bstamp[QQoLi[m, P], sub, mode]};

BpsiPart[n_Integer] := BpsiInert[n];
BpsiPart[n_Integer, pred : Except[_List | _String]] :=
  Total[BpsiTermValue[n, #] & /@ BpsiSelect[n, pred]];
BpsiPart[n_Integer, poly_List, mode_String : "Inside"] :=
  Total[BpsiTermValue[n, #, poly, mode] & /@ BpsiSelect[n, poly, mode]];

(* psi with every polylog frozen: QQLiB / QQeLi / QQoLi.
   BpsiInert is the name that matches FchainInert; psiNgonInert is kept as a
   synonym because earlier notebooks use it. *)
BpsiInert[n_Integer] := BpsiPart[n, True &];
psiNgonInert[n_Integer] := BpsiInert[n];

(* and the evaluated version *)
psiNgon[n_Integer] := psiNgonInert[n] /. BinertToFun;


(* ---------------- literal n = 2, 3 transcriptions from main.tex ----------------

   Multiple polylogs are written in the symbology.m two-list form
     Li[{m1,...,md},{x1,...,xd}],
   which is the PolyLogTools / chain-paper convention -- the same one the note
   uses.  Convert with symbology`LiToG (symbols) or LiToPolyLog (depth 1).
   Nothing below has been checked numerically.                                *)

(* ---------- weight-one QLi's ---------- *)

QLi1A[L_List]  := Log[1 - qfold[L]];        (* eq (4.23) *)
QLi1B[L_List]  := Log[1 - crqh[L]];         (* eq (4.22); A-type with q -> q^{1/2} *)
QLi1Ap[L_List] := Log[1 - qfold[L]];
QLi1Am[L_List] := -Log[1 - 1/qfold[L]];
QLi1Bp[L_List] := Log[1 - crqh[L]];         (* qli_1^{B,+,v2} *)
QLi1Bm[L_List] := -Log[1 - 1/crqh[L]];      (* qli_1^{B,-,v2} *)

(* ---------- explicit QLi^B from the draft ---------- *)

(* w = 2, eq (eq:QB0hv1), on the octagon (a,b,c,d,abar,bbar,cbar,dbar) *)
QLi2Bat[{a_, b2_, c_, d_}] := With[{B = bar},
   Li[{2}, {crqh[{b2, c, d, B[a], B[b2], B[c], B[d], a}]}]
   - Li[{1, 1}, {crqh[{b2, B[a], B[b2], a}], qfold[{b2, c, d, B[a]}]}]
   + Li[{1, 1}, {crqh[{b2, c, B[b2], B[c]}], qfold[{B[b2], c, d, B[a]}]}]
   - Li[{1, 1}, {crqh[{d, B[c], B[d], c}],   qfold[{B[b2], B[c], d, B[a]}]}]
   + Li[{1, 1}, {crqh[{d, B[a], B[d], a}],   qfold[{b2, c, d, a}]}]];

QLi2Bv1 := QLi2Bat[{1, 2, 3, 4}];

(* w = 2, v2, eq (eq:QB0qhv2) *)
QLi2Bv2 := With[{B = bar},
   Li[{2}, {1/crqh[{1, 2, 3, 4, B[1], B[2], B[3], B[4]}]}]
   - Li[{1, 1}, {1/crqh[{1, 2, B[1], B[2]}], qfold[{2, 3, 4, B[1]}]}]
   + Li[{1, 1}, {crqh[{2, 3, B[2], B[3]}],   1/qfold[{3, 4, B[1], B[2]}]}]
   - Li[{1, 1}, {1/crqh[{3, 4, B[3], B[4]}], qfold[{4, B[1], B[2], B[3]}]}]
   + Li[{1, 1}, {crqh[{4, B[1], B[4], 1}],   1/qfold[{1, 2, 3, 4}]}]];

(* eqs (4.16)-(4.18), the v1 assembly *)
psi2gonV1 := With[{B = bar},
   QLi2Bv1
   + QLi1B[{2, B[1], B[2], 1}] QLi1A[{2, 3, 4, B[1]}]
   - QLi1B[{2, 3, B[2], B[3]}] QLi1A[{B[2], 3, 4, B[1]}]
   + QLi1B[{4, B[3], B[4], 3}] QLi1A[{B[2], B[3], 4, B[1]}]
   - QLi1B[{4, B[1], B[4], 1}] QLi1A[{2, 3, 4, 1}]];

(* eq (eq:2gonQBv2):  (-1)^2 psi_{2-gon} = ... *)
psi2gonV2 := With[{B = bar},
   QLi2Bv2
   - QLi1Bm[{1, 2, B[1], B[2]}] QLi1Ap[{2, 3, 4, B[1]}]
   + QLi1Bp[{2, 3, B[2], B[3]}] QLi1Am[{3, 4, B[1], B[2]}]
   - QLi1Bm[{3, 4, B[3], B[4]}] QLi1Ap[{4, B[1], B[2], B[3]}]
   + QLi1Bp[{4, B[1], B[4], 1}] QLi1Am[{1, 2, 3, 4}]];

(* w = 3, Delta-form seed of (eq:QBoLid6v1); the full function is
   seed + (i->i+2) + (i->i+4).  The draft's red minus sign is kept as written. *)
QLi3BseedDelta := With[{d = dd, B = bar},
   -Li[{3}, {-d[2,3] d[4,5] d[B[1],6]/(d[1,2] d[3,4] d[5,6])}]
   - Li[{1,1,1}, {-d[B[1],2]/d[1,2], -d[2,3] d[B[1],4]/(d[3,4] d[B[1],2]), -d[4,5] d[B[1],6]/(d[5,6] d[B[1],4])}]
   + Li[{1,1,1}, {-d[B[1],2]/d[1,2], -d[2,3] d[B[1],6]/(d[3,6] d[B[1],2]), -d[4,5] d[3,6]/(d[5,6] d[3,4])}]
   - Li[{1,1,1}, {-d[B[1],2]/d[1,2], -d[2,5] d[B[1],6]/(d[5,6] d[B[1],2]), -d[2,3] d[4,5]/(d[2,5] d[3,4])}]
   - Li[{1,1,1}, {-d[2,3]/d[B[2],3], -d[B[2],3] d[4,5]/(d[3,4] d[B[2],5]), -d[B[2],5] d[B[1],6]/(d[5,6] d[1,2])}]
   + Li[{1,1,1}, {-d[2,3]/d[B[2],3], -d[B[2],3] d[B[1],4]/(d[3,4] d[1,2]), -d[4,5] d[B[1],6]/(d[5,6] d[B[1],4])}]
   - Li[{1,1,1}, {-d[2,3]/d[B[2],3], -d[B[2],3] d[B[1],6]/(d[3,6] d[1,2]), -d[4,5] d[3,6]/(d[5,6] d[3,4])}]
   - Li[{1,2},   {-d[2,3]/d[B[2],3], d[B[2],3] d[B[1],6] d[4,5]/(d[1,2] d[3,4] d[5,6])}]
   + Li[{1,1,1}, {-d[B[1],4]/d[1,4], -d[2,3] d[1,4]/(d[1,2] d[3,4]), -d[4,5] d[B[1],6]/(d[5,6] d[B[1],4])}]
   + Li[{2,1},   {d[2,3] d[B[1],4]/(d[1,2] d[3,4]), -d[4,5] d[B[1],6]/(d[5,6] d[B[1],4])}]
   + Li[{1,1,1}, {-d[B[1],4]/d[1,4], -d[B[1],6] d[4,5]/(d[B[1],4] d[5,6]), -d[1,4] d[2,3]/(d[1,2] d[3,4])}]
   - Li[{2,1},   {d[B[1],6] d[4,5]/(d[1,4] d[5,6]), -d[1,4] d[2,3]/(d[1,2] d[3,4])}]
   + Li[{1,2},   {-d[B[1],4]/d[1,4], d[B[1],6] d[4,5] d[1,4] d[2,3]/(d[B[1],4] d[5,6] d[1,2] d[3,4])}]];

QLi3B := QLi3BseedDelta + BshiftExpr[QLi3BseedDelta, 3, 2] + BshiftExpr[QLi3BseedDelta, 3, 4];

(* w = 3, q-form seed (last displayed equation of section 4); QLi3Bv2 = -QLi3B *)
QLi3Bv2seedQ := With[{B = bar},
   Li[{3}, {1/crqh[BpolyAll[3]]}]
   + Li[{1,1,1}, {-1/crqh[{1,2,B[1],B[2]}], qfold[{2,3,4,B[1]}],      qfold[{4,5,6,B[1]}]}]
   - Li[{1,1,1}, {-1/crqh[{1,2,B[1],B[2]}], qfold[{2,3,6,B[1]}],      1/qfold[{3,4,5,6}]}]
   + Li[{1,1,1}, {-1/crqh[{1,2,B[1],B[2]}], qfold[{2,5,6,B[1]}],      qfold[{2,3,4,5}]}]
   + Li[{1,2},   {-crqh[{2,3,B[2],B[3]}],   qfold[{2,3,4,B[1]}] qfold[{4,5,6,B[1]}]}]
   + Li[{1,1,1}, {-crqh[{2,3,B[2],B[3]}],   1/qfold[{3,4,5,B[2]}],    1/qfold[{5,6,B[1],B[2]}]}]
   - Li[{1,1,1}, {-crqh[{2,3,B[2],B[3]}],   1/qfold[{3,4,B[1],B[2]}], qfold[{4,5,6,B[1]}]}]
   + Li[{1,1,1}, {-crqh[{2,3,B[2],B[3]}],   1/qfold[{3,6,B[1],B[2]}], 1/qfold[{3,4,5,6}]}]
   - Li[{1,2},   {-crqh[{4,B[1],B[4],1}],   qfold[{4,5,6,B[1]}]/qfold[{1,2,3,4}]}]
   - Li[{1,1,1}, {-crqh[{4,B[1],B[4],1}],   1/qfold[{1,2,3,4}],       qfold[{4,5,6,B[1]}]}]
   - Li[{1,1,1}, {-crqh[{4,B[1],B[4],1}],   qfold[{4,5,6,B[1]}],      1/qfold[{1,2,3,4}]}]
   + Li[{2,1},   {-qfold[{4,5,6,B[1]}] crqh[{4,B[1],B[4],1}], 1/qfold[{1,2,3,4}]}]
   - Li[{2,1},   {-crqh[{4,B[1],B[4],1}]/qfold[{1,2,3,4}],    qfold[{4,5,6,B[1]}]}]];

QLi3Bv2 := QLi3Bv2seedQ + BshiftExpr[QLi3Bv2seedQ, 3, 2] + BshiftExpr[QLi3Bv2seedQ, 3, 4];

(* ---------- QLi^B as a function: explicit where the draft gives it ---------- *)

QLiBfun[1, P_List] := QLi1B[P];
QLiBfun[2, P_List] /; Length[P] === 8  := QLi2Bat[P[[1 ;; 4]]];
QLiBfun[3, P_List] /; Length[P] === 12 := QLi3B;
QLiBfun[w_Integer, P_List] := QLiB[P];      (* general n: the arborification *)

(* ---------- symbol helpers and kinematics ---------- *)

(* PolyLogTools is NOT used anywhere in this project.  The symbol grammar is the
   NumPolyLog.m / symbology.m one: the symbol is Tensor[l1,...,ln], the
   multiplicativity expander is ExpandTensor, and the route from a multiple
   polylog to its symbol is

        Li[{m...},{x...}]  --LiToG-->  G[{a...}, z]  --ToSymbol-->  Tensor[...]

   The Li ordering of symbology`LiToG (note the Reverse[m] in its definition) is
   the PolyLogTools / chain-paper (2605.06542) convention, which is also the one
   the loops note uses -- and differs from Rudenko's and from NumPolyLog`numLi. *)

(* ExpandTensor already splits products, quotients and powers and drops overall
   signs; all that is left is to kill entries that are pure numbers (a constant
   has vanishing symbol). *)
Bcanon[e_] := Expand[Expand[ExpandTensor[e]] /.
    Tensor[a___] /; AnyTrue[{a}, NumericQ] :> 0];
BsymOf[e_] := Bcanon[ToSymbol[LiToG[e]]];



(* ================================================================
   Chain wavefunctions: the general formula of 2605.06542
   ================================================================
   "de Sitter Wavefunction from Quadrangular Polylogarithms: Chain Graphs",
   transcribed from draft_v4.tex (\section{Solution of the Recursion}).
   Cross-ratio q_{ijkl} = D_ij D_kl/(D_jk D_li) = cr0 on the z's = -crq.      *)

qCR[a_, b_, c_, d_] := cr0[Subscript[z, a], Subscript[z, b], Subscript[z, c], Subscript[z, d]];

(* QLi^{+-}_k with the WEIGHT in the subscript (the paper's normalisation),
   in terms of QeLi/QoLi whose own index is k - n + 1 for a 2n-gon.
   Sanity: QLiP[k,{a,b,c,d}] = (-1)^k Li_k(q_abcd). *)

QLiP[k_Integer, P_List] := QeLi[k - Length[P]/2 + 1, P];
QLiM[k_Integer, P_List] := QoLi[k - Length[P]/2 + 1, P];
QLiPM[k_Integer, P_List] := If[EvenQ[First[P]], QLiP[k, P], QLiM[k, P]];

(* frozen twins, so that F_n can be assembled and inspected without expanding a
   single polylog -- the chain analogue of QQLiB / QQeLi / QQoLi on the loop side.
   QQqRoot freezes the root cross-ratio too; without it the "inert" expression
   would still carry the fully expanded z-rational inside the log. *)
QQLiP[k_Integer, P_List] := QQeLi[k - Length[P]/2 + 1, P];
QQLiM[k_Integer, P_List] := QQoLi[k - Length[P]/2 + 1, P];
QQLiPM[k_Integer, P_List] := If[EvenQ[First[P]], QQLiP[k, P], QQLiM[k, P]];

(* dissections of (0,...,2n-1); BevenDiss already returns the root piece S_0
   (the one carrying the edge (0,2n-1)) first, as the paper requires.
   Counts: 1, 4, 21, 126 for n = 2,3,4,5. *)
ChainDiss[P_List] := BevenDiss[P];

(* q_{S_0} = prod_{i=1}^{|S_0|/2-1} q_{S_0(1),S_0(2i),S_0(2i+1),S_0(2i+2)} *)
qRoot[S0_List] := Product[
   qCR[S0[[1]], S0[[2 i]], S0[[2 i + 1]], S0[[2 i + 2]]], {i, 1, Length[S0]/2 - 1}];

(* F_n, eq (eq:H_function_final), and F_1(a,b) = -log D_ab.
   Fchain is assembled from FchainTerms so that the SAME sub-family selection
   available for the loop (see DissMatchQ / BpsiSelect) works here too. *)

FchainTerms[P_List] /; Length[P] >= 4 := FchainTerms[P] =
  Module[{n = Length[P]/2},
   Function[D, <|"S0" -> First[D], "rest" -> Rest[D], "pieces" -> D,
      "k" -> Length[D] - 1, "allQuads" -> AllTrue[D, Length[#] === 4 &],
      "coeff" -> (-1)^(Length[D] - 1 + n)|>] /@ ChainDiss[P]];

(* INERT by construction: QQeLi / QQoLi / QQqRoot, never QeLi / QoLi.  Thaw with
   BinertToFun (Fchain does it for you). *)
FchainTermValue[t_Association] :=
  t["coeff"] (QQLiP[Length[t["S0"]]/2, t["S0"]] +
      QQLiP[Length[t["S0"]]/2 - 1, t["S0"]] Log[QQqRoot[t["S0"]]]) *
   Times @@ (QQLiPM[Length[#]/2 - 1, #] & /@ t["rest"]);

FchainTermValue[t_Association, sub_List, mode_String : "Inside"] :=
  FchainTermValue[t] /. {QQeLi[m_, Q_] :> Bstamp[QQeLi[m, Q], sub, mode],
     QQoLi[m_, Q_] :> Bstamp[QQoLi[m, Q], sub, mode]};

FchainSelect[P_List, pred : Except[_List | _String]] := Select[FchainTerms[P], pred];
FchainSelect[P_List, poly_List, mode_String : "Inside"] :=
  FchainSelect[P, DissMatchQ[#["pieces"], poly, mode] &];
FchainTerms[P_List, pred : Except[_List | _String]] := FchainSelect[P, pred];
FchainTerms[P_List, poly_List, mode_String : "Inside"] := FchainSelect[P, poly, mode];

(* just the chosen sub-family of F_n *)
FchainPart[P_List] /; Length[P] >= 4 := FchainInert[P];
FchainPart[P_List, pred : Except[_List | _String]] :=
  Total[FchainTermValue /@ FchainSelect[P, pred]];
FchainPart[P_List, poly_List, mode_String : "Inside"] :=
  Total[FchainTermValue[#, poly, mode] & /@ FchainSelect[P, poly, mode]];

(* FchainPart / FchainInert are inert; Fchain is the evaluated one. *)
FchainInert[P_List] /; Length[P] >= 4 := FchainPart[P, True &];

Fchain[{a_, b_}] := -Log[Subscript[z, a] - Subscript[z, b]];
Fchain[P_List] /; Length[P] >= 4 := FchainInert[P] /. BinertToFun;
Fchain[a__] := Fchain[{a}];

(* psi_n = F_n(2n+1,1,...,2n-1) - F_n(2n,1,...,2n-1) + F_n(2n,2n+1,2,...,2n-1) *)
psiChain[n_Integer] :=
  Fchain[Join[{2 n + 1}, Range[1, 2 n - 1]]] -
  Fchain[Join[{2 n}, Range[1, 2 n - 1]]] +
  Fchain[Join[{2 n, 2 n + 1}, Range[2, 2 n - 1]]];

FchainCounts[P_List] := FchainCounts[P, "k"];
FchainCounts[P_List, key_String] := KeySort[Counts[#[key] & /@ FchainTerms[P]]];
FchainCounts[P_List, poly_List, mode_String : "Inside"] :=
  KeySort[Counts[#["k"] & /@ FchainSelect[P, poly, mode]]];


(* ---- QLi of a polygon, parity fixed by the ORIGINAL definition ----
   QeLi (= QLi^+) when the polygon starts on an even label, QoLi (= QLi^-) when
   it starts on an odd label; lowest natural weight (M = 0, i.e. weight |P|/2-1).
   The optional (sub, mode) key restricts the arborification exactly as for
   QeLi/QoLi. *)

QLiStart[P_List] := If[EvenQ[First[P]], QeLi[0, P], QoLi[0, P]];
QLiStart[P_List, sub_List, mode_String : "Inside"] :=
  If[EvenQ[First[P]], QeLi[0, P, sub, mode], QoLi[0, P, sub, mode]];

(* ---- per-full-quadrangulation decomposition ----
   Sum ONLY over full quadrangulations Q of P (BquadDiss -- every cell a quad;
   no hexagons/octagons).  Each Q's contribution QLiStart[P,Q,"Inside"] already
   carries its correctly signed share of every parent term (perimeter and
   intermediate), so

       Total[Values[QLiByQuad[P]]] == QLiStart[P] .

   Verified through the octagon, both start parities.  The enumerator only
   packages the sum for inspection; it changes no sign.  (B-type analogue:
   QLiBByQuad, over the full B-quadrangulations First /@ TarbBTerms[n].) *)

QLiByQuad[P_List] := AssociationMap[QLiStart[P, #, "Inside"] &, BquadDiss[P]];
QLiBByQuad[P_List] /; Mod[Length[P], 4] === 0 := Module[{n = Length[P]/4},
   AssociationMap[QLiB[P, #, "Inside"] &,
     (First /@ TarbBTerms[n]) /. Thread[BpolyAll[n] -> P]]];


(* ================= Apsi: chain F with all pieces at lowest weight, no logs =================
   Same dissections and the same selection / key API as the Fchain family, but
   the term value is stripped down: the root piece S0 no longer carries the
   higher-weight QLi_{|S0|/2} or the log q_{S0}; EVERY piece (root included)
   contributes only the lowest-weight quadrangular polylog QLi_{|S|/2 - 1}(S).
   Inert by construction (QQeLi / QQoLi); Apsi[P] is the thawed value.          *)

ApsiTerms[P_List] := FchainTerms[P];

ApsiTermValue[t_Association] :=
  t["coeff"] QQLiP[Length[t["S0"]]/2 - 1, t["S0"]] *
   Times @@ (QQLiPM[Length[#]/2 - 1, #] & /@ t["rest"]);
ApsiTermValue[t_Association, sub_List, mode_String : "Inside"] :=
  ApsiTermValue[t] /. {QQeLi[m_, Q_] :> Bstamp[QQeLi[m, Q], sub, mode],
     QQoLi[m_, Q_] :> Bstamp[QQoLi[m, Q], sub, mode]};

ApsiSelect[P_List, pred : Except[_List | _String]] := Select[ApsiTerms[P], pred];
ApsiSelect[P_List, poly_List, mode_String : "Inside"] :=
  ApsiSelect[P, DissMatchQ[#["pieces"], poly, mode] &];
ApsiTerms[P_List, pred : Except[_List | _String]] := ApsiSelect[P, pred];
ApsiTerms[P_List, poly_List, mode_String : "Inside"] := ApsiSelect[P, poly, mode];

ApsiPart[P_List] := ApsiInert[P];
ApsiPart[P_List, pred : Except[_List | _String]] :=
  Total[ApsiTermValue /@ ApsiSelect[P, pred]];
ApsiPart[P_List, poly_List, mode_String : "Inside"] :=
  Total[ApsiTermValue[#, poly, mode] & /@ ApsiSelect[P, poly, mode]];

ApsiCounts[P_List] := ApsiCounts[P, "k"];
ApsiCounts[P_List, key_String] := KeySort[Counts[#[key] & /@ ApsiTerms[P]]];
ApsiCounts[P_List, poly_List, mode_String : "Inside"] :=
  KeySort[Counts[#["k"] & /@ ApsiSelect[P, poly, mode]]];

ApsiInert[P_List] := ApsiPart[P, True &];
Apsi[P_List] := ApsiInert[P] /. BinertToFun;
