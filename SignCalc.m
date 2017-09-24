(* ::Package:: *)

BeginPackage["SignCalc`"];

Print["\!\(\*
StyleBox[\"SignCalc\",\nFontSize->16,\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontSize->14]\)\!\(\*
StyleBox[\"v1\",\nFontSize->14]\)\!\(\*
StyleBox[\".0\",\nFontSize->14]\)\!\(\*
StyleBox[\" \",\nFontSize->14]\)\!\(\*
StyleBox[\"-\",\nFontSize->14]\)\!\(\*
StyleBox[\" \",\nFontSize->14]\)\!\(\*
StyleBox[\"package\",\nFontSize->14]\)\!\(\*
StyleBox[\" \",\nFontSize->14]\)\!\(\*
StyleBox[\"for\",\nFontSize->14]\)\!\(\*
StyleBox[\" \",\nFontSize->14]\)\!\(\*
StyleBox[\"Chiara\",\nFontSize->14]\)"];


Mom::"usage"=
"Mom is the head of a four momentum p^\[Mu].

It is used as Momentum[ p,index ].";

FieldA::"usage"=
"FieldA[ pos,ind ] is the head of a photon field A^ind(pos).";

FieldPsi::"usage"=
"FiedlPsi[ pos,ind ] is the head of a spinor \!\(\*SubscriptBox[\(\[Psi]\), \(ind\)]\)(pos) field.";

FieldPsiBar::"usage"=
"FiedlPsiBar[ pos,ind ] is the head of a spinor \!\(\*SubscriptBox[OverscriptBox[\(\[Psi]\), \(_\)], \(ind\)]\)(pos) field.";

SpinU::"usage"=
"SpinU[ p,ind ] is the head of a \!\(\*SubscriptBox[\(u\), \(ind\)]\)(p) spinor.";

DiracGamma::"usage"=
"DiracGamma[ indLor,ind1,ind2 ] is the head of a Dirac gamma matrix \!\(\*SubsuperscriptBox[\(\[Gamma]\), \(ind1, ind2\), \(indLor\)]\).";

Slash::"usage"=
"Slash[ p ] is the head of a Feyman slashed momentum.";

ScalarP::"usage"=
"ScalarP[p,q] is the head of the scalar product p*q.";

tr::"usage"=
"tr[ arg ] is the head of a Dirac trace.";

Metric::"usage"=
"Metric[ ind1,ind2 ] is the head of a metric tensor \!\(\*SuperscriptBox[\(g\), \(ind1\\\ ind2\)]\).";

Boxx::"usage"=
"Boxx[ pos ] is the head of a D'Alembertian operator in the four-vector pos, \!\(\*SubscriptBox[\(\[Square]\), \(x\)]\).";

LeftPartial::"usage"=
"LeftPartial[ pos,ind ] is the head of a partial derivative operator (\!\(\*OverscriptBox[SubscriptBox[\(\[PartialD]\), \(pos\)], \(\[LeftArrow]\)]\)\!\(\*SuperscriptBox[\()\), \(ind\)]\).";

RightPartial::"usage"=
"RightPartial[ pos,ind ] is the head of a partial derivative operator (\!\(\*OverscriptBox[SubscriptBox[\(\[PartialD]\), \(pos\)], \(\[RightArrow]\)]\)\!\(\*SuperscriptBox[\()\), \(ind\)]\).";

LeftPartialSlash::"usage"=
"LeftPartialSlash[ pos,ind ] is the head of a slashed partial derivative operator \!\(\*SuperscriptBox[\(\[Gamma]\), \(ind\)]\)(\!\(\*OverscriptBox[SubscriptBox[\(\[PartialD]\), \(pos\)], \(\[LeftArrow]\)]\)\!\(\*SuperscriptBox[\()\), \(ind\)]\).";

RightPartialSlash::"usage"=
"RightPartialSlash[ pos,ind ] is the head of a slashed partial derivative operator \!\(\*SuperscriptBox[\(\[Gamma]\), \(ind\)]\)(\!\(\*OverscriptBox[SubscriptBox[\(\[PartialD]\), \(pos\)], \(\[RightArrow]\)]\)\!\(\*SuperscriptBox[\()\), \(ind\)]\).";



LorentzContract::"usage"=
"This function contracts Lorentz indices only.";

DiracContract::"usage"=
"This function contracts spinor indices only.";

FullContract::"usage"=
"This function contracts Lorentz indices and then spinor indices.";

Dotter::"usage"=
"Dotter[ expr ] transforms a Times expression into a Dot expression.";

Timer::"usage"=
"Timer[ expr ] transforms a Dot expression into a Times expression.";

Lister::"usage"=
"Lister[ expr ] transforms expression expr into a list.";

SwapWick::"usage"=
"Swap[ list, i, j ] swaps elements i and j in list.";

PermuteWick::"usage"=
"Permute[ list, n ] cyclically permutes list n times.";

Wick::"usage"=
"Wick performs the Wick theorem on a list of fields.";

GetAmp::"usage"=
"Gives the amplitude corresponding to the given Wick expansion.";

ExtFact::"usage"=
"Applies external factors to amp.";

Integrations::"usage"=
"Performs integrations over the space variables provided and propagator momenta.";


Begin["`Private`"]


Mom /:
   MakeBoxes[ Mom[p_, index_], TraditionalForm
            ] := MakeBoxes[p^index, TraditionalForm];

FieldA /:
	MakeBoxes[ FieldA[ pos_,ind_ ], TraditionalForm
            ] := MakeBoxes[(("A")^ind)[pos], TraditionalForm];

FieldPsi /:
	MakeBoxes[ FieldPsi[pos_], TraditionalForm
            ] := MakeBoxes["\[Psi]"[pos], TraditionalForm];
	MakeBoxes[ FieldPsi[pos_,ind_], TraditionalForm
            ] := MakeBoxes[Subscript["\[Psi]", ind][pos], TraditionalForm];
	MakeBoxes[ FieldPsi[pos_,ind_,label_], TraditionalForm
            ] := MakeBoxes[Subscript["\[Psi]", ind][pos], TraditionalForm];

FieldPsiBar /:
	MakeBoxes[ FieldPsiBar[pos_], TraditionalForm
            ] := MakeBoxes["\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\)"[pos], TraditionalForm];
	MakeBoxes[ FieldPsiBar[pos_,ind_], TraditionalForm
            ] := MakeBoxes[Subscript["\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\)", ind][pos], TraditionalForm];
	MakeBoxes[ FieldPsiBar[pos_,ind_,label_], TraditionalForm
            ] := MakeBoxes[Subscript["\!\(\*OverscriptBox[\(\[Psi]\), \(_\)]\)", ind][pos], TraditionalForm];

SpinU /:
	MakeBoxes[ SpinU[mom_,ind_], TraditionalForm
            ] := MakeBoxes[Subscript["u", ind][mom], TraditionalForm];
	MakeBoxes[ SpinU[mom_], TraditionalForm
            ] := MakeBoxes["u"[mom], TraditionalForm];
	MakeBoxes[ SpinU[mom_,label_], TraditionalForm
            ] := MakeBoxes["u"[mom], TraditionalForm];

DiracGamma /:
	MakeBoxes[ DiracGamma[indLor_,ind1_,ind2_], TraditionalForm
            ] := MakeBoxes[Subscript[(("\[Gamma]")^indLor), ind1.ind2], TraditionalForm];
	MakeBoxes[ DiracGamma[indLor_], TraditionalForm
            ] := MakeBoxes[Superscript["\[Gamma]",indLor], TraditionalForm];
	MakeBoxes[ DiracGamma[indLor_,label_], TraditionalForm
            ] := MakeBoxes[Superscript["\[Gamma]",indLor], TraditionalForm];

Slash /:
	MakeBoxes[ Slash[p_,ind1_,ind2_], TraditionalForm
			] := MakeBoxes[Subscript[HoldForm[\!\(\*OverscriptBox[
UnderscriptBox[\(p\), \(_\)], \(_\)]\)]," "ind1.ind2],TraditionalForm];
	MakeBoxes[ Slash[p_], TraditionalForm
            ] := MakeBoxes[\!\(\*OverscriptBox[
UnderscriptBox[\(p\), \(_\)], \(_\)]\),TraditionalForm];
	MakeBoxes[ Slash[p_,label_], TraditionalForm
            ] := MakeBoxes[\!\(\*OverscriptBox[
UnderscriptBox[\(p\), \(_\)], \(_\)]\),TraditionalForm];
            
ScalarP /:
	MakeBoxes[ ScalarP[p_,q_], TraditionalForm
			] := MakeBoxes[p\[CenterDot]q,TraditionalForm];
            
tr /:
	MakeBoxes[ tr[arg_], TraditionalForm
            ] := MakeBoxes["tr"[arg], TraditionalForm];

Metric /:
	MakeBoxes[ Metric[ind1_,ind2_], TraditionalForm
            ] := MakeBoxes[("g")^(ind1 ind2), TraditionalForm];
	MakeBoxes[ Metric[ind1_,ind2_,label_], TraditionalForm
            ] := MakeBoxes[("g")^(ind1 ind2), TraditionalForm];

Boxx /:
	MakeBoxes[ Boxx[pos_], TraditionalForm
            ] := MakeBoxes[Subscript["\[Square]", pos], TraditionalForm];

LeftPartial /:
	MakeBoxes[ LeftPartial[pos_,ind_], TraditionalForm
            ] := MakeBoxes[Subscript[("\!\(\*OverscriptBox[\(\[PartialD]\), \(\[LeftArrow]\)]\)"), pos], TraditionalForm];

RightPartial /:
	MakeBoxes[ RightPartial[pos_,ind_], TraditionalForm
            ] := MakeBoxes[Subscript[("\!\(\*OverscriptBox[\(\[PartialD]\), \(\[RightArrow]\)]\)"), pos], TraditionalForm];

LeftPartialSlash /:
	MakeBoxes[ LeftPartialSlash[pos_,ind1_,ind2_], TraditionalForm
            ] := MakeBoxes[Subsuperscript[Overscript[Overlay[{"\[PartialD]"," /"}],"\[LeftArrow]"],pos,ind1.ind2], TraditionalForm];

RightPartialSlash /:
	MakeBoxes[ RightPartialSlash[pos_,ind1_,ind2_], TraditionalForm
            ] := MakeBoxes[Subsuperscript[Overscript[Overlay[{"\[PartialD]"," /"}],"\[RightArrow]"],pos,ind1.ind2], TraditionalForm];


LorentzContract[expr_]:=Block[
{expr0,expr1,len,lorentzcheck,replace,replace1,delete,pos,pos1,pos2,pos3,posi,index,ind,indlor,ind1,ind2,
	name,name1,numfactor,metrics,indices,multi,multi2,i,j,traceflag,flag,
	diractraces,diractraces1,diractr,diraccontracted,dirac1,dirac2,diraclist,diraclist1,diractimes,
	diraclabel,sl,sl1,slc,sltr,ggc,ggt},


If[Head[expr]===List,
len=Length[expr],
len=1;
];


expr0={};
For[j=1,j<=len,j++,

If[Head[expr]===List,
expr1=expr[[j]],
expr1=expr;
];


diractraces1=Select[expr1,MemberQ[{tr},Head[#]]&];
diraccontracted=Select[expr1,MemberQ[{Dot},Head[#]]&];

If[!(diraccontracted===1),
If[Head[diraccontracted]===Dot,
	diraccontracted={diraccontracted},
	diraccontracted=Lister[diraccontracted];
],
diraccontracted={};
];

If[!(diractraces1===1),
If[Head[diractraces1]===tr,
	diractraces={diractraces1},
	(*diractr={};
	For[i=1,i\[LessEqual]Length[diractraces1],i++,
	Print[Lister[diractraces1[[i]][[1]]]];
	diractr=Append[diractr,Lister[diractraces1[[i]][[1]]]];
	Print[diractr[[1]]];
	];
	Print["diractr  ",diractr];*)
	diractraces=Lister[diractraces1];
],
diractraces={};
];

diraclist={};
For[i=1,i<=Length[diraccontracted],i++,
dirac1=diraccontracted[[i]];
diraclist1=Table[Append[dirac1[[j]],{"c",i,Alphabet[][[j]]}],{j,1,Length[dirac1]}];
diraclist=Append[diraclist,diraclist1];
Print[dirac1];
pos=Position[expr1,dirac1][[1,1]];
expr1=ReplacePart[expr1,{pos->Timer[Flatten[diraclist1]]}];
];


diraclist={};
For[i=1,i<=Length[diractraces],i++,
dirac1=diractraces[[i]];
dirac2=dirac1[[1]];
Print["dirac1  ",dirac1];
Print["dirac2  ",dirac2];
diraclist1=Table[Append[dirac2[[j]],{"t",i,Alphabet[][[j]]}],{j,1,Length[dirac2]}];
diraclist=Append[diraclist,diraclist1];
pos=Position[expr1,dirac1];
Print[pos];
expr1=ReplacePart[expr1,{pos->Timer[Flatten[diraclist1]]}];
];

Print["expr1  ",expr1];

lorentzcheck={};
For[i=1,i<=Length[expr1],i++,
If[Head[expr1[[i]]]===Mom,
	lorentzcheck=Append[lorentzcheck,expr1[[i]][[2]]];
];
If[Head[expr1[[i]]]===FieldA,
	lorentzcheck=Append[lorentzcheck,expr1[[i]][[2]]];
];
If[Head[expr1[[i]]]===DiracGamma,
	lorentzcheck=Append[lorentzcheck,expr1[[i]][[1]]];
];
If[Head[expr1[[i]]]===Metric,
	lorentzcheck=Append[lorentzcheck,expr1[[i]][[1]]];
	lorentzcheck=Append[lorentzcheck,expr1[[i]][[2]]];
];
];
multi=Tally[lorentzcheck];
multi2=multi[[All,2]];
If[Select[multi2,#>2&]!={},
Print["ERROR: Lorentz index repeated more than twice!"];
Print["Abort."];
Return[];
];



(* Contract Gammas with...*)
pos=Position[expr1,DiracGamma[___]]//Flatten;
replace={};
delete={};
For[i=1,i<=Length[pos],i++,
ind=expr1[[pos[[i]]]][[1]];
If[Head[expr1[[pos[[i]]]][[2]]]=!=List,
ind1=expr1[[pos[[i]]]][[2]];
ind2=expr1[[pos[[i]]]][[3]];
diraclabel=0,
diraclabel=expr1[[pos[[i]]]][[2]];
];
If[DeleteCases[Position[expr1,ind][[All,1]],pos[[i]]]!={},
pos1=DeleteCases[Position[expr1,ind][[All,1]],pos[[i]]][[1]],
Break[];
];
(* ...four-vectors *)
If[Head[expr1[[pos1]]]===Mom,
If[diraclabel==0,
replace=Append[replace,pos[[i]]->Slash[expr1[[pos1]][[1]],ind1,ind2]],
replace=Append[replace,pos[[i]]->Slash[expr1[[pos1]][[1]],diraclabel]];
];
delete=Append[delete,{pos1}];
];
(* ...metric tensor *)
If[Head[expr1[[pos1]]]===Metric,
Print["metric"];
indlor=Complement[{expr1[[pos1]][[1]],expr1[[pos1]][[2]]},{ind}][[1]];
Print[indlor];
Print[diraclabel];
If[diraclabel===0,
replace=Append[replace,pos[[i]]->DiracGamma[indlor,ind1,ind2]],
replace=Append[replace,pos[[i]]->DiracGamma[indlor,diraclabel]];
];
delete=Append[delete,{pos1}];
]
];
expr1=ReplacePart[expr1,replace];
expr1=Delete[expr1,delete];

Print["expr1  ",expr1];


(* Contract Momenta with...*)

Print["momenta"];
pos=Position[DeleteDuplicates[expr1],Mom[__]]//Flatten;
replace={};
delete={};
Print[pos];
i=1;
While[pos!={},
name=expr1[[pos[[1]]]][[1]];
ind=expr1[[pos[[1]]]][[2]];
Print["ind ",ind];
pos1=DeleteCases[Position[expr1,ind][[All,1]],pos[[1]]][[1]];
Print[Head[expr1[[pos1]]]];

(* ...momenta *)
If[Head[expr1[[pos1]]]===Mom,
replace=Append[replace,pos[[1]]->name^2];
delete=Append[delete,{pos1}];
pos=Delete[pos,pos[[1]]];
pos=Delete[pos,pos1];
]
(* ...metric tensor *)
If[Head[expr1[[pos1]]]===Metric,
indlor=Complement[{expr1[[pos1]][[1]],expr1[[pos1]][[2]]},{ind}][[1]];
Print[indlor];
pos3=DeleteCases[Position[expr1,indlor][[All,1]],pos1][[1]];
If[Head[expr1[[pos3]]]===Mom,
name1=expr1[[pos3]][[1]];
ind1=expr1[[pos3]][[2]];
(* replace=Append[replace,pos[[1]]\[Rule]ScalarP[name,name1]]; *)
If[name1!=name,
expr1=ReplacePart[expr1,pos[[1]]->ScalarP[name,name1]],
expr1=ReplacePart[expr1,pos[[1]]->name^2]
];
(* delete=Append[delete,{pos1,pos3}]; *)
expr1=ReplaceAll[expr1,Mom[name1,ind1]->1];
expr1=ReplaceAll[expr1,Metric[ind,ind1]->1];
pos=Delete[pos,1];
pos=Delete[pos,Position[pos,pos3]];
Print[pos];
]
];
i++
];
(* expr1=ReplacePart[expr1,replace];
expr1=Delete[expr1,delete]; *)
Print[expr1];


(* Contract metric tensor with metric tensor*)
numfactor=1;
metrics=Cases[expr1,Metric[__]];

flag=0;
While[flag==0,
indices=Table[{metrics[[i]][[1]],metrics[[i]][[2]]},{i,1,Length[metrics]}]//Flatten;
multi=Tally[indices];
multi2=multi[[All,2]];
If[Select[multi2,#>1&]!={},
index=Flatten[Select[multi,#[[All]][[2]]==2&]][[1]];
posi=Flatten[Position[indices,index]];

traceflag=0;
If[OddQ[posi[[1]]],
	If[posi[[2]]!=posi[[1]]+1,traceflag=1],
	If[posi[[2]]!=posi[[1]]-1,traceflag=1]
];
If[traceflag==1,
ind1=If[EvenQ[posi[[1]]],
	Complement[{indices[[posi[[1]]-1]],indices[[posi[[1]]]]},{index}][[1]],
	Complement[{indices[[posi[[1]]+1]],indices[[posi[[1]]]]},{index}][[1]]
];
pos1=Ceiling[posi[[1]]/2];
ind2=ind2=If[EvenQ[posi[[2]]],
	Complement[{indices[[posi[[2]]-1]],indices[[posi[[2]]]]},{index}][[1]],
	Complement[{indices[[posi[[2]]+1]],indices[[posi[[2]]]]},{index}][[1]]
];
pos2=Ceiling[posi[[2]]/2];
metrics=ReplacePart[metrics,{pos1->Metric[ind1,ind2]}];
metrics=Delete[metrics,{pos2}],
pos1=Ceiling[posi[[1]]/2];
metrics=Delete[metrics,{pos1}];
numfactor=numfactor*4;
],
flag=1;
];
];
expr1=DeleteCases[expr1,Metric[__]];
If[Head[expr1]===Dot,
For[i=1,i<=Length[metrics],i++,
expr1=expr1.metrics[[i]];
If[numfactor!=1,
expr1=numfactor.expr1];
],
For[i=1,i<=Length[metrics],i++,
expr1=expr1*metrics[[i]];
If[numfactor!=1,
expr1=numfactor*expr1];
];
];

If[diraccontracted!={},
sl=Select[expr1,MemberQ[{Slash,DiracGamma,SpinU},Head[#]]&];
sl1=Select[sl,Head[#[[2]]]===List &];
slc=Select[sl1,#[[2]][[1]]=="c" &];
sltr=Select[sl1,#[[2]][[1]]=="t" &];
Print["sltr  ",sltr];
ggc=GroupBy[Lister[slc],#[[2]][[2]]&];
For[i=1,i<=Length[slc],i++,
expr1=DeleteCases[expr1,slc[[i]]];
];
For[i=1,i<=Length[ggc],i++,
expr1=expr1*Dotter[SortBy[ggc[[i]],#[[2]][[3]]&]];
];
];
If[diractraces!={},
ggt=GroupBy[Lister[sltr],#[[2]][[2]]&];
Print["ggt  ",ggt];
For[i=1,i<=Length[sltr],i++,
expr1=DeleteCases[expr1,sltr[[i]]];
];
For[i=1,i<=Length[ggt],i++,
expr1=expr1*tr[Dotter[ggt[[i]]]];
];
Print[expr1];
];
expr0=Append[expr0,expr1];
];

If[Head[expr]===List,
	Return[expr0],
Return[expr0[[1]]];
];
];


DiracContract[expr_]:=Block[
{expr0,len,b,b1,b1a,b1b,diracplace,diracexpr,sl,lensl,rest,
indlist,elemlist,elemlist1,pos,pos1,tocontr,tocontr1,ind1,i,j,k,start,contracted,contracted1},

If[Head[expr]===List,
len=Length[expr],
len=1;
];


expr0={};
For[k=1,k<=len,k++,

If[Head[expr]===List,
b=expr[[k]],
b=expr;
];



Print[Head[b]];

If[Head[b]===Times||Head[b]===Dot,
sl=Select[b,MemberQ[{SpinU,DiracGamma,Slash},Head[#]]&];
rest=b;
lensl=Length[sl];
Print[sl];
Print[Length[sl]];
Print[sl[[1]]];
Print[sl[[2]]];
Print[Head[sl]];
(*If[Head[sl]=!=List,
	lensl=1;
];*)
Print["lensl= ",lensl];
For[i=1,i<=lensl,i++,
rest=DeleteCases[rest,sl[[i]]];
];
If[rest==Last[sl],rest=1];

indlist={};
elemlist={};
For[i=1,i<=lensl,i++,
If[Head[sl[[i]]]===SpinU,
indlist=Append[indlist,{sl[[i]][[2]]}];
elemlist=Append[elemlist,sl[[i]]];
];
If[Head[sl[[i]]]===DiracGamma||Head[sl[[i]]]===Slash,
indlist=Append[indlist,{sl[[i]][[2]],sl[[i]][[3]]}];elemlist=Append[elemlist,sl[[i]]];
];
];

pos=Position[Tally[Flatten[indlist]][[All,2]],1]//Flatten;
If[Length[pos]>0,
pos1=pos[[1]];
ind1=Tally[Flatten[indlist]][[pos1]][[1]];
If[Flatten[Position[elemlist,ind1]][[2]]==3,pos1=pos[[2]]],
pos1=1;
];

elemlist1=elemlist;
tocontr={};
tocontr1={};
If[indlist!={},
ind1=Tally[Flatten[indlist]][[pos1]][[1]];
];

Print["CULO"];
Print[elemlist];

For[i=1,i<=Length[elemlist],i++,

If[Position[indlist,ind1]!={},
pos1=Position[indlist,ind1][[1,1]];
tocontr1=Append[tocontr1,elemlist1[[pos1]]];
If[Length[indlist]>1,
	If[Complement[indlist[[pos1]],{ind1}]!={},
		ind1=Complement[indlist[[pos1]],{ind1}][[1]],
		ind1=1;
	],
ind1=indlist[[1]];
];
indlist=Delete[indlist,pos1];
elemlist1=Delete[elemlist1,pos1],

tocontr=Append[tocontr,tocontr1];
If[indlist!={},
pos=Position[Tally[Flatten[indlist]][[All,2]],1]//Flatten;
];

If[Length[pos]>0,
pos1=pos[[1]];
ind1=Tally[Flatten[indlist]][[pos1]][[1]];
If[Flatten[Position[elemlist,ind1]][[2]]==3,pos1=pos[[2]]],
pos1=1;
];
ind1=Tally[Flatten[indlist]][[pos1]][[1]];
tocontr1={};
i=i-1;
]
];
tocontr=DeleteDuplicates[Append[tocontr,tocontr1]];

contracted=1;


For[j=1,j<=Length[tocontr],j++,
tocontr1=tocontr[[j]];

If[Length[tocontr1]>1,

If[Head[tocontr1[[1]]]==Slash,
contracted1=Slash[tocontr1[[1]][[1]]];
];
If[Head[tocontr1[[1]]]==DiracGamma,
contracted1=DiracGamma[tocontr1[[1]][[1]]];
];
If[Head[tocontr1[[1]]]==SpinU,
contracted1=SpinU[tocontr1[[1]][[1]]];
];

For[i=2,i<=Length[tocontr1],i++,
If[Head[tocontr1[[i]]]==Slash,
contracted1=contracted1.Slash[tocontr1[[i]][[1]]];
];
If[Head[tocontr1[[i]]]==DiracGamma,
contracted1=contracted1.DiracGamma[tocontr1[[i]][[1]]];
];
If[Head[tocontr1[[i]]]==SpinU,
contracted1=contracted1.SpinU[tocontr1[[i]][[1]]];
];
],
contracted1=tocontr1;
];

If[tocontr1!={},
If[!(Head[Last[tocontr1]]===SpinU),
	If[First[tocontr1][[2]]===Last[tocontr1][[3]],
		contracted1=tr[contracted1];
	];
	contracted=contracted*contracted1,
	contracted=contracted*contracted1;
];
];
];
expr0=Append[expr0,contracted*rest],
expr0=Append[expr0,b];
]
];
expr0=Flatten[expr0];

Print[Head[expr]];
If[Head[expr]===List,
	Return[expr0],
	Return[expr0[[1]]];
];

];


FullContract[expr_]:=Block[
{expr1},
expr1=LorentzContract[expr];
expr1=DiracContract[expr1];
Return[expr1];
];


Dotter[expr_]:=Block[
{expr1,i},
expr1=expr[[1]];
For[i=2,i<=Length[expr],i++,
expr1=expr1.expr[[i]];
];
Return[expr1];
];


Timer[expr_]:=Block[
{expr1,i},
expr1=1;
For[i=1,i<=Length[expr],i++,
expr1=expr1*expr[[i]];
];
Return[expr1];
];


Lister[expr_]:=Block[
{list1,i},
list1={};
For[i=1,i<=Length[expr],i++,
list1=Append[list1,expr[[i]]];
];
Return[list1];
];


SwapWick[list_,tuplelist_]:=Block[
{temp,prefactor,pre,wicklist,postfactor,sign,list1,poslist,i,a,b},
prefactor=list[[1]];
pre=list[[2]];
wicklist=list[[3]];
postfactor=list[[4]];
sign=wicklist[[1]];
list1=Delete[wicklist,{1}];
If[Depth[tuplelist]==2,
poslist={tuplelist},
poslist=tuplelist;
];
For[i=1,i<=Length[poslist],i++,
a=poslist[[i]][[1]];
b=poslist[[i]][[2]];
temp=list1[[a]];
list1[[a]]=list1[[b]];
list1[[b]]=temp;
];
wicklist=Prepend[list1,sign];
Return[{prefactor,pre,wicklist,postfactor}];
]


PermuteWick[list_,a_]:=Block[
{temp,prefactor,pre,wicklist,postfactor,sign,list1,i,j},
prefactor=list[[1]];
pre=list[[2]];
wicklist=list[[3]];
postfactor=list[[4]];
sign=wicklist[[1]];
list1=Delete[wicklist,{1}];
For[i=1,i<=a,i++,
temp=Last[list1];
For[j=Length[list1],j>1,j--,
list1[[j]]=list1[[j-1]];
];
list1[[1]]=temp;
];
wicklist=Prepend[list1,sign];
Return[{prefactor,pre,wicklist,postfactor}];
]


Wick[lista_]:=Block[
{prefactor,pre,expr0,postfactor,exprgamma,exprmom,exprmetric,exprslash,exprnum,expr1,exps,exps1,box,
lista1,numfactor,counter,c,cc,cc1,i,j,k,l,row,rownew,element,field1,field2,flag,lista2,
sign,signcount},
prefactor=lista[[1]];
expr0=lista[[2]];
postfactor=lista[[3]];

exprgamma=Cases[expr0,DiracGamma[___]];
expr1=DeleteCases[expr0,DiracGamma[___]];
exprmom=Cases[expr1,Mom[__]];
expr1=DeleteCases[expr1,Mom[__]];
exprmetric=Cases[expr1,Metric[__]];
expr1=DeleteCases[expr1,Metric[__]];
exprslash=Cases[expr1,Slash[___]];
expr1=DeleteCases[expr1,Slash[___]];
exprnum=Cases[expr1,_Integer];
exprnum=Append[exprnum,1];
expr1=DeleteCases[expr1,_Integer];

pre=1;
For[i=1,i<=Length[exprmom],i++,
pre=pre*exprmom[[i]];
];
For[i=1,i<=Length[exprgamma],i++,
pre=pre*exprgamma[[i]];
];
For[i=1,i<=Length[exprmetric],i++,
pre=pre*exprmetric[[i]];
];
For[i=1,i<=Length[exprslash],i++,
pre=pre*exprslash[[i]];
];
numfactor=Product[exprnum[[i]],{i,1,Length[exprnum]}];
If[numfactor!=1,
	pre=numfactor*pre;
];

exps={};
exps=Append[exps,Select[expr0,MemberQ[{FieldA},Head[#]]&]];
exps=Append[exps,Select[expr0,MemberQ[{FieldPsi,FieldPsiBar},Head[#]]&]];

exps1={{},{}};
For[l=1,l<=2,l++,

expr1=exps[[l]];

If[EvenQ[Length[expr1]],

lista1=Table[expr1[[i]],{i,1,Length[expr1]}];

counter=1;
For[j=1,j<=Length[lista1],j++,
If[Head[lista1[[j]]]===FieldPsi,
lista1[[j]]=FieldPsi[lista1[[j]][[1]],lista1[[j]][[2]],counter];
counter++;
];
If[Head[lista1[[j]]]===FieldPsiBar,
lista1[[j]]=FieldPsiBar[lista1[[j]][[1]],lista1[[j]][[2]],counter];
counter++;
];
];

c = Map[lista1[[#]]&,DeleteDuplicates[Map[Sort,Partition[#,2]&/@Permutations[Range[Length@lista1]],2]],{2}];


(* ciclo sulle righe di c *)
For[i=1,i<=Length[c],i++,
cc1={};
flag=1;
row=c[[i]];
rownew={};

For[j=1,j<=Length[row],j++,
element=row[[j]];
field1=element[[1]];
field2=element[[2]];

If[!(field1[[1]]===field2[[1]]),
If[Head[field1]===FieldA,
If[Head[field2]===FieldA,
rownew=Append[rownew,element];
];
];

If[Head[field1]===FieldPsi,
If[Head[field2]===FieldPsiBar,
rownew=Append[rownew,element];
];
];

If[Head[field1]===FieldPsiBar,
If[Head[field2]===FieldPsi,
rownew=Append[rownew,{field2,field1}];
flag=-1;
];
];
];
If[Length[rownew]==Length[lista1]/2.,
cc1=Flatten[Append[cc1,rownew],1];

];
];

If[Length[cc1]>0,
lista2=Flatten[cc1];
If[l!=1,
sign=Signature[DeleteCases[Table[If[Head[lista2[[i]]]===FieldPsi||Head[lista2[[i]]]===FieldPsiBar,lista2[[i]][[3]]],{i,1,Length[lista2]}],Null]];
cc1=Prepend[cc1,sign];
];



exps1[[l]]=Append[exps1[[l]],{cc1}];
];
],
Return[{}];
];
];

signcount=0;
cc={};
For[i=1,i<=Length[exps1[[2]]],i++,
For[j=1,j<=Length[exps1[[1]]],j++,
cc1=Flatten[exps1[[2]][[i]],1];
If[cc1[[1]]==-1,signcount++];
For[k=1,k<=Length[Flatten[exps1[[1]],1][[j]]],k++,
cc1=Append[cc1,Flatten[exps1[[1]],1][[j]][[k]]];
];
cc=Append[cc,{prefactor,pre,cc1,postfactor}];
];
];

Print[Length[cc]," non vanishing combinations."];
Print[signcount," odd permutations of spinor fields."];
Print[" "];
(* cc=Append[cc,{prefactor,pre,cc1,postfactor}]; *)
Return[cc];

]


GetAmp[a_,p_]:=Block[
{aa,prefactor,pre,postfactor,amp,momCount,varspace,varmom,vareiko,momX,momZ,
exp,prop,ind1,ind2,lr,flag,test,i,j,\[Lambda]},
prefactor=a[[1]];
pre=a[[2]];
aa=a[[3]];
postfactor=a[[4]];
amp=aa[[1]];
momCount=1;
varspace={};
varmom={};
vareiko={};

For[i=2,i<=Length[aa],i++,
If[Length[aa[[i]]]==1,amp=amp*aa[[i]]];
If[Length[aa[[i]]]==2,
If[Head[aa[[i]][[1]]]===FieldPsi,
exp=Exp[-I*p[momCount]*(aa[[i]][[1]][[1]]-aa[[i]][[2]][[1]])];
varmom=Append[varmom,p[momCount]];
varspace=Append[varspace,aa[[i]][[1]][[1]]];
varspace=Append[varspace,aa[[i]][[2]][[1]]];
ind1=aa[[i]][[1]][[2]];
ind2=aa[[i]][[2]][[2]];
prop=I*Slash[p[momCount],ind1,ind2]/(p[momCount]^2);
amp=amp*prop*exp;
momCount++,

ind1=aa[[i]][[1]][[2]];
ind2=aa[[i]][[2]][[2]];
exp=Exp[-I*p[momCount]*(aa[[i]][[1]][[1]]-aa[[i]][[2]][[1]])];
varmom=Append[varmom,p[momCount]];


If[Head[aa[[i]][[1]][[1]]]=!=Times,
varspace=Append[varspace,aa[[i]][[2]][[1]]],
lr=Lister[aa[[i]][[1]][[1]]];
flag=1;
For[j=1,j<=Length[lr],j++,
test=lr[[j]];
If[Head[test]===Symbol,
If[ToString[test]==="\[Lambda]",
	vareiko=Append[vareiko,test];flag=0],
If[ToString[Head[test]]==="\[Lambda]",vareiko=Append[vareiko,test];flag=0]]
];
If[flag==1,Print["ERROR"];Return[];];
];

If[Head[aa[[i]][[2]][[1]]]=!=Times,
varspace=Append[varspace,aa[[i]][[2]][[1]]],
lr=Lister[aa[[i]][[2]][[1]]];
flag=1;
For[j=1,j<=Length[lr],j++,
test=lr[[j]];
If[Head[test]===Symbol,
If[ToString[test]==="\[Lambda]",
	vareiko=Append[vareiko,test];flag=0],
If[ToString[Head[test]]==="\[Lambda]",vareiko=Append[vareiko,test];flag=0]]
];
If[flag==1,Print["ERROR"];Return[];];
];
prop=-I*Metric[ind1,ind2]/(p[momCount]^2);
amp=amp*prop*exp;
momCount++
];
];
];
varspace=DeleteDuplicates[varspace];
Return[{prefactor,pre*amp,postfactor,varspace,varmom,vareiko}];
];


ExtFact[amp_]:=Block[
{expr,prefactor,pre,b,postfactor,varspace,varmom,vareiko,post,post1,posbox,posex,posu,exp,varx,posdeslash,varz,
ind,inda,indb,indu,ind1,ind2,pos,pos1,momu,
deleteslash,deslash,momz,posslash,i},
prefactor=amp[[1]];
b=amp[[2]];
postfactor=amp[[3]];
varspace=amp[[4]];
varmom=amp[[5]];
vareiko=amp[[6]];


posbox=Flatten[Position[prefactor,Boxx[_]]];

If[posbox!={},
varx=prefactor[[posbox[[1]]]][[1]];
pre=DeleteCases[prefactor,Boxx[_]];
b=D[b,{varx,2}]*Timer[pre],
b=b*Timer[prefactor];
];


posdeslash=Flatten[Position[postfactor,LeftPartialSlash[___]]];
posu=Flatten[Position[postfactor,SpinU[__]]];
If[posdeslash!={},
varz=postfactor[[posdeslash[[1]]]][[1]];
ind1=postfactor[[posdeslash[[1]]]][[2]];
ind2=postfactor[[posdeslash[[1]]]][[3]];
exp=b[[Position[b,Exp[_]][[1]]]];
deslash=D[exp,varz]/exp;
momz=deslash/I;
If[momz[[1]]==-1,momz=-momz];
Print[ind1];
pos=Position[b,ind1];
Print[pos];

For[i=1,i<=Length[pos],i++,
Print[Head[b[[pos[[i]][[1]]]]]];
If[Head[b[[pos[[i]][[1]]]]]===Slash,
pos1=pos[[i]]];
];
Print[pos1];

ind=ind1;
inda=ind2;
If[pos1=={},
pos1=Position[b,ind2];
ind=ind2;
inda=ind1;
];
pos1=pos1[[1]];
indb=Complement[{b[[pos1]][[2]],b[[pos1]][[3]]},{ind}][[1]];
Print[indb];
indu=Complement[{inda,indb},{postfactor[[posu[[1]]]][[2]]}][[1]];
Print[indu];
momu=postfactor[[posu[[1]]]][[1]];
Print[b[[pos1]]];
b=b/b[[pos1]]*momz^2;
post=DeleteCases[postfactor,LeftPartialSlash[___]];
post=DeleteCases[post,SpinU[__]];
post1=Product[post[[i]],{i,1,Length[post]}]/(-I);
b=b*post1*SpinU[momu,indu];
];
Return[{b,varspace,varmom,vareiko}];
];



Integrations[amplist_,spaceint_]:=Integrations[amplist,spaceint,{},{}];

Integrations[amplist_,spaceint_,momenta_,eikoint_]:=Block[
{a2a,varint,varmomint,varspace,varmom,vareiko,vareikoint,exponent,omega1,exp1,omegalist,
omega1list,momint,sign,momrep,dot,i},
varint=spaceint;
varmomint=momenta;
a2a=amplist[[1]];
varspace=amplist[[2]];
varmom=amplist[[3]];
vareiko=amplist[[4]];

If[Intersection[varspace,varint]=={},
Print["ERROR!!"];
Return[];
];

exponent=a2a[[Position[a2a,Exp[_]][[1,1]]]][[2]];
Print[exponent];

While[Length[varint]>0,
omega1=Coefficient[exponent,varint[[1]]]/I//FullSimplify;

Print["Integrate on ",varint[[1]]];

exp1=Exp[I*omega1*varint[[1]]];

Print["exp1    ",exp1];
Print["\[Omega]1=  ",omega1];

omegalist=Table[omega1[[j]],{j,1,Length[omega1]}];
omega1list=Table[If[Length[omega1[[j]]]<2,omega1[[j]],-omega1[[j]]],{j,1,Length[omega1]}];

Print[omegalist];
Print[omega1list];


If[varmomint=={},
momint=Intersection[omega1list,varmom][[1]],
momint=varmomint[[1]];
varmomint=DeleteCases[varmomint,momint];
];
sign=Coefficient[omega1,momint];

Print["Integrate on ",momint];
Print[sign];

If[sign==-1,momrep=omega1+momint,momrep=-omega1+momint];

Print[momrep];

a2a=a2a/exp1//Simplify;
a2a=a2a/.momint->momrep;

Print[a2a];

varint=DeleteCases[varint,varint[[1]]];
varmom=DeleteCases[varmom,momint];

Print["varint= ",varint];
Print["varmom= ",varmom];

exponent=Collect[a2a[[Position[a2a,Exp[_]][[1,1]]]][[2]],varint];

Print[exponent,"  ",Length[exponent]];
Print["--------------"];

];

Print["EIKOINT"];

If[eikoint=={},vareikoint=vareiko,
	vareikoint=Intersection[eikoint,vareiko];
	If[vareikoint=={},Print["ERROR"];Return[];];
];

Print["vareikoint= ",vareikoint];

While[vareikoint!={},
	Print[vareikoint[[1]]];
	sign=1;
	dot=Coefficient[exponent,vareikoint[[1]]]/I//FullSimplify;
	If[dot[[1]]==-1,dot=-1*dot;sign=-1];
	Print[dot];
	Print[ScalarP[dot[[1]],dot[[2]]]];
	Print[Exp[I*dot]];
	a2a=a2a/(Exp[I*vareikoint[[1]]dot]*ScalarP[dot[[1]],dot[[2]]])*I*sign;
	vareikoint=DeleteCases[vareikoint,vareikoint[[1]]];
];

If[varmom!={},
	If[vareikoint!={},
		Return[{a2a//FullSimplify,varmom,vareikoint}],
		Return[{a2a//FullSimplify,varmom}]
	],
	If[vareikoint!={},
		Return[{a2a//FullSimplify,vareikoint}],
		Return[{a2a//FullSimplify}]
	];
];

];


End[ ]

EndPackage[ ]
