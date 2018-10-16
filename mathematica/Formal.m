(* ::Package:: *)

(* ::Section:: *)
(*\:0418\:043c\:043f\:043e\:0440\:0442 \:0431\:0438\:0431\:043b\:0438\:043e\:0442\:0435\:043a*)


(* ::Input::Initialization:: *)
If[$FrontEnd =!= Null, AppendTo[$Path, FileNameJoin[{NotebookDirectory[], "."}]]];

(Once@Get[#] &) /@ { "Features.m" }


(* ::Section:: *)
(*\:041e\:043f\:0440\:0435\:0434\:0435\:043b\:0435\:043d\:0438\:044f*)


DD=\[Eth];
DD[_?NumberQ,i__]:=0;
DD[SSum[g_,r__],i__]:=SSum[DD[g,i],r];
DD[g_ +h_,i__]:=DD[g,i]+DD[h,i];
DD[DD[g_,j__],i__]:=DD[g,j,i];
DD[g_ h_,i_,j__]:= DD[DD[g,i]h+g DD[h,i],j];
DD[g_ h_,i_]:= DD[g,i]h+g DD[h,i];

DD2DRules=\[Eth]2DRules;
\[Eth]2DRules[v_]:={DD[a_,i__]:>D@@Join[{a},(v[[#+1]]&)/@{i}]};

EnableFeature[Formatter[\[Eth]]]:=Module[{},
	\[Eth]/:MakeBoxes[\[Eth][g_,a__Integer],StandardForm]:=Module[{},
		SubscriptBox[ToBoxes[g],ToBoxes[","~StringJoin~(ToString/@{a})]]
	];
	\[Eth]/:MakeBoxes[\[Eth][g_,a__],StandardForm]:=Module[{},
		SubscriptBox[ToBoxes[g],RowBox[{","}~Join~Table[ToBoxes[$t],{$t,{a}}]]]
	];
];

Tensor[g_,cont_List,cov_List]:=Tensor[g,Sort[DeleteDuplicates[cont]],Sort[DeleteDuplicates[cov]]]/;!DuplicateFreeQ[cont]||!OrderedQ[cont]||!DuplicateFreeQ[cov]||!OrderedQ[cov];
Tensor[g_,cont_Integer,cov_Integer]:=Tensor[g,Range[1,cont],Range[cont+1,cont+cov]];
Tensor[g_,cont_Integer]:=Tensor[g,cont,0];

TensorDeltaSymbol=\[Delta];
TensorLeviCivitaSymbol=\[Epsilon];

TensorDelta[cont_:1,cov_:1]:=Tensor[TensorDeltaSymbol,cont,cov];
TensorDeltaValue[i_,j_]:=If[i==j,1,0];

TensorLeviCivita3[cont_:3,cov_:0]:=Tensor[TensorLeviCivitaSymbol,cont,cov];
TensorLeviCivita3Value[i_,j_,k_]:=LeviCivitaTensor[3][[i,j,k]];

TensorCov[Tensor[g_,cont_,cov_],a__]:=Tensor[g,Select[cont,(!MemberQ[{a},#]&)],cov~Join~{a}]/;ContainsAll[cont~Join~cov,{a}];
TensorCov[Tensor[g_,cont_,cov_]]:=Tensor[g,{},cont~Join~cov];
TensorCov[expr_,a___]:=expr/.{t:Tensor[__]:>TensorCov[t,a]};

TensorContr[Tensor[g_,cont_,cov_],a__]:=Tensor[g,cont~Join~{a},Select[cov,(!MemberQ[{a},#]&)]]/;ContainsAll[cont~Join~cov,{a}];
TensorContr[Tensor[g_,cont_,cov_]]:=Tensor[g,cont~Join~cov,{}];
TensorContr[expr_,a___]:=expr/.{t:Tensor[__]:>TensorContr[t,a]};

TensorSymbol[Tensor[g_,__]]:=g;
TensorDims[Tensor[g_,cont_,cov_]]:={Length[cont],Length[cov]};
TensorLength[Tensor[g_,cont_,cov_]]:=Length[cont]+Length[cov];
TensorCovQ[Tensor[g_,cont_,cov_]]:=Length[cont]==0;
TensorContQ[Tensor[g_,cont_,cov_]]:=Length[cov]==0;
TensorCovQ[Tensor[g_,cont_,cov_],i_]:=MemberQ[cov,i];
TensorContQ[Tensor[g_,cont_,cov_],i_]:=MemberQ[cont,i];
TensorQAlt[Tensor[g_Symbol,cont_,cov_]]:=True;
TensorQAlt[t_]:=False;
TensorQAlt[t_,g_Symbol]:=TensorQAlt[t]&&TensorSymbol[t]===g;
TensorQAlt[t_,g_Symbol,l_Integer]:=TensorQAlt[t,g]&&TensorLength[t]==l;
TensorQAlt[t_,l_Integer]:=TensorQAlt[t]&&TensorLength[t]==l;

EnableFeature[Formatter[Tensor]]:=Module[{$fmt,$v},
	$fmt[a_,idx__Integer]:=ToBoxes[StringJoin@Table[ToString[{idx}[[a[[$v]]]]],{$v,Length[a]}]];
	$fmt[a_,idx__]:=RowBox[Table[ToBoxes[{idx}[[a[[$v]]]]],{$v,Length[a]}]];
	Tensor/:MakeBoxes[Tensor[g_,cont_,cov_][idx__],StandardForm]:=Module[{},
		SubsuperscriptBox[If[AtomQ[g],ToBoxes[g],RowBox[{"(",ToBoxes[g],")"}]],$fmt[cov,idx],$fmt[cont,idx]]
	];
	Tensor/:MakeBoxes[Tensor[g_,cont_,cov_],StandardForm]:=Module[{},
		SubsuperscriptBox[If[AtomQ[g],ToBoxes[g],RowBox[{"(",ToBoxes[g],")"}]],RowBox[Table["\[Bullet]",Length[cov]]],RowBox[Table["\[Bullet]",Length[cont]]]]
	];
];

SSum[0,i__]:=0;
SSum[SSum[a_,i__],j__]:=SSum[a,i,j];

SSum2SumRules[imapper_]:={SSum[a_,v__]:>Sum@@Join[{a},imapper/@{v}]};

USum[x_,v__] := Module[{i,uvars=Unique[ToString/@{v}],umap},umap=Table[{v}[[i]]->uvars[[i]],{i,Length[{v}]}];SSum@@({x/.umap}~Join~uvars)];

GG=\[CapitalGamma];
\[CapitalGamma][g_,i_,k_,l_] := 1/2Module[{m},USum[g[i,m](\[Eth][TensorCov[g][m,k],l]+\[Eth][TensorCov[g][m,l],k]-\[Eth][TensorCov[g][k,l],m]),m]];

RR=\[CapitalRHacek];
\[CapitalRHacek][g_,r_,s_,m_,v_] := \[Eth][\[CapitalGamma][g,r,v,s],m]-\[Eth][\[CapitalGamma][g,r,m,s],v]+Module[{l},USum[\[CapitalGamma][g,r,m,l]\[CapitalGamma][g,l,v,s]-\[CapitalGamma][g,r,v,l]\[CapitalGamma][g,l,m,s],l]];
\[CapitalRHacek][g_,i_,j_] := Module[{l},USum[\[CapitalRHacek][g,l,i,l,j],l]];
\[CapitalRHacek][g_] := Module[{i,j},USum[g[i,j]\[CapitalRHacek][g,i,j],i,j]];

TensorBr[g_?(TensorQAlt[#,2]&&TensorCovQ[#]&)][i_,j_]:=Module[{k,l,m,n},SSum[TensorLeviCivita3[][i,l,k]TensorLeviCivita3[][j,n,m]\[Eth][g[l,n],k,m],l,k,n,m]];
TensorSr[g_?(TensorQAlt[#,2]&&TensorCovQ[#]&)][i_,m_]:=Module[{k,l},SSum[TensorLeviCivita3[][i,k,l]\[Eth][g[m,k],l],k,l]];

SSum/:MakeBoxes[SSum[x_,r__],StandardForm]:=Module[{i,t,ssym},
	t=RowBox[{}];
	ssym[{v_,v0_,v1_}]:=UnderoverscriptBox[StyleBox["S",Large],RowBox[{ToBoxes[v,StandardForm],"=",ToBoxes[v0]}],ToBoxes[v1]];
	ssym[v_]:=UnderscriptBox[StyleBox["S",Large],ToBoxes[v]];
	RowBox[Table[ssym[v],{v,{r}}]~Join~{RowBox[{"(",ToBoxes[x],")"}]}]
];

MakeExpressionSsumHelper[x0_,m___]:=Module[{s,t},
	s[{UnderoverscriptBox["S",RowBox[{a0_,"=",b0_}],c0_],x2__}]:=Module[{},s[{x2}]~Join~{{ToExpression[a0],ToExpression[b0],ToExpression[c0]}, ","}];
	s[{UnderscriptBox["S",a0_],x2__}]:=Module[{},s[{x2}]~Join~{ToExpression[a0], ","}];
	s[{r_}]:={r};
	t=s[x0];
	MakeExpression[RowBox[{m,"SSum","[",First@t,","}~Join~t[[2;;Length[t]-1]]~Join~{"]"}],StandardForm]
];
MakeExpression[RowBox[x0:{m___,UnderoverscriptBox["S",RowBox[{_,"=",_}],_],__}],StandardForm]:=MakeExpressionSsumHelper[x0[[Length[{m}]+1;;Length[x0]]],m];
MakeExpression[RowBox[x0:{m___,UnderscriptBox["S",_],__}],StandardForm]:=MakeExpressionSsumHelper[x0[[Length[{m}]+1;;Length[x0]]],m];

SSumUniteRuleHelper[a_,b_,r1_,r2_]:=Module[{i,t1,t2,tu,v1,v2,s1,s2,l,r},
	If[Length[r1]>Length[r2],
	t1=r2;t2=r1;v1=b;v2=a,
	t1=r1;t2=r2;v1=a;v2=b];
	l=Length[t1];
	tu=Table[Unique["i"],Length[t1]];
	s1=v1/.Table[t1[[i]]->tu[[i]],{i,Length[t1]}];
	v2=v2/.Table[t2[[i]]->tu[[i]],{i,Length[t1]}];
	If[Length[t2]==l,s2=v2,s2=SSum@@({v2}~Join~t2[[l+1;;Length[t2]]])];
	SSum@@({s1+s2}~Join~tu[[1;;l]])
];
SSumUniteRules={
	SSum[a_,r1__]SSum[b_,r2__]:>Module[{t1=Table[Unique["i"],Length[{r1}]],t2=Table[Unique["i"],Length[{r2}]],v},SSum[(a/.Table[{r1}[[v]]->t1[[v]],{v,Length[{r1}]}]) (b/.Table[{r2}[[v]]->t2[[v]],{v,Length[{r2}]}]),t1,t2]],
	k_ SSum[a_,r1__]+ SSum[b_,r2__]:>SSumUniteRuleHelper[k a,b,{r1},{r2}],
	SSum[a_,r1__]+ k_ SSum[b_,r2__]:>SSumUniteRuleHelper[a,k b,{r1},{r2}],
	k1_ SSum[a_,r1__]+ k2_ SSum[b_,r2__]:>SSumUniteRuleHelper[k1 a,k2 b,{r1},{r2}],
	SSum[a_,r1__]+ SSum[b_,r2__]:>SSumUniteRuleHelper[a,b,{r1},{r2}],
	k_ SSum[a_,r__]:>SSum[k a,r],
	SSum[a_,r__]k_:>SSum[k a,r]
};

Tensorify[e_,r_:SSumUniteRules] := Module[{t=e,t0=0},While[t=!=t0,t0=t;t=ExpandAll[(t//.r)]];t];

TensorBeautify[e_] := Module[{abc,abc0,vars={},scan,vscan},
	abc0=abc={i,j,k,l,m,n,s,t,a,b,c,u,v,\[Alpha],\[Beta],\[Gamma],\[Rho],\[Mu],\[Nu],\[Chi]};
	scan[e0_]:=abc=Select[abc,(#=!=e0 &)];
	vscan={SSum[a_,v__]:>Module[{},vars=vars~Join~{v};a/.vscan;]};
	Scan[scan,e,{0,Infinity},Heads->True];
	e/.vscan;
	vars=DeleteDuplicates[vars];
	vars=Select[vars,(!MemberQ[abc0,#]&)];
	vars=Take[vars,Min[Length[abc],Length[vars]]];
	e/.Table[vars[[idx]]->abc[[idx]],{idx,Length[vars]}]
];

TensorMapHelper[idx_,Plus[a_,b__],r_] := Plus@@((TensorMapHelper[idx,#,r]&)/@{a,b});
TensorMapHelper[idx_,SSum[e_,l__],r_] := SSum[TensorMapHelper[idx~Join~{l},e,r],l];
TensorMapHelper[idx_,k_ e:SSum[__],r_] := TensorMapHelper[idx,k,r] TensorMapHelper[idx,e,r];
TensorMapHelper[idx_,k1_ e:SSum[__] k2_,r_] := TensorMapHelper[idx,k1,r] TensorMapHelper[idx,e,r] TensorMapHelper[idx,k2,r];
TensorMapHelper[idx_,e_,r_] := r[e,idx];
TensorMap[e_,r_] := Module[{t=e,t0=0},While[t=!=t0,t0=t;t=TensorMapHelper[{},t,r]];t];
TensorReplaceAll[e_,r_] := TensorMap[e,(#/.r &)];
TensorReplaceRepeated[e_,r_] := TensorMap[e,(#//.r &)];

(*
	\:0423\:043f\:0440\:043e\:0441\:0442\:0438\:0442\:0435\:043b\:044c \:0432\:044b\:0440\:0430\:0436\:0435\:043d\:0438\:0439. \:0420\:0430\:0441\:0441\:043c\:0430\:0442\:0440\:0438\:0432\:0430\:0435\:0442 \:043a\:0430\:0436\:0434\:043e\:0435 \:0432\:0441\:0442\:0440\:0435\:0447\:0435\:043d\:043d\:043e\:0435 \:0442\:0435\:043d\:0437\:043e\:0440\:043d\:043e\:0435 \:043f\:0440\:043e\:0438\:0437\:0432\:0435\:0434\:0435\:043d\:0438\:0435
	\:0432 \:043a\:043e\:043d\:0442\:0435\:043a\:0441\:0442\:0435 \:043e\:0442\:0434\:0435\:043b\:044c\:043d\:043e\:0439 \:0441\:0443\:043c\:043c\:044b. \:041d\:0430\:043f\:0440. Sum[a[i,j]b[j,k]+c[i,j]d[j,k],j] \:0440\:0430\:0441\:043f\:0430\:0434\:0430\:0435\:0442\:0441\:044f
	\:043d\:0430 Sum[a[i,j]b[j,k],j]+Sum[c[i,j]d[j,k],j]. \:042d\:0442\:043e \:043f\:043e\:0437\:0432\:043e\:043b\:044f\:0435\:0442 \:043f\:0440\:043e\:0438\:0437\:0432\:043e\:0434\:0438\:0442\:044c \:0443\:043f\:0440\:043e\:0449\:0435\:043d\:0438\:044f
	\:043d\:0430 \:0443\:0440\:043e\:0432\:043d\:0435 \:0441\:0443\:043c\:043c, \:0443\:043d\:0438\:0447\:0442\:043e\:0436\:0430\:0442\:044c \:043d\:0435\:043d\:0443\:0436\:043d\:044b\:0435 \:043f\:0440\:043e\:043c\:0435\:0436\:0443\:0442\:043e\:0447\:043d\:044b\:0435 \:0441\:0443\:043c\:043c\:044b.
	
	\:041f\:0440\:043e\:043a\:0438\:043d\:0443\:0442\:044b\:0439 \:0447\:0435\:0440\:0435\:0437 Sow[i] \:0438\:043d\:0434\:0435\:043a\:0441 \:0431\:0443\:0434\:0435\:0442 \:0443\:043d\:0438\:0447\:0442\:043e\:0436\:0435\:043d. \:041d\:0430\:043f\:0440\:0438\:043c\:0435\:0440
		expr=Sum[g[i,j]G[j,k],j] (=delta[i,k])
	\:043c\:043e\:0436\:043d\:043e \:0443\:043f\:0440\:043e\:0441\:0442\:0438\:0442\:044c \:0442\:0430\:043a:
		TensorSimplify[expr,(#/.{g[i_,j_]G[j_,k_]\[RuleDelayed](Sow[j];delta[i,k])}&)]
	\:0422\:043e\:0433\:0434\:0430 \:0441\:0443\:043c\:043c\:0430 \:043f\:043e j \:0431\:0443\:0434\:0435\:0442 \:0443\:0441\:0442\:0440\:0430\:043d\:0435\:043d\:0430.
 *)
TensorSimplifyDeltaMapper[e_,idx_]:=(e//.{
	k_ x:Tensor[TensorDeltaSymbol,a__][i_,j_]:>If[MemberQ[idx,i],Sow[i];(k/.i->j),
		If[MemberQ[idx,j],Sow[j];(k/.j->i),k x]
	],
	Tensor[TensorDeltaSymbol,a__][i_,j_]:>If[MemberQ[idx,i],Sow[i];1,If[MemberQ[idx,j],Sow[j];1]]
});
TensorSimplifyMetricsMapper[t:Tensor[_,0,2]][e_,idx_]:=(e//.{
	t[a_,b_]TensorContr[t][b_,c_]:>(Sow[b];TensorDelta[c,a]),
	t[a_,b_]TensorContr[t][c_,b_]:>(Sow[b];TensorDelta[c,a]),
	t[b_,a_]TensorContr[t][b_,c_]:>(Sow[b];TensorDelta[c,a]),
	t[b_,a_]TensorContr[t][c_,b_]:>(Sow[b];TensorDelta[c,a])
});
TensorSimplifyHelper[idx_,Plus[a_,b__],r_] := Plus@@((TensorSimplifyHelper[idx,#,r]&)/@{a,b});
TensorSimplifyHelper[idx_,SSum[e_,l__],r_] := TensorSimplifyHelper[idx~Join~{l},e,r];
TensorSimplifyHelper[idx_,k_ e:SSum[__],r_] := TensorSimplifyHelper[idx,k,r] TensorSimplifyHelper[idx,e,r];
TensorSimplifyHelper[idx_,k1_ e:SSum[__] k2_,r_] := TensorSimplifyHelper[idx,k1,r] TensorSimplifyHelper[idx,e,r] TensorSimplifyHelper[idx,k2,r];
TensorSimplifyHelper[idx_,e_,r_] := If[idx=={},e,Module[{t,fi},
	t=Reap[r[e,idx]];
	If[Last@t=={},Return[SSum@@Join[{e},idx]]];
	fi=Select[idx,(!MemberQ[Last@Last@t,#]&)];
	If[fi=={},First@t,SSum@@Join[{First@t},fi]]
]];
TensorSimplify[e_,r__:TensorSimplifyDeltaMapper] := Module[{t=e,t0=0,s,o},While[t=!=t0,t0=t;t=TensorSimplifyHelper[{},t,((s=#1;Do[s=o[s,#2],{o,{r}}];s)&)]];t];

TopoSortCanPermutate[l_,{i_,j_},p_]:=Module[{pi},
	Catch[Do[If[First[pi]==i&&Last[pi]==j||First[pi]==j&&Last[pi]==i||First[pi]!=i&&Last[pi]!=j&&First[pi]!=j&&Last[pi]!=i&&(l[[First[pi]]]===l[[i]]&&l[[Last[pi]]]===l[[j]]||l[[First[pi]]]===l[[j]]&&l[[Last[pi]]]===l[[i]]),Throw[True]],{pi,p}];False]];

TopoSort[l_,p_,c_]:=Module[{l0,l1,t,i,j,pi,p0},
	l0={};
	l1=l;
	While[l0=!=l1,
		l0=l1;
		Do[
			Do[
				If[TopoSortCanPermutate[l1,{i,j},p]&&c[l1[[i]],l1[[j]]]>0,
					t=l1[[i]];l1[[i]]=l1[[j]];l1[[j]]=t;Break[]
				]
			,{j,i+1,Length[l]}]
		,{i,Length[l]}]
	];
	l1
];

TopoSortInv[l_,p_,c_,vars_]:=Module[{ls,l0,r1,r2,l1,l2},
	ls=TopoSort[l,p,c];
	l0=DeleteDuplicates[ls];
	l0=Select[l0,(MemberQ[vars,#]&)];
	l1=Sort[l0,(AlphabeticOrder[ToString[#1],ToString[#2]]>0&)];
	l2=Table[Unique["i"],Length[l1]];
	r1=AssociationThread[l0->l2];
	r2=AssociationThread[l2->l1];
	ls/.r1/.r2
];

(*
	\:0421\:0438\:043c\:043c\:0435\:0442\:0440\:0438\:0437\:0430\:0446\:0438\:044f \:0432\:0441\:0435\:0445 \:0442\:0435\:043d\:0437\:043e\:0440\:043e\:0432.
	\:0417\:0434\:0435\:0441\:044c \:0441\:0447\:0438\:0442\:0430\:0435\:043c, \:0447\:0442\:043e \:0432\:0441\:0435 \:0432\:043e\:0437\:043c\:043e\:0436\:043d\:044b\:0435 \:0432\:044b\:0440\:0430\:0436\:0435\:043d\:0438\:044f -- \:0442\:0435\:043d\:0437\:043e\:0440\:044b \:0440\:0430\:043d\:0433\:0430 2
	\:0438 \:043e\:0431\:044b\:0447\:043d\:044b\:0435 \:043f\:0440\:043e\:0438\:0437\:0432\:043e\:0434\:043d\:044b\:0435 \:0442\:0435\:043d\:0437\:043e\:0440\:043e\:0432 \:043f\:0440\:043e\:0438\:0437\:0432\:043e\:043b\:044c\:043d\:043e\:0433\:043e \:043f\:043e\:0440\:044f\:0434\:043a\:0430.
	\:041f\:043e\:043b\:0435\:0437\:043d\:043e \:043f\:0440\:0438 \:0440\:0430\:0431\:043e\:0442\:0435 \:0441 \:043c\:0435\:0442\:0440\:0438\:043a\:0430\:043c\:0438.
 *)
Tensor2TopoSortMapper[e_,vars_]:=Tensor2TopoSortMapper[(True&)][e,vars];
Tensor2TopoSortMapper[symQ_][e_,vars_]:=Module[{ic,ia,n,ni,r1,r2,r0},
	r1={};r2={};
	n=1;
	ic[x:\[Eth][a_,k__]]:=Module[{},
		ic[a];
		(AppendTo[r1,#]&)/@{k};
		If[symQ[x],(AppendTo[r2,#]&)/@Permutations[Table[ni,{ni,n,n+Length[{k}]-1}],{2}]];
		n+=Length[{k}]];
	ic[x:Tensor[a__][i_,j_]]:=Module[{},
		(AppendTo[r1,#]&)/@{i,j};
		(AppendTo[r2,#]&)/@{{n,n+1}};
		n+=2]/;symQ[x];
	ic[Tensor[a__][ij__]]:=Module[{},
		(AppendTo[r1,#]&)/@{ij};
		n+=Length[{ij}]];
	ic[a_ b_]:=Module[{},ic[a];ic[b]];
	ic[e];
	r0=TopoSortInv[r1,r2,(-AlphabeticOrder[ToString[#1],ToString[#2]]&),vars];
	n=1;
	ia[\[Eth][a_,k__]]:=Module[{y},
	y=\[Eth]@@Join[{ia[a]},r0[[n;;n+Length[{k}]-1]]];
	n+=Length[{k}];y];
	ia[Tensor[a__][ij__]]:=Module[{y},
		y=Tensor[a]@@r0[[n;;n+Length[{ij}]-1]];
		n+=Length[{ij}];y];
	ia[a_ b_]:=Module[{},ia[a]ia[b]];
	ia[a_]:=a;
	ia[e]
];
