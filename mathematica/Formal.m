(* ::Package:: *)

(* ::Section:: *)
(*\:0418\:043c\:043f\:043e\:0440\:0442 \:0431\:0438\:0431\:043b\:0438\:043e\:0442\:0435\:043a*)


(* ::Input::Initialization:: *)
If[$FrontEnd =!= Null, AppendTo[$Path, FileNameJoin[{NotebookDirectory[], "."}]]];

(Once@Get[#] &) /@ { "Features.m" }


(* ::Section:: *)
(*\:041e\:043f\:0440\:0435\:0434\:0435\:043b\:0435\:043d\:0438\:044f*)


DD=\[Eth];
DD[_?NumericQ,i_]:=0;
DD[g_^k_,i_]:=k g^(k-1) DD[g^(k-1),i];
DD[x[i_],i_]:=1;
DD[x[j_],i_]:=0;
DD[SSum[g_,r__],i_]:=SSum[DD[g,i],r];
DD[g_+h_,i_]:=DD[g,i]+DD[h,i];
DD[DD[g_,j_],i_]:=DD[g,Flatten[{j,i}]];
DD[g_ h_,i_]:= DD[g,i]h+g DD[h,i];

EnableFeature[Formatter[\[Eth]]]:=Module[{},
	\[Eth]/:Format[\[Eth][g_,{a__}],StandardForm]:=Subscript[g, StringForm[",``",StringJoin[ToString/@{a}]]];
	\[Eth]/:Format[\[Eth][g_,a_],StandardForm]:=Subscript[g, StringForm[",``",a]];
];

Tensor[g_,cont_List,cov_List]:=Tensor[g,Sort[DeleteDuplicates[cont]],Sort[DeleteDuplicates[cov]]]/;!DuplicateFreeQ[cont]||!OrderedQ[cont]||!DuplicateFreeQ[cov]||!OrderedQ[cov];
Tensor[g_,cont_Integer,cov_Integer]:=Tensor[g,Range[1,cont],Range[cont+1,cont+cov]];
Tensor[g_,cont_Integer]:=Tensor[g,cont,0];

TensorCov[Tensor[g_,cont_,cov_],a__]:=Tensor[g,Select[cont,(!MemberQ[{a},#]&)],cov~Join~{a}]/;ContainsAll[cont~Join~cov,{a}];
TensorCov[Tensor[g_,cont_,cov_]]:=Tensor[g,{},cont~Join~cov];
TensorCov[expr_,a___]:=expr/.{t:Tensor[__]:>TensorCov[t,a]};

TensorContr[Tensor[g_,cont_,cov_],a__]:=Tensor[g,cont~Join~{a},Select[cov,(!MemberQ[{a},#]&)]]/;ContainsAll[cont~Join~cov,{a}];
TensorContr[Tensor[g_,cont_,cov_]]:=Tensor[g,cont~Join~cov,{}];
TensorContr[expr_,a___]:=expr/.{t:Tensor[__]:>TensorContr[t,a]};

EnableFeature[Formatter[Tensor]]:=Module[{},
	Tensor/:Format[Tensor[g_,cont_,cov_][idx__],StandardForm]:=Module[{gu,gd,t,f},
		gu="";gd="";
		Do[gu=StringJoin[{gu,ToString[{idx}[[v]]]}],{v,cont}];
		Do[gd=StringJoin[{gd,ToString[{idx}[[v]]]}],{v,cov}];
		f=If[AtomQ[g],ToString[g],StringForm["(``)",g]];
		
\!\(\*SubsuperscriptBox[\(f\), \(gd\), \(gu\)]\)
	]/;Length[cont]+Length[cov]==Length[{idx}];

	Tensor/:Format[Tensor[g_,cont_,cov_],StandardForm]:=Module[{gu,gd,t,f},
		gu="";gd="";
		Do[gu=StringJoin[{"\[Bullet]",gu}],{v,cont}];
		Do[gd=StringJoin[{"\[Bullet]",gd}],{v,cov}];
		f=If[AtomQ[g],ToString[g],StringForm["(``)",g]];
		
\!\(\*SubsuperscriptBox[\(f\), \(gd\), \(gu\)]\)
	];
];

SSum[0,i__]:=0;
SSum[SSum[a_,i__],j__]:=SSum[a,i,j];

USum[x_,v__] := Module[{i,uvars=Unique[ToString/@{v}],umap},umap=Table[{v}[[i]]->uvars[[i]],{i,Length[{v}]}];SSum@@({x/.umap}~Join~uvars)];

GG=\[CapitalGamma];
\[CapitalGamma][g_,i_,k_,l_] := 1/2Module[{m},USum[g[i,m](\[Eth][TensorCov[g][m,k],l]+\[Eth][TensorCov[g][m,l],k]-\[Eth][TensorCov[g][k,l],m]),m]];

RR=\[CapitalRHacek];
\[CapitalRHacek][g_,r_,s_,m_,v_] := Module[{l},\[Eth][\[CapitalGamma][g,r,v,s],m]-\[Eth][\[CapitalGamma][g,r,m,s],v]+USum[\[CapitalGamma][g,r,m,l]\[CapitalGamma][g,l,v,s],l]-USum[\[CapitalGamma][g,r,v,l]\[CapitalGamma][g,l,m,s],l]];
\[CapitalRHacek][g_,i_,j_] := Module[{l},USum[\[CapitalRHacek][g,l,i,l,j],l]];
\[CapitalRHacek][g_] := Module[{i,j},USum[g[i,j]\[CapitalRHacek][g,i,j],i,j]];

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

SSumUniteRuleHelper[a_,b_,r1_,r2_]:=Module[{i,t1,t2,v1,v2,s1,s2,l,r},
	If[Length[r1]>Length[r2],
	t1=r2;t2=r1;v1=b;v2=a,
	t1=r1;t2=r2;v1=a;v2=b];
	l=Length[t1];
	s1=v1/.Table[t1[[i]]->t2[[i]],{i,Length[t1]}];
	If[Length[t2]==l,s2=v2,s2=SSum@@({v2}~Join~t2[[l+1;;Length[t2]]])];
	SSum@@({s1+s2}~Join~t2[[1;;l]])
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

TensorMapHelper[e_,r_] := r[e];
TensorMapHelper[a_ + b_,r_] := TensorMapHelper[a,r]+TensorMapHelper[b,r];
TensorMapHelper[SSum[e_,l__],r_] := SSum[TensorMapHelper[e,r],l];
TensorMapHelper[k_ e:SSum[__],r_] := TensorMapHelper[k,r] TensorMapHelper[e,r];
TensorMap[e_,r_] := Module[{t=e,t0=0},While[t=!=t0,t0=t;t=TensorMapHelper[t,r]];t];
TensorReplaceAll[e_,r_] := TensorMap[e,(#/.r &)];
