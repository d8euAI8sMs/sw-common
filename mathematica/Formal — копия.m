(* ::Package:: *)

DD=\[Eth];
DD[_?NumericQ,i_]:=0;
DD[g_^k_,i_]:=k g^(k-1) DD[g^(k-1),i];
DD[x[i_],i_]:=1;
DD[x[j_],i_]:=0;
DD[SSum[g_,r__],i_]:=SSum[DD[g,i],r];
DD[g_+h_,i_]:=DD[g,i]+DD[h,i];
DD[DD[g_,j_],i_]:=DD[g,Flatten[{j,i}]];
DD[g_ h_,i_]:= DD[g,i]h+g DD[h,i];

(*CoUp[g_]:=g;
CoUp[CoUp[g_,c1__],c2__]:=CoUp@@Join[{g},DeleteDuplicates[{c1}~Join~{c2}]];
CoDown[g_]:=g;
CoDown[CoDown[g_,c1__],c2__]:=CoDown@@Join[{g},DeleteDuplicates[{c1}~Join~{c2}]];
CoDown[CoUp[g_,c1__],c2__]:=CoDown@@Join[{CoUp@@Join[{g},Select[{c1},(!MemberQ[{c2},#]&)]]},Select[{c2},(!MemberQ[{c1},#]&)]]/;ContainsAny[{c1},{c2}];
CoUp[CoDown[g_,c1__],c2__]:=CoUp@@Join[{CoDown@@Join[{g},Select[{c1},(!MemberQ[{c2},#]&)]]},Select[{c2},(!MemberQ[{c1},#]&)]]/;ContainsAny[{c1},{c2}];
CoUp[a_ b_,c__]:=CoUp[a,c]CoUp[b,c];
CoDown[a_ b_,c__]:=CoDown[a,c]CoDown[b,c];
CoUp[a_ + b_,c__]:=CoUp[a,c]+CoUp[b,c];
CoDown[a_ + b_,c__]:=CoDown[a,c]+CoDown[b,c];
CoUp[SSum[a_,r__],c__]:=SSum[CoUp[a,c],r];
CoDown[SSum[a_,r__],c__]:=SSum[CoDown[a,c],r];*)

SSum[0,i__]:=0;
SSum[SSum[a_,i__],j__]:=SSum[a,i,j];

USum[x_,v__] := Module[{i,uvars=Unique[ToString/@{v}],umap},umap=Table[{v}[[i]]->uvars[[i]],{i,Length[{v}]}];SSum@@({x/.umap}~Join~uvars)];

GG=\[CapitalGamma];
\[CapitalGamma][g_,i_,k_,l_] := 1/2USum[CoUp[g[i,m],i,m](\[Eth][CoDown[g[m,k],m,k],l]+\[Eth][CoDown[g[m,l],m,l],k]-\[Eth][CoDown[g[k,l],k,l],m]),m];

RR=\[CapitalRHacek];
\[CapitalRHacek][g_,s_,m_,v_,r_] := \[Eth][\[CapitalGamma][g,v,s,r],m]-\[Eth][\[CapitalGamma][g,m,s,r],v]+USum[\[CapitalGamma][g,m,l,r]\[CapitalGamma][g,v,s,l],l]-USum[\[CapitalGamma][g,v,l,r]\[CapitalGamma][g,m,s,l],l];
\[CapitalRHacek][g_,i_,j_] := USum[\[CapitalRHacek][g,i,l,j,l],l];
\[CapitalRHacek][g_] := USum[CoUp[g[i,j],i,j]\[CapitalRHacek][g,i,j],i,j];

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

SSumUniteRuleHelper[a_,b_,r1_,r2_]:=Module[{i,t1,t2,v1,v2,s1,s2,l},
	If[Length[r1]>Length[r2],
	t1=r2;t2=r1;v1=b;v2=a,
	t1=r1;t2=r2;v1=a;v2=b];
	l=Length[t1];
	s1=v1/.Table[t1[[i]]->t2[[i]],{i,Length[t1]}];
	If[Length[t2]==l,s2=v2,s2=SSum@@({v2}~Join~t2[[l+1;;Length[t2]]])];
	SSum@@({s1+s2}~Join~t2[[1;;l]])
];
SSumUniteRules={
	SSum[a_,r1__]SSum[b_,r2__]:>SSum[a b,r1,r2],
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
	vscan[s:SSum[a_,v__]]:=Module[{},vars=vars~Join~{v};vscan[a]];
	vscan[k_ s:SSum[__]]:=Module[{},vscan[k];vscan[s]];
	vscan[a_ + b_]:=Module[{},vscan[a];vscan[b]];
	vscan[a_ b_]:=Module[{},vscan[a];vscan[b]];
	Scan[scan,e,{0,Infinity},Heads->True];
	vscan[e];
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
