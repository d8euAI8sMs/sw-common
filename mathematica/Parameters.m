(* ::Package:: *)

(* ::Section:: *)
(*\:0418\:043c\:043f\:043e\:0440\:0442 \:0431\:0438\:0431\:043b\:0438\:043e\:0442\:0435\:043a*)


(* ::Section::Closed:: *)
(*\:041e\:043f\:0440\:0435\:0434\:0435\:043b\:0435\:043d\:0438\:044f*)


(* ::Input::Initialization:: *)
Parameterize[v_,p_Association:<||>]:=Module[{p1},
	p1=Reap[v//.Parameterized[x_,y_]:>(Sow[y];x)];
	If[Last@p1=={},Parameterized[First@p1,p],
		Parameterized[First@p1,Join[Join@@First@Last@p1,p]]
	]
];
Parameterize[v_,kv__]:=Parameterize[v,<|kv|>];

ResolveParameterized[Parameterized[v_,p_]]:=Parameterized[v,ResolveParameterized[p]];
ResolveParameterized[p_Association]:=Module[{kv,k,v,v0,sr,vs,p0,sr0,a},
	sr[e_]:=Reap[e/.x_ :>(Sow[x];x)/;MemberQ[Keys[p],x]];
	kv=KeyValueMap[Function[{k,v},
		sr0=Last@sr[v];
		If[sr0==={},{},Table[k->v0,{v0,First@sr0}]]
	],p]//Flatten[#,1]&;
	vs=TopologicalSort[Graph[Keys[p],kv]]//Reverse;
	p0=p;
	Do[p0[vs[[v]]]=p0[vs[[v]]]/.p0,{v,Length[vs]}];
	p0
];

Decay[Parameterized[v_,p_]]:=v/.ResolveParameterized[p];
Decay[Parameterized[_,p_],{All}]:=ResolveParameterized[p];
Decay[Parameterized[v_,p_],{Full}]:={v/.ResolveParameterized[p],ResolveParameterized[p]};
Decay[Parameterized[_,p_],k_List]:=<|(#->ResolveParameterized[p][#]&/@k)|>//DeleteMissing;
Decay[Parameterized[_,p_],k_]:=ResolveParameterized[p][k];
Decay[e_]:=Decay[Parameterize[e]];
Decay[e_,k_]:=Decay[Parameterize[e],k];

DecayOp[p_]:=Function[{v},Decay[v,p]];


(* ::Section::Closed:: *)
(*\:041f\:0440\:0438\:043c\:0435\:0440\:044b \:0438 \:0442\:0435\:0441\:0442\:044b*)


(* ::Code:: *)
(*tests={*)
(*	Parameterize[k x + b],*)
(*	Parameterize[k x + b, k->1/b],*)
(*	Parameterize[k x + b, s->31, k->1/b, b->1/s]*)
(*}*)
(**)
(*{*)
(*	tests[[1]]//Parameterize[#, k->1/b]&,*)
(*	tests[[2]]//Parameterize[#, k->b]&,*)
(*	tests[[3]]//Parameterize[#, z->v]&*)
(*}*)
(**)
(*{*)
(*	tests[[1]]//Decay,*)
(*	tests[[2]]//Decay,*)
(*	tests[[3]]//Decay*)
(*}*)
(*tests//Decay*)
(**)
(*{*)
(*	tests[[2]]//DecayOp[k],*)
(*	tests[[2]]//DecayOp[b],*)
(*	tests[[2]]//DecayOp[{k,b}],*)
(*	tests[[3]]//DecayOp[{k,b}]*)
(*}*)
(*tests//DecayOp[{Full}]*)



