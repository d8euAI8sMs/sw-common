(* ::Package:: *)

(* ::Section:: *)
(*\:0418\:043c\:043f\:043e\:0440\:0442 \:0431\:0438\:0431\:043b\:0438\:043e\:0442\:0435\:043a*)


(* ::Section:: *)
(*\:041e\:043f\:0440\:0435\:0434\:0435\:043b\:0435\:043d\:0438\:044f*)


(* ::Input::Initialization:: *)
$globalCache=<||>;
$globalCacheFile=Null;


(* ::Input::Initialization:: *)
Attributes[Intern]={HoldAll};
Intern[key_,val_, c_Function:(False&)]:=With[{t=$globalCache[Hold[key]]},If[MissingQ[t]||!MissingQ[t]&&c[t],With[{v=val},AppendTo[$globalCache,Hold[key]->v]; v], t]];

Attributes[Cached]={HoldAll};
Cached[expr_, c_Function:(False&)]:=With[{x=Extract[Unevaluated[expr],{1}], x0=Extract[Unevaluated[expr],{1},Hold]},With[{c0=Hold[Evaluate@x]===x0},
If[c0||!c0&&c[x],expr;AppendTo[$globalCache,x0->x];x,x]
]
];
Cached[key_,val_, c_Function:(False&)]:=Unevaluated[key]=Intern[key, val,c];

DumpCache[file_String]:=(DumpSave[file, $globalCache];);
DumpCache[]:=If[$globalCacheFile=!=Null,DumpCache[$globalCacheFile]];
RestoreCache[file_String]:=Get[file];
RestoreCache[]:=If[$globalCacheFile=!=Null,RestoreCache[$globalCacheFile]];


(* ::Section::Closed:: *)
(*\:041f\:0440\:0438\:043c\:0435\:0440\:044b \:0438 \:0442\:0435\:0441\:0442\:044b*)


(* ::Text:: *)
(*\:041d\:0430\:043f\:0435\:0447\:0430\:0442\:0430\:0435\:0442 val1 \:043e\:0434\:0438\:043d \:0440\:0430\:0437.*)


(* ::Code:: *)
(*{Cached[var1=Echo[val1]],var1}*)
(*{Cached[var1=Echo[val1]],var1}*)
(*{Cached[var1=Echo[val2]],var1}*)


(* ::Text:: *)
(*\:041d\:0430\:043f\:0435\:0447\:0430\:0442\:0430\:0435\:0442 val1 \:043e\:0434\:0438\:043d \:0440\:0430\:0437.*)


(* ::Code:: *)
(*{Cached[var2=Echo[val1]],var2}*)
(*{Cached[var2=Echo[val2]],var2}*)


(* ::Text:: *)
(*\:041d\:0430\:043f\:0435\:0447\:0430\:0442\:0430\:0435\:0442 \:043e\:0431\:0430 \:0440\:0430\:0437\:0430.*)


(* ::Code:: *)
(*{Cached[var3=Echo[val1]],var3}*)
(*{Cached[var3=Echo[val2],#===val1&],var3}*)
