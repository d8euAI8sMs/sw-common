(* ::Package:: *)

(* ::Section:: *)
(*\:0418\:043c\:043f\:043e\:0440\:0442 \:0431\:0438\:0431\:043b\:0438\:043e\:0442\:0435\:043a*)


(* ::Section:: *)
(*\:041e\:043f\:0440\:0435\:0434\:0435\:043b\:0435\:043d\:0438\:044f*)


(* ::Input::Initialization:: *)
SetAttributes[Intern,HoldAll];
Intern[x_,v_]:=(x=v)/;!ValueQ[x];
Intern[x_,v_]:=x/;ValueQ[x];
Intern[x_,v_,c_]:=(x=v)/;!ValueQ[x];
Intern[x_,v_,c_]:=If[!c[x],x,x=v]/;ValueQ[x];


(* ::Input::Initialization:: *)
SetAttributes[Cache,HoldFirst];
Cache[expr_,c_:(False&)]:=
With[{x=Extract[Unevaluated[expr],{1}]},
With[{c0=Hold[Evaluate@x]===Extract[Unevaluated[expr],{1},Hold]},
If[c0||!c0&&c[x],expr,x]
]
];


(* ::Section::Closed:: *)
(*\:041f\:0440\:0438\:043c\:0435\:0440\:044b \:0438 \:0442\:0435\:0441\:0442\:044b*)


(* ::Text:: *)
(*\:041d\:0430\:043f\:0435\:0447\:0430\:0442\:0430\:0435\:0442 val1 \:043e\:0434\:0438\:043d \:0440\:0430\:0437.*)


(* ::Code:: *)
(*{Intern[var1,Echo[val1]],var1}*)
(*{Intern[var1,Echo[val1]],var1}*)
(*{Intern[var1,Echo[val2]],var1}*)


(* ::Text:: *)
(*\:041d\:0430\:043f\:0435\:0447\:0430\:0442\:0430\:0435\:0442 val1 \:043e\:0434\:0438\:043d \:0440\:0430\:0437.*)


(* ::Code:: *)
(*{Intern[var2,Echo[val1]],var2}*)
(*{Intern[var2,Echo[val2]],var2}*)


(* ::Text:: *)
(*\:041d\:0430\:043f\:0435\:0447\:0430\:0442\:0430\:0435\:0442 \:043e\:0431\:0430 \:0440\:0430\:0437\:0430.*)


(* ::Code:: *)
(*{Intern[var3,Echo[val1]],var3}*)
(*{Intern[var3,Echo[val2],#===val1&],var3}*)


(* ::Text:: *)
(*\:041d\:0430\:043f\:0435\:0447\:0430\:0442\:0430\:0435\:0442 val1 \:043e\:0434\:0438\:043d \:0440\:0430\:0437.*)


(* ::Code:: *)
(*{Cache[var1=Echo[val1]],var1}*)
(*{Cache[var1=Echo[val1]],var1}*)
(*{Cache[var1=Echo[val2]],var1}*)


(* ::Text:: *)
(*\:041d\:0430\:043f\:0435\:0447\:0430\:0442\:0430\:0435\:0442 val1 \:043e\:0434\:0438\:043d \:0440\:0430\:0437.*)


(* ::Code:: *)
(*{Cache[var2=Echo[val1]],var2}*)
(*{Cache[var2=Echo[val2]],var2}*)


(* ::Text:: *)
(*\:041d\:0430\:043f\:0435\:0447\:0430\:0442\:0430\:0435\:0442 \:043e\:0431\:0430 \:0440\:0430\:0437\:0430.*)


(* ::Code:: *)
(*{Cache[var3=Echo[val1]],var3}*)
(*{Cache[var3=Echo[val2],#===val1&],var3}*)
