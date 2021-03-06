(* ::Package:: *)

(* ::Section::Closed:: *)
(*\:0418\:043c\:043f\:043e\:0440\:0442 \:0431\:0438\:0431\:043b\:0438\:043e\:0442\:0435\:043a*)


(* ::Input::Initialization:: *)
If[$FrontEnd =!= Null, AppendTo[$Path, FileNameJoin[{NotebookDirectory[], "."}]]];

(Once@Get[#] &) /@ { "Riemannian.m" };


(* ::Section:: *)
(*\:0412\:0441\:043f\:043e\:043c\:043e\:0433\:0430\:0442\:0435\:043b\:044c\:043d\:044b\:0435 \:0444\:0443\:043d\:043a\:0446\:0438\:0438*)


(* ::Section:: *)
(*\:0412\:044b\:0447\:0438\:0441\:043b\:0435\:043d\:0438\:044f*)


(* ::Subsection::Closed:: *)
(*\:041f\:043e\:043b\:044f \:041a\:0438\:043b\:043b\:0438\:043d\:0433\:0430 \:0442\:0440\:0435\:0445\:043c\:0435\:0440\:043d\:043e\:0433\:043e \:0435\:0432\:043a\:043b\:0438\:0434\:043e\:0432\:0430 \:043f\:0440\:043e\:0441\:0442\:0440\:0430\:043d\:0441\:0442\:0432\:0430*)


(* ::Text:: *)
(*\:0414\:0435\:043a\:0430\:0440\:0442\:043e\:0432\:044b \:043a\:043e\:043e\:0440\:0434\:0438\:043d\:0430\:0442\:044b*)


killingDec = { nDec, lDec } =
{
	(* \:0412\:0435\:043a\:0442\:043e\:0440\:044b \:0441\:0434\:0432\:0438\:0433\:043e\:0432 *)
	IdentityMatrix[3],

	(* \:0412\:0435\:043a\:0442\:043e\:0440\:044b \:0432\:0440\:0430\:0449\:0435\:043d\:0438\:0439 *)
	{{  0,  z, -y },
	 { -z,  0,  x },
	 {  y, -x,  0 }}
};
killingDec = Flatten[killingDec, 1];


(* ::Text:: *)
(*\:0421\:0444\:0435\:0440\:0438\:0447\:0435\:0441\:043a\:0438\:0435 \:043a\:043e\:043e\:0440\:0434\:0438\:043d\:0430\:0442\:044b*)


killingSpher = { nSpher, lSpher } =
{
	(* \:0412\:0435\:043a\:0442\:043e\:0440\:044b \:0441\:0434\:0432\:0438\:0433\:043e\:0432 *)
	{{ r Sin[u] Cos[w], Cos[u] Cos[w], - Csc[u] Sin[w] },
	 { r Sin[u] Sin[w], Cos[u] Sin[w], + Csc[u] Cos[w] },
	 { r Cos[u], - Sin[u], 0 }} / r,

	(* \:0412\:0435\:043a\:0442\:043e\:0440\:044b \:0432\:0440\:0430\:0449\:0435\:043d\:0438\:0439 *)
	{{ 0, Sin[w],  Cos[w] Cot[u] },
	 { 0, Cos[w], -Cot[u] Sin[w] },
	 { 0, 0, 1 }}
};
killingSpher = Flatten[killingSpher, 1];


(* ::Text:: *)
(*\:041e\:043f\:0435\:0440\:0430\:0442\:043e\:0440\:044b \:043f\:043e\:0432\:044b\:0448\:0435\:043d\:0438\:044f \:0438 \:043f\:043e\:043d\:0438\:0436\:0435\:043d\:0438\:044f  \:0432 \:0434\:0435\:043a\:0430\:0440\:0442\:043e\:0432\:044b\:0445 \:043a\:043e\:043e\:0440\:0434\:0438\:043d\:0430\:0442\:0430\:0445*)


udzDec =
{
	lDec[[1]] - I lDec[[2]], (* up *)
	lDec[[1]] + I lDec[[2]], (* down *)
	lDec[[3]] (* z *)
};

udzDecOp = Lie /@ udzDec;


(* ::Text:: *)
(*\:041e\:043f\:0435\:0440\:0430\:0442\:043e\:0440\:044b \:043f\:043e\:0432\:044b\:0448\:0435\:043d\:0438\:044f \:0438 \:043f\:043e\:043d\:0438\:0436\:0435\:043d\:0438\:044f  \:0432 \:0441\:0444\:0435\:0440\:0438\:0447\:0435\:0441\:043a\:0438\:0445 \:043a\:043e\:043e\:0440\:0434\:0438\:043d\:0430\:0442\:0430\:0445*)


udzSpher =
{
	lSpher[[1]] - I lSpher[[2]], (* up *)
	lSpher[[1]] + I lSpher[[2]], (* down *)
	lSpher[[3]] (* z *)
};

udzSpherOp = Lie /@ udzSpher;
