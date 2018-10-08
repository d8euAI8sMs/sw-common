(* ::Package:: *)

EnableFeature[{a_}]:=EnableFeature[a];
EnableFeature[{a_,b__}]:=Module[{},EnableFeature[a];EnableFeature[{b}]];
