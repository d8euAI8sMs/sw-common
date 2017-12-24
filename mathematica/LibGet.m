(* ::Package:: *)

$LibRoot = "../../lib/mathematica";
$CurDir = ".";

Options[ImportLibs] = {
	LibRoot -> $CurDir,
	Quiet -> False
};

ImportLibs[rawlibs_, OptionsPattern[]] := Module[{libs, relpath, abspath, has, eval},
	relpath = OptionValue[LibRoot];
	
	If[!ListQ[rawlibs], libs = { rawlibs }, libs = rawlibs];
	
	Do[
		abspath = AbsoluteFileName[FileNameJoin[{NotebookDirectory[], relpath, lib <> ".m"}]];
		has = False;

		If[!ValueQ[$ImportedLibs], $ImportedLibs = {}];

		Do[If[has, Break[]]; has = e[[3]] == abspath, { e, $ImportedLibs }];
		If[has, Return[]];

		AppendTo[$ImportedLibs, { lib, relpath, abspath }];

		If[OptionValue[Quiet],
			Quiet[NotebookEvaluate[abspath]],
			NotebookEvaluate[abspath]
		];

		,
		{ lib, libs }
	];
];
