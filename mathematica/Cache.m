(* ::Package:: *)

(* ::Section:: *)
(*\:0418\:043c\:043f\:043e\:0440\:0442 \:0431\:0438\:0431\:043b\:0438\:043e\:0442\:0435\:043a*)


(* ::Section:: *)
(*\:041e\:043f\:0440\:0435\:0434\:0435\:043b\:0435\:043d\:0438\:044f*)


(* ::Input::Initialization:: *)
$taggedCaches=<||>;
$currentCacheTag="Global";
$currentCache:=GetCache[];
$cacheDir=Null;

EnsureCache[tag_String]:=With[{c=$taggedCaches[tag]}, If[MissingQ[c],AppendTo[$taggedCaches,tag-><||>]]];

GetCache[] :=GetCache[GetCurrentCacheTag[]];
GetCache[tag_String]:=(EnsureCache[tag];$taggedCaches[tag]);
GetCacheFile[]:=GetCache[GetCurrentCacheTag[]];
GetCacheFile[tag_String]:=(EnsureCache[tag];$taggedCaches[tag]);
SetCache[cache_Association]:=SetCache[GetCurrentCacheTag[],cache];
SetCache[tag_String,cache_Association]:=(EnsureCache[tag];$taggedCaches[[Key[tag]]]=cache);

GetCurrentCacheTag[]:=$currentCacheTag;
SetCurrentCacheTag[tag_String]:=$currentCacheTag=tag;

SetAttributes[InCache,{HoldRest}];
InCache[tag_String,expr_]:=Block[{$currentCacheTag=tag},expr];

GetFromCache[key_]:=GetFromCache[GetCurrentCacheTag[],key];
GetFromCache[tag_String,key_]:=(EnsureCache[tag];$taggedCaches[[Key[tag],Key[key]]]);
PutToCache[val_]:=PutToCache[GetCurrentCacheTag[],val];
PutToCache[tag_String,val_]:=(EnsureCache[tag];AppendTo[$taggedCaches[[Key[tag]]],val]);
DeleteFromCache[key_]:=DeleteFromCache[GetCurrentCacheTag[],key];
DeleteFromCache[tag_String,key_]:=(EnsureCache[tag];$taggedCaches[[Key[tag]]]=Delete[$taggedCaches[[Key[tag]]],Key[key]]);


(* ::Input::Initialization:: *)
Attributes[Intern]={HoldAll};
Intern[key_,val_, c_Function:(False&)]:=With[{t=GetFromCache[Hold[key]]},If[MissingQ[t]||!MissingQ[t]&&c[t],With[{v=val},PutToCache[Hold[key]->v];DumpCache[]; v], t]];

Attributes[Cached]={HoldAll};
Cached[expr_, c_Function:(False&)]:=With[{x0=Extract[Unevaluated[expr],{1},Hold]},
With[{t=GetFromCache[x0]},
If[MissingQ[t]||!MissingQ[t]&&c[t],expr;PutToCache[x0->ReleaseHold[x0]];DumpCache[];ReleaseHold[x0],Module[{eq={Extract[Unevaluated[expr],{1},Unevaluated],t}},eq[[0]]=Set;eq;];x]
]
];
Cached[key_,val_, c_Function:(False&)]:=Unevaluated[key]=Intern[key, val,c];

Attributes[AllCached]={HoldAll};
AllCached[exprs_List]:=Do[With[{t=Extract[Unevaluated[exprs],{i},Unevaluated]},Cached[t]],{i,Length[Unevaluated[exprs]]}];
AllCached[exprs__]:=Do[With[{t=Extract[Unevaluated[{exprs}],{i},Unevaluated]},Cached[t]],{i,Length[Unevaluated[{exprs}]]}];

Attributes[Uncache]={HoldAll};
Uncache[keys__]:=(Do[With[{k=Extract[Unevaluated[{keys}],{i},Hold]};DeleteFromCache[k]],{i,Length[Unevaluated[{keys}]]}];DumpCache[]);

ClearCache[] := (SetCache[<||>]; DumpCache[]);

DumpCache[]:=If[$cacheDir=!=Null,DumpCache[$cacheDir]];
DumpCache[dir_String]:=Do[
Quiet@CreateDirectory[dir];
Block[{$cacheData=GetCache[tag],$cacheTag=tag},
DumpSave[FileNameJoin[{dir,tag<>".cache.mx"}],{$cacheData,$cacheTag}]]
,{tag,Keys[$taggedCaches]}];

RestoreCache[dir_String]:=With[{files=FileNames["*.cache.mx",dir]},
Do[
Block[{$cacheData,$cacheTag},
Get[file];
SetCache[$cacheTag,$cacheData];
Do[
Module[{eq={Extract[k,{1},Unevaluated],$cacheData[k]}},
eq[[0]]=Set;
eq;
]
,{k,Keys[$cacheData]}]
]
,{file,files}]
];
RestoreCache[]:=If[$cacheDir=!=Null,RestoreCache[$cacheDir]];


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
