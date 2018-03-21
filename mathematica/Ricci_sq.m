(* ::Package:: *)

Lsol[zz_,yy_] := Module[{y,z,x},
	z = zz /. yy->y;
	x = Solve[z == 0,y];
	y /. x[[1]] //Simplify
]

Lin[F_,x_] := Module[{f,y,z},
	f = F /. x -> y;
	z = Series[f, {y,0,1}] //Normal //Simplify;
	z /. y->x //Simplify
]

S[z_] := z //Simplify

Eq[l_,b_] := Module[{bb,n,x,i,db},
	bb = b;
	n = Length[bb];
	db = D[l,b] - Sum[D[D[l, D[b, bb[[i]]]], bb[[i]]], {i,n}] //S
]


GGD = {
	{1,0,0},
	{0,1,0},
	{0,0,1}
};
Decart := Ricci[{x,y,z}, GGD]

GGS := {
	{1,0,0},
	{0,r^2,0},
	{0,0,r^2 Sin[u]^2}
}
Spher := Ricci[{r,u,w}, GGS]

Ricci[coords_,mtr_] := Module[{DG,ss,i,j,k,s,zzzz},
	Do[x[i] = coords[[i]],{i,3}];
	DG = Det[mtr] //Simplify;
	ss = Solve[zzzz^2 == DG, zzzz];
	gd = zzzz /. ss[[2]];
	HH = Inverse[mtr] //Simplify;
	Do[
		Do[
			hh[i,j] = HH[[i,j]];
			gg[i,j] = mtr[[i,j]],
			{j,3}
		],
		{i,3}
	];
	Do[Do[Do[
		cs1[i,j,k] = D[gg[i,j], x[k]] + D[gg[i,k], x[j]] - D[gg[j,k], x[i]] //Simplify,
			{k,3}], {j,3}], {i,3}];
	Do[Do[Do[
		cs2[i,j,k] = Sum[hh[i,s] cs1[s,j,k] / 2, {s,3}] //Simplify,
			{k,3}], {j,3}], {i,3}];
	Do[cs[i] = Sum[cs2[j,i,j], {j,3}] //Simplify, {i,3}];

	Do[
		Do[
			rici[i,j] =
				Sum[D[cs2[k,i,j], x[k]], {k,3}] -
				D[cs[i], x[j]] +
				Sum[
					Sum[cs2[k,i,j] cs2[l,k,l] - cs2[k,l,i] cs2[l,k,j] //Simplify, {l,3}],
					{k,3}
				],
				{j,3}
		],
		{i,3}
	];
	Do[Do[ric[i,j] = Sum[hh[i,s]rici[s,j] //Simplify, {s,3}], {j,3}], {i,3}];
	rs = Sum[ric[i,i], {i,3}] //Simplify;
	Rij = Array[ric,{3,3}]
]


ddd[h_,i_,j_,k_] := D[h[[i,j]], x[k]] - Sum[(cs2[s,i,k] h[[s,j]] + cs2[s,j,k] h[[i,s]]), {s,3}] //S

Lag20[h_] := Module[{e,i,j,k},
	Do[e[i,j,k] = 0, {i,3}, {j,3}, {k,3}];
	e[1,2,3] = e[2,3,1] = e[3,1,2] = 1;
	e[1,3,2] = e[3,2,1] = e[2,1,3] = -1;
	Do[b[i,j] = Sum[e[i,k,l] ddd[h,j,k,l], {k,3}, {l,3}], {i,3}, {j,3}];
	Ub = Sum[b[i,j] b[j,i], {i,3}, {j,3}] / 2 //S //Expand;
	Do[ee[i,j] = D[h[[i,j]], t], {i,3}, {j,3}];
	HT =
		hh[1,1] hh[2,2] (ee[1,2]^2 - ee[1,1] ee[2,2]) +
		hh[1,1] hh[3,3] (ee[1,3]^2 - ee[1,1] ee[3,3]) +
		hh[2,2] hh[3,3] (ee[2,3]^2 - ee[2,2] ee[3,3]);
	(HT gd - Ub / gd) / 4 //S
]


Killing[Vels_] := Module[{DG,ss},
	Do[Do[
		kil[i,j] = Sum[
			D[Vels[[s]], x[i]] gg[s,j] + D[Vels[[s]], x[j]] gg[i,s] + Vels[[s]] D[gg[i,j], x[s]],
			{s,3}
		],
		{j,3}], {i,3}];
	Array[kil, {3,3}] //Simplify
]

Commut[vel1_,vel2_] := Module[{},
	Do[com[i] = Sum[
		vel1[[s]] D[vel2[[i]], x[s]] - vel2[[s]] D[vel1[[i]], x[s]],
		{s,1,3}
	], {i,1,3}] //Simplify;
	Array[com, 3] //Simplify
]


Div[V_] := Module[{},
	Sum[D[V[[i]] gd,x[i]], {i,3}] / gd //Simplify
]
Rot[V_] := Module[{vl,rrr},
	Do[vl[i] = Sum[gg[i,j] V[[j]], {j,3}], {i,3}];
	rrr[1] = (D[vl[2], x[3]] - D[vl[3], x[2]]) / gd //Simplify;
	rrr[2] = (D[vl[3], x[1]] - D[vl[1], x[3]]) / gd //Simplify;
	rrr[3] = (D[vl[1], x[2]] - D[vl[2], x[1]]) / gd //Simplify;
	Array[rrr, 3]
]


mtr[coords_,mt_] := Module[{DG,ss,i,j,k,s,zzzz},
	Do[x[i] = coords[[i]], {i,3}];
	DG = Det[mt] //Simplify;
	ss = Solve[zzzz^2 == DG, zzzz];
	gd = zzzz /. ss[[2]];
	HH = Inverse[mt] //Simplify;
	Do[Do[
		hh[i,j] = HH[[i,j]];
		gg[i,j] = mtr[[i,j]],
	{j,3}], {i,3}];
]


Approx[h_] := Module[{dgd,dg,ds,i,j,k,s},
	Do[Do[Do[
		dgd[i,j,k] =
			D[h[[k,i]], x[j]] +
			D[h[[k,j]], x[i]] -
			D[h[[i,j]], x[k]] -
			2 Sum[cs2[s,i,j] h[[k,s]], {s,3}] //Simplify,
	{k,3}], {j,3}], {i,3}];
	Do[Do[Do[
		dg[i,j,k] = Sum[hh[i,s] dgd[j,k,s] / 2, {s,3}] //Simplify,
	{k,3}], {j,3}], {i,3}];
	Do[ds[i] = Sum[dg[k,i,k] //Simplify, {k,3}], {i,3}];
	Do[Do[
		dR[i,j] =
			- D[ds[i],x[j]] +
			Sum[D[gd dg[k,i,j], x[k]] / gd + cs2[k,i,j] ds[k] //Simplify, {k,3}] -
			Sum[Sum[(cs2[s,k,i] dg[k,s,j] + cs2[s,k,j] dg[k,s,i]), {k,3}], {s,3}],
	{j,3}], {i,3}];
	Array[dR, {3,3}]
]


Spur[T_] := Sum[hh[kk,kk] T[[kk,kk]], {kk,3}] //Simplify

CovDif[Vels_] := Module[{DG,ss},
	Do[Do[
		cov[i,j] = D[Vels[[i]], x[j]] + Sum[cs2[i,j,k] Vels[[k]], {k,3}],
	{j,3}], {i,3}];
	Array[cov, {3,3}]//Simplify
]

Geodes[Field_] := Module[{DG,ss},
	Do[zz[i] = Sum[
		Field[[k]] (D[Field[[i]], x[k]] + Sum[cs2[i,j,k] Field[[j]], {j,3}]), {k,3}
	] //Simplify, {i,3}];
	ZZ = Array[zz,3]
]

Pr[V1_,V2_] := Module[{l1,l2,rr},
	Do[l1[i] = Sum[gg[i,j] V1[[j]], {j,3}], {i,3}];
	Do[l2[i] = Sum[gg[i,j] V2[[j]], {j,3}], {i,3}];
	rr[1] = (l1[2] l2[3] - l1[3] l2[2]) / gd //Simplify;
	rr[2] = (l1[3] l2[1] - l1[1] l2[3]) / gd //Simplify;
	rr[3] = (l1[1] l2[2] - l1[2] l2[1]) / gd //Simplify;
	Array[rr,3]
]

Scal[V1_,V2_] := Module[{},
	Sum[Sum[gg[i,j] V1[[i]] V2[[j]], {j,3}], {i,3}] //Simplify
]
Lie[V_,f_] := Module[{}, Sum[V[[i]] D[f,x[i]], {i,3}] //Simplify]

Lap[f_] := Module[{},
	Sum[D[Sum[gd hh[i,j] D[f, x[j]], {j,3}], x[i]] / gd, {i,3}] //Simplify
]

DivTens[tt_] := Module[{tu,i,j,k},
	Do[Do[tu[i,j] = Sum[hh[i,k] tt[[k,j]], {k,3}] //Simplify, {i,3}], {j,3}];
	Do[div[j] =
		((Sum[D[gd tu[i,j], x[i]] / gd, {i,3}]) -
		 (Sum[Sum[cs2[i,j,k] tu[k,i], {k,3}], {i,3}])) //Simplify, {j,3}];
	Array[div,3]
]

KillT[V_,T_] := Module[{i,j,k},
	Do[Do[kT[i,j] = Sum[
		V[[k]] D[T[[i,j]], x[k]] +
		D[V[[k]], x[i]] T[[k,j]] +
		D[V[[k]], x[j]] T[[i,k]],
	{k,3}] //Simplify, {j,3}], {i,3}];
	Array[kT, {3,3}]
]

RR[vec_] := Rot[Rot[vec]] - m vec //Simplify

KillV[V_,A_] := Module[{i,k},
	Do[kV[i] = Sum[
		V[[k]] D[A[[i]], x[k]] -
		D[V[[i]], x[k]] A[[k]],
	{k,3}] //Simplify, {i,3}];
	Array[kV, 3]
]

KillS[V_,f_] := Sum[V[[k]] D[f,x[k]], {k,3}] //Simplify

LapV[A_] := Module[{i,j,k,l,s,b,B},
	W = Sum[D[Sum[gd hh[i,j] D[A, x[j]], {j,3}], x[i]] / gd, {i,3}] //Simplify;
	Do[b[i] = Sum[Sum[Sum[
		hh[k,j] (cs2[i,j,l]D[A[[l]],x[k]] +
		cs2[i,k,l] D[A[[l]],x[j]] +
		(
			D[cs2[i,j,l], x[k]] +
			(
				Sum[cs2[i,k,s] cs2[s,j,l] -
					cs2[i,l,s] cs2[s,j,k], {s,3}]
			)
		) A[[l]]), {l,3}], {k,3}], {j,3}] //Simplify, {i,3}];
	B = Array[b, 3];
	W + B + m A //Simplify
]

LapT[h_] := Module[{mh,nh},
	Do[Do[Do[
		mh[i,j,k] =
			D[h[[j,k]], x[i]] -
			Sum[(cs2[s,i,j] h[[s,k]] + cs2[s,i,k] h[[j,s]]), {s,3}] //Simplify,
	{k,3}], {j,3}], {i,3}];
	Do[Do[Do[
		nh[i,j,k] = Sum[hh[i,s] mh[s,j,k], {s,3}] //Simplify,
	{k,3}], {j,3}], {i,3}];
	Do[Do[
		lt[j,k] =
			Sum[D[nh[i,j,k] gd, x[i]] / gd -
			Sum[(cs2[s,i,j] nh[i,s,k] + cs2[s,i,k] nh[i,j,s]), {s,3}], {i,3}] //Simplify,
	{j,3}], {k,3}];
	Array[lt,{3,3}]
]

pLie[V_,f_] := Sum[D[f V[[i]], x[i]], {i,3}] //Simplify
