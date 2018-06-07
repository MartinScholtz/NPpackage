(* ::Package:: *)

(* Wolfram Language Package *)

(* Created by the Wolfram Workbench Jun 7, 2018 *)

BeginPackage["NP`"]
(* Exported symbols added here with SymbolName::usage *) 
NPExtractMetric::usage="NPExtractMetric[ds, xs] \n returns the matrix of metric tensor constructed from the line element ds, assuming that the list of coordinates is given by xs";
NPConnection::usage="NPConnection[xs,gd] \n returns matrix of Christoffel symbols.";
NPCurvatureTensors::usage="NPCurvatureTensors[xs, gd] \n returns { Christoffel, Riemann, Ricci, scalar curvature, Weyl}, all covariant.";
NPCheckFrame::usage="NPCheckFrame[e,gd] \n returns the matrix of all scalar products of the frame vectors e with respect to metric g.";
NPSpinCoeffs::usage="NPSpinCoeffs[xs,gd,\[CapitalGamma],{lu,nu,mu,mucc}] \n returns the spin coefficients.";
NPWeylScalars::usage="NPWeylScalars[W,{lu,nu,mu,mucc}] \n returns the Weyl scalars, i.e. the components of the Weyl tensor W with respect to the null tetrad.";
NPRicciScalars::usage="NPRicciScalars[Ric,{lu,nu,mu,mucc}] \n returns the Ricci scalars, i.e. the components of the Ricci tensor Ric with respect to the null tetrad.";


Begin["`Private`"]
(* Implementation of the package *)


(* Einstein equations *)
NPExtractMetric[ds_,x_List] := Table[ If[i==j,1,1/2]Coefficient[Expand[ds], Dt[x[[i]]] Dt[x[[j]]]], {i,1,Length[x]},{j,1,Length[x]}]
NPConnection[xs_/;ListQ[xs],gd_/;MatrixQ[gd]]:= Module[ {Dg,gu},
	gu =Inverse[gd];
	Dg = (\!\(
\*SubscriptBox[\(\[PartialD]\), \(#\)]gd\))& /@ xs;
	1/2 gu.( Transpose[Dg,{3,2,1}]+Transpose[Dg,{2,1,3}]-Dg) 
]
NPCurvatureTensors[xs_/;ListQ[xs],gd_] := Module[ {\[CapitalGamma],d\[CapitalGamma],Ruddd,Rd,Ric,W,W2,gR,R,gg},
	Print["Calculating connection"];
	\[CapitalGamma] = NPConnection[xs,gd];
	Print["Derivatives of \[CapitalGamma]"];
	d\[CapitalGamma] = (\!\(
\*SubscriptBox[\(\[PartialD]\), \(#\)]\[CapitalGamma]\) &) /@ xs//Simplify;
	Print["\!\(\*SubsuperscriptBox[\(R\), \(\[Beta]\[Mu]\[Nu]\), \(\[Alpha]\)]\)"];
	Ruddd=Transpose[ d\[CapitalGamma],{4,1,2,3}] - Transpose[ d\[CapitalGamma],{3,1,2,4}] + Transpose[Transpose[\[CapitalGamma],{1,3,2}].\[CapitalGamma],{1,4,2,3}]-Transpose[Transpose[\[CapitalGamma],{1,3,2}].\[CapitalGamma],{1,3,2,4}]//Simplify;
	Print["\!\(\*SubscriptBox[\(R\), \(\[Alpha]\[Beta]\[Mu]\[Nu]\)]\)"];
	Rd=gd.Ruddd//Simplify;
	Print["\!\(\*SubscriptBox[\(R\), \(\[Mu]\[Nu]\)]\)"];
	Ric = TensorContract[Ruddd,{{1,3}}]//Simplify;
	Print["\!\(\*SubscriptBox[\(g\), \(\[Mu]\[Nu]\)]\)\!\(\*SubscriptBox[\(R\), \(\[Alpha]\[Beta]\)]\)"];
	gR=gd\[TensorProduct]Ric//Simplify;
	Print["\!\(\*SubscriptBox[\(g\), \(\[Mu]\[Nu]\)]\)\!\(\*SubscriptBox[\(g\), \(\[Alpha]\[Beta]\)]\)"];
	gg=gd\[TensorProduct]gd//Simplify;
	Print["R"];
	R=Tr[Inverse[gd].Ric]//Simplify;
	Print["\!\(\*SubscriptBox[\(C\), \(\[Alpha]\[Beta]\[Mu]\[Nu]\)]\)"];
	W=Rd-(Transpose[gR,{1,3,4,2}]-Transpose[gR,{1,4,2,3}]-Transpose[gR,{2,3,4,1}]+Transpose[gR,{2,4,3,1}])/2
		+1/6 R ( Transpose[gg,{1,3,4,2}]-Transpose[gg,{1,4,2,3}])//Simplify;
	{\[CapitalGamma],Rd,Ric,R,W}
]
Differentiate[obj_,xs_]:=D[obj,#]&/@xs
NPSpinCoeffs[xs_,gd_,\[CapitalGamma]_,{lu_,nu_,mu_,mucc_}]:= Module[{ld,nd,md,mdcc,Dl,Dn,Dm,Dmcc},
	{ld,nd,md,mdcc}=gd.#&/@{lu,nu,mu,mucc}//Simplify;
	{Dl,Dn,Dm,Dmcc}=Differentiate[#,xs]-#.\[CapitalGamma]&/@{ld,nd,md,mdcc}//Simplify;
	Rule@@@Transpose[{$defaultSpinCoeffs,{
		1/2 (nu.(lu.Dl) - mucc.(lu.Dm)) (* epsilon *),
		mu.(lu.Dl) (*kappa*),
		nu.(lu.Dmcc) (* pi *),
		mu.(nu.Dl) (* tau *),
		1/2 ( nu.(mucc.Dl)-mucc.(mucc.Dm)) (* alpha *),
		1/2 ( nu.(mu.Dl)-mucc.(mu.Dm)) (* beta *),
		1/2 ( nu.(nu.Dl)-mucc.(nu.Dm)) (* gamma *),
		nu.(nu.Dmcc) (* nu *),
		mu.(mucc.Dl) (* rho *),
		mu.(mu.Dl) (* sigma *),
		nu.(mucc.Dmcc) (* lambda *),
		nu.(mu.Dmcc) (* mu *)
	}}]
]
NPWeylScalars[W_,{l_,n_,m_,mc_}]:= {
		Global`\[Psi][0]-> m.(l.W.m).l,
		Global`\[Psi][1]->n.(l.W.m).l,
		Global`\[Psi][2]->m.(l.W.n).mc,
		Global`\[Psi][3]->n.(l.W.n).mc,
		Global`\[Psi][4]->n.(mc.W.n).mc
	}//Simplify;
NPRicciScalars[Ric_, {lu_,nu_,mu_,mucc_}]:=  Module[{},
	{
	 Global`\[CapitalPhi][0,0] -> - (1/2)lu.Ric.lu,
	 Global`\[CapitalPhi][0,1] -> - (1/2)lu.Ric.mu,
	 Global`\[CapitalPhi][0,2] -> - (1/2)mu.Ric.mu,
	 Global`\[CapitalPhi][1,1] -> - (1/4)( lu.Ric.nu + mu.Ric.mucc),
	 Global`\[CapitalPhi][1,2] -> - (1/2)nu.Ric.mu,
	 Global`\[CapitalPhi][2,2] -> - (1/2)nu.Ric.nu
	 }//Simplify
]
NPCheckFrame[e_,g_] := e.g.Transpose[e]


End[]

EndPackage[]

