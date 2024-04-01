newPackage(
	"TateAlgebra",
    	Version => "1.0", 
    	Date => "Jul 25, 2023",
        Authors => {
	    {Name => "Liana Sega",
		Email => "segal@umkc.edu"},
	    {Name => "Deepak Sireeshan",
         	Email => "dsbx7@umsystem.edu"} },
    	Headline => "DG algebra and module structure in rings with linear pair of exact zero divisors",
	Keywords => {"Exact zero divisors"},
	AuxiliaryFiles => false, -- set to true if package comes with auxiliary files,
	PackageExports =>{"Macaulay2Doc"},
    	DebuggingMode => false	 -- set to true only during development
    	)

export {
     "multMap",
     "tateMul",
     "tateRes",
     "LenLimit"
     }

------------------------------------------
multMap = method()
multMap(ChainComplex, RingElement, ZZ, ZZ) := (C,f,i,j)->(
    sig := new MutableHashTable;
    BasisofV := new MutableHashTable;
    BasisofU := new MutableHashTable;
    if ((i+j) > length C) then error "insufficient resolution length";
    Q := ring f; 
    sig#(0,0) = id_(C_0);
    pair := select(1,flatten entries gens ann(f), d -> degree(d) == {1});-- selects a linear zero divisor from ann(f)
    if pair == {} then error "annihilator of f does not have any linear elements";
    exact := pair|{f};
    BasisofV#0 = BasisofU#0 = sig#(0,0);
    for k from 0 to j do(
    	lis := {};
    	if (k == 0) then (
    	    for l from 1 to (i+j) do(	
	    	sig#(l,k) = (exact_(l%2)*sig#((l-1),k))//C.dd_l;----sigma maps complete
	    	);
	    BasisofV#1 = mingens ker transpose sig#(1,k);
	    BasisofU#1 = BasisofV#1 | sig#(1,k);
	    )
    	else (
	    sig#(0,k) = id_(C_k);
	    for l from 1 to (i+j-k) do(
		eqmatrix := ((exact_(l%2))*sig#((l-1),k)) -(((-1)^(l+1))*(sig#(l,(k-1))*C.dd_k));
		sig#(l,k) = eqmatrix//C.dd_(l+k);
	    	);
        	for h from 1 to (k+1) do (
	    	    lis  = lis|{sig#(h,(k+1-h))*BasisofV#(k+1-h)};
	    	    );
     		eq := sum(lis, d-> image d);
     		BasisofV#(k+1) = mingens ker transpose mingens eq;
		BasisofU#(k+1) = BasisofV#(k+1) | matrix{lis};	
		);
    	    );
    return (sig, BasisofV, BasisofU)
	)		
--------------------------------------------------------------------------------------------------
tateMul = method()
tateMul(ChainComplex, RingElement, ZZ, Matrix) := (C,f,i,Vec)->(
    sig := new MutableHashTable;
    BasisofV := new MutableHashTable;
    BasisofU := new MutableHashTable;
    j := -1;
    while ((j+1<=length C) and (numgens C_(j+1) != numgens target Vec)) do (
    	j = j+1;
    	);
    --if (j == -1) then error "Enter a free module element of approproate degree"
    --else (j = j+1);
    j = j+1;
    (sig,BasisofV,BasisofU) = multMap(C,f,i,j);
    return sig#(i,j)*Vec
    )
--------------------------------------------------------------------------------    
tateRes = method(Options => {LenLimit => 4})
tateRes(ChainComplex, RingElement) := o -> (C,f)->(
    invBU := new MutableHashTable;
    projM := new MutableHashTable;
    diffr := {};
    i := 1;
    j := o.LenLimit - 1;
    Q := ring f;
    R := Q/ideal(f) ; 
    (sig,BasisofV,BasisofU) := multMap(C,f,i,j);
    for k from 0 to j do(
	if (k == 0) then (
	    invBU#1 = inverse BasisofU#1;
	    diffr = diffr | {substitute(C.dd_1*BasisofV#1,R)};
	    projM#1 = matrix((image BasisofU#1)^{0..(numgens prune image BasisofV#1 - 1)})*invBU#1;
	    )
	else (
	    invBU#(k+1) = inverse BasisofU#(k+1);
	    projM#(k+1) = matrix ((image BasisofU#(k+1))^{0..(numgens prune image BasisofV#(k+1) - 1)})*invBU#(k+1);
	    diffr = diffr | {substitute (projM#k*C.dd_(k+1)*BasisofV#(k+1), R)};
	    );
	);
    return chainComplex diffr
    )
------------------------------------------------------------
-- DOCUMENTATION TateAlgebra -- documentation
------------------------------------------------------------

beginDocumentation()

doc ///
Key 
     TateAlgebra
Headline 
     A package to explore DG module structures of minimal free resolutions and its modulo over an exact zero divisor.
Description
 Text
     Given a ring $Q$ that admits a linear pair of  zero divisors $(f,g)$, the $Q$-module $Q/f$ 
     has a DG algebra structure, say $A$, as detailed in \url{https://arxiv.org/abs/2208.04452}. Furthermore, the 
     minimal free resolution $U$ of a $Q$ module $M$ with $fM = 0$ has  DG module structure over the DG 
     algebra $A$. We use the proof of the theorem to write an algorithm 'tateMul' that can define the 
     multiplication maps $A \times U \to U$.
     
     If $(f,g)$ is a pair of exact zero divisors, meaning $\{q \in Q|f*q = 0\} = (g)$ and $\{q \in Q|g*q =0\} = (f)$, then
     $U \otimes_A Q/f$ is a minimal free resolution of M over $Q/f$. The function 'tateRes' computes
     the said minimal free resolution. 
    
SeeAlso
     multMap
     tateMul
     tateRes
///

------------------------------------------------------------
-- DOCUMENTATION tateMult
------------------------------------------------------------

doc ///
     Key
          tateMul
	  (tateMul, ChainComplex, RingElement, ZZ, Matrix) 
     Headline
          multiplies DG algebra basis element with an element in the  minimal free resolution (has DG module structure).
     Usage
     	  V=tateMul(C,f,i,Vec)
         
     Inputs
          C:ChainComplex
	       the minimal free resolution of a  module $M$ with $fM = 0$.
	  f:RingElement
	      the linear zero divisor.
	  i:ZZ
	       the homological degree of the basis of the DG algebra that you choose to multiply.
	  Vec:Matrix
	       Column Vector of size (j) with entries in $Q$ such that
	       the free module $Q^j = C_n$ for some $n \geq 0$.  
	      
     Outputs
          V:Matrix
	       Column Vector of size $(i+j)$ in $C_{i+n}$.
     Description
          Text
              The function produces the result of multiplication of the basis of $i$th free module
	      of the DG algebra $Q/(f)$ with the given element of the minimal free resolution.
       
	  Text
	      The algorithm uses the main theorem from Sega and Sireeshan, \url{https://arxiv.org/abs/2208.04452}
	      to construct the multiplication maps iteratively. 
          Example
               S = ZZ/32003[a,b,c,d]
	       I = ideal(a*b, a^2, c^7+d^8)
	       Q = S/I
	  Text
	       Since $a^2 = 0$, we have a linear pair of zero divisors. The following line 
	       constructs a random module in $Q$ such that $aM = 0$. 
	       
	  Example 
	       M = cokernel matrix{{random(3,Q), random(2,Q), a}} -- module with fM = 0
	       C = res (trim M, LengthLimit => 4)
	       i = 2 -- the homological of the basis of element of the DG algebra
	       Vec = matrix{{random(1,Q)},{random(2,Q)},{random(3,Q)}, {random(4,Q)}} -- an element in C_1 = Q^4
	       V = tateMul(C,a,i,Vec) -- an element in C_3 = Q^8
      
	  Text 
	       $y_i$ is the basis of $i$th free module of the DG algebra $Q/(f)$. Since
	       $y_iu \in C_{i+n}$ where $u \in C_n$, the output is a column vector of size 8 $\in C_3$ 
	       since Vec $\in C_1$.    
     SeeAlso
     	  tateRes
     	  
///


------------------------------------------------------------
-- DOCUMENTATION tateRes
------------------------------------------------------------
doc ///
     Key
          tateRes
	  (tateRes, ChainComplex, RingElement)
	  [tateRes, LenLimit]
     Headline
          produces a minimal free resolution of the module utilizing DG module structures
	   
     Usage
          CR = tateRes(C,f)
     Inputs
	  f:RingElement
	       The linear exact zero divisor. 
	       
	  C:ChainComplex
	       The  minimal free resolution of a module $M$ such that $fM = 0$.	       
     Outputs
          CR:ChainComplex
	       The minimal free resolution of $M$ over the quotient ring (modulo $f$)
     Description
          Text
	       The algorithm uses the main theorem from Sega and Sireeshan, \url{https://arxiv.org/abs/2208.04452}
	       to construct the resolution iteratively.
	       
	  Example
               S = ZZ/32003[a,b,c]
	       setRandomSeed 0
	       I = trim ideal fromDual matrix {{random(2,S), random(2,S)}}
	       Q = S/I
	  Text
	       This creates one instance of a ring that admits linear pair of {\it exact zero} divisors. 
	       
	  Example
	       f = a - 14488*b - 7246*c
	       g = ann f
	       ann g == ideal f
	       
	  Text
	       The above lines of code verifies that $(f,g)$ are infact a pair of exact zero divisors. 
	       
          Example
	       M = cokernel matrix{{107*b+4376*c, -5570*b + 3187*c, f}}
	       C = res(trim M, LengthLimit => 4)
	       CRtate = tateRes(C,f,LenLimit => 4) 	
	       apply({1,2,3}, i->(ker CRtate.dd_i == image CRtate.dd_(i+1))) -- checks exactness
     Caveat
	  In the current version, the time complexity of this function is not better than that of res function. 
  
     SeeAlso
     	  tateMul    
///



------------------------------------------------------------
-- DOCUMENTATION LenLimit
------------------------------------------------------------
doc ///
     Key
     	  LenLimit
     
     Headline
     	  option to tateRes
    
     Description
          Text
	       LenLimit is an optional argument in tateRes function  which is the same as LengthLimit in resolution function. 
	       The default value is 4.
	      
///



TEST///
S = ZZ/32003[a,b,c];
setRandomSeed 0;
I = trim ideal fromDual matrix {{random(2,S), random(2,S)}};
Q = S/I;
f = a - 14488*b - 7246*c;
M = cokernel matrix{{107*b+4376*c, -5570*b + 3187*c, f}};
C = res(trim M, LengthLimit => 4);
CRtate = tateRes(C,f,LenLimit => 4);
assert(CRtate.dd^2 == 0)
assert(numgens C#4 ==sum({0,1,2,3,4}, (d -> numgens CRtate#d)))
///



end--  
restart
loadPackage ("TateAlgebra", Reload =>true)
load "TateAlgebra.m2"

uninstallPackage "TateAlgebra"
restart
installPackage "TateAlgebra"
check "TateAlgebra"
viewHelp TateAlgebra


------------------------------------------------------------
-- DOCUMENTATION CoefMat
------------------------------------------------------------
doc ///
     Key
          CoefMat
     Headline
          produces a matrix of coefficients. 
     Usage
          C = CoefMat(M)
     Inputs
	  M:Matrix
	       Matrix of linear terms 
	       	       
     Outputs
          C:Matrix
	       Coefficient Matrix of M using all indeterminates  in ring M. 
     Description
          Text
	       The code is a naive extension of coefficients function in Macaulay2Doc.  
	       
	  Example
               Q = ZZ[x,y,z]
	       M = matrix{{random(1,Q), random(1,Q), random(1,Q)},{random(1,Q), random(1,Q), random(1,Q)}}
	       C = CoefMat(M)
	  	
     Caveat
     	  Unlike coefficients function,this function only gives the coefficients matrix and not the
	  variable matrix. Nevertheless, the variable matrix has a fixed structure: A diagonal block
	  matrix where each diagonal block is a row matrix of interminates in the defined order. In our example,
	  variable matrix is 
	  $B = \begin{pmatrix} x&y&z&0&0&0 \\ 0&0&0&x&y&z \end{pmatrix}$. Note that $BC = M$. 
	  
     
///


------------------------------------------------------------
-- DOCUMENTATION alp
------------------------------------------------------------
doc ///
     Key
          alp
	 
     Headline
          computes appropriate binomial coefficients.  
     Usage
          C = alp(i,j)
     Inputs
	  i:ZZ
	  j:ZZ
	       	       
     Outputs
          C:ZZ
	       
     Description
          Text
	       $0$ if $i,j$ are odd. $\binom{1/2(i+j)}{i/2}$ if $i,j$ are even.
	       $\binom{1/2(i+j-1)}{i/2}$ if $i$ is even and $j$ is odd.  
	       $\binom{1/2(i+j-1)}{(i-1)/2}$ if $i$ is odd and $j$ is even. 
	       
	  Example
               C = alp(7,4)
	  	   
///

-- Function to pick coefficients in the desired order
CoefMat = (M) -> (
    m := numgens target M; -- number of rows
    n := numgens source M; -- number of columns
    ent := flatten entries vars ring M;
    cnt := length ent;
    zeros := matrix{{n:0}}; -- first dummy row
     -- first dummy row
    for i from 0 to (m-1) do(
	zeros = zeros||(coefficients (M^{i}, Monomials => ent))_1;
	);
    return zeros^{1..(cnt*m)}
    )

--Binomial coefficients needed for divided powers
alp = (i,j) ->(
    if (even i) and (even j) then binomial(substitute(((1/2)*(i+j)),ZZ) ,substitute(((1/2)*i),ZZ))
	else if (even i) and (odd j) then binomial(substitute(((1/2)*(i+j-1)),ZZ) ,substitute(((1/2)*i),ZZ))
	else if (odd i) and (even j) then binomial(substitute(((1/2)*(i+j-1)),ZZ) ,substitute(((1/2)*(i-1)),ZZ))
	else  0
)
