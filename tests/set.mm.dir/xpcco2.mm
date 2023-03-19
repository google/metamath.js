include "cop.mm"
include "co.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cxp.mm"
include "chom.mm"
include "xpcbas.mm"
include "eqid.mm"
include "wcel.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "xpchom2.mm"
include "eleqtrrd.mm"
include "xpcco.mm"
include "wceq.mm"
include "op1stg.mm"
include "opeq12d.mm"
include "oveq12d.mm"
include "oveq123d.mm"
include "op2ndg.mm"
include "eqtrd.mm"

theorem xpcco2
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.xb: class .xb
  let cT: class T
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cO: class O
  let cX: class X
  let cY: class Y
  assume xpcco2.t: |- T = ( C Xc. D )
  assume xpcco2.x: |- X = ( Base ` C )
  assume xpcco2.y: |- Y = ( Base ` D )
  assume xpcco2.h: |- H = ( Hom ` C )
  assume xpcco2.j: |- J = ( Hom ` D )
  assume xpcco2.m: |- ( ph -> M e. X )
  assume xpcco2.n: |- ( ph -> N e. Y )
  assume xpcco2.p: |- ( ph -> P e. X )
  assume xpcco2.q: |- ( ph -> Q e. Y )
  assume xpcco2.o1: |- .x. = ( comp ` C )
  assume xpcco2.o2: |- .xb = ( comp ` D )
  assume xpcco2.o: |- O = ( comp ` T )
  assume xpcco2.r: |- ( ph -> R e. X )
  assume xpcco2.s: |- ( ph -> S e. Y )
  assume xpcco2.f: |- ( ph -> F e. ( M H P ) )
  assume xpcco2.g: |- ( ph -> G e. ( N J Q ) )
  assume xpcco2.k: |- ( ph -> K e. ( P H R ) )
  assume xpcco2.l: |- ( ph -> L e. ( Q J S ) )


  assert |- ( ph -> ( <. K , L >. ( <. <. M , N >. , <. P , Q >. >. O <. R , S >. ) <. F , G >. ) = <. ( K ( <. M , P >. .x. R ) F ) , ( L ( <. N , Q >. .xb S ) G ) >. )

  proof
    wph
    cK
    cL
    cop
    #
    cF
    cG
    cop
    #
    cM
    cN
    cop
    #
    cP
    cQ
    cop
    #
    cop
    cR
    cS
    cop
    #
    cO
    co
    co
    @0
    c1st
    cfv
    #
    @1
    c1st
    cfv
    #
    @2
    c1st
    cfv
    #
    @3
    c1st
    cfv
    #
    cop
    #
    @4
    c1st
    cfv
    #
    c.x
    co
    #
    co
    #
    @0
    c2nd
    cfv
    #
    @1
    c2nd
    cfv
    #
    @2
    c2nd
    cfv
    #
    @3
    c2nd
    cfv
    #
    cop
    #
    @4
    c2nd
    cfv
    #
    c.xb
    co
    #
    co
    #
    cop
    cK
    cF
    cM
    cP
    cop
    #
    cR
    c.x
    co
    #
    co
    #
    cL
    cG
    cN
    cQ
    cop
    #
    cS
    c.xb
    co
    #
    co
    #
    cop
    wph
    cX
    cY
    cxp
    #
    cC
    cD
    c.xb
    cT
    c.x
    @1
    @0
    cT
    chom
    cfv
    #
    cO
    @2
    @3
    @4
    xpcco2.t
    cC
    cD
    cT
    cX
    cY
    xpcco2.t
    xpcco2.x
    xpcco2.y
    xpcbas
    @28
    eqid
    #
    xpcco2.o1
    xpcco2.o2
    xpcco2.o
    wph
    cM
    cX
    wcel
    #
    cN
    cY
    wcel
    #
    @2
    @27
    wcel
    xpcco2.m
    xpcco2.n
    cM
    cN
    cX
    cY
    opelxpi
    syl2anc
    wph
    cP
    cX
    wcel
    #
    cQ
    cY
    wcel
    #
    @3
    @27
    wcel
    xpcco2.p
    xpcco2.q
    cP
    cQ
    cX
    cY
    opelxpi
    syl2anc
    wph
    cR
    cX
    wcel
    #
    cS
    cY
    wcel
    #
    @4
    @27
    wcel
    xpcco2.r
    xpcco2.s
    cR
    cS
    cX
    cY
    opelxpi
    syl2anc
    wph
    @1
    cM
    cP
    cH
    co
    #
    cN
    cQ
    cJ
    co
    #
    cxp
    #
    @2
    @3
    @28
    co
    wph
    cF
    @36
    wcel
    #
    cG
    @37
    wcel
    #
    @1
    @38
    wcel
    xpcco2.f
    xpcco2.g
    cF
    cG
    @36
    @37
    opelxpi
    syl2anc
    wph
    cC
    cD
    cP
    cQ
    cT
    cH
    cJ
    @28
    cM
    cN
    cX
    cY
    xpcco2.t
    xpcco2.x
    xpcco2.y
    xpcco2.h
    xpcco2.j
    xpcco2.m
    xpcco2.n
    xpcco2.p
    xpcco2.q
    @29
    xpchom2
    eleqtrrd
    wph
    @0
    cP
    cR
    cH
    co
    #
    cQ
    cS
    cJ
    co
    #
    cxp
    #
    @3
    @4
    @28
    co
    wph
    cK
    @41
    wcel
    #
    cL
    @42
    wcel
    #
    @0
    @43
    wcel
    xpcco2.k
    xpcco2.l
    cK
    cL
    @41
    @42
    opelxpi
    syl2anc
    wph
    cC
    cD
    cR
    cS
    cT
    cH
    cJ
    @28
    cP
    cQ
    cX
    cY
    xpcco2.t
    xpcco2.x
    xpcco2.y
    xpcco2.h
    xpcco2.j
    xpcco2.p
    xpcco2.q
    xpcco2.r
    xpcco2.s
    @29
    xpchom2
    eleqtrrd
    xpcco
    wph
    @12
    @23
    @20
    @26
    wph
    @5
    cK
    @6
    cF
    @11
    @22
    wph
    @9
    @21
    @10
    cR
    c.x
    wph
    @7
    cM
    @8
    cP
    wph
    @30
    @31
    @7
    cM
    wceq
    xpcco2.m
    xpcco2.n
    cM
    cN
    cX
    cY
    op1stg
    syl2anc
    wph
    @32
    @33
    @8
    cP
    wceq
    xpcco2.p
    xpcco2.q
    cP
    cQ
    cX
    cY
    op1stg
    syl2anc
    opeq12d
    wph
    @34
    @35
    @10
    cR
    wceq
    xpcco2.r
    xpcco2.s
    cR
    cS
    cX
    cY
    op1stg
    syl2anc
    oveq12d
    wph
    @44
    @45
    @5
    cK
    wceq
    xpcco2.k
    xpcco2.l
    cK
    cL
    @41
    @42
    op1stg
    syl2anc
    wph
    @39
    @40
    @6
    cF
    wceq
    xpcco2.f
    xpcco2.g
    cF
    cG
    @36
    @37
    op1stg
    syl2anc
    oveq123d
    wph
    @13
    cL
    @14
    cG
    @19
    @25
    wph
    @17
    @24
    @18
    cS
    c.xb
    wph
    @15
    cN
    @16
    cQ
    wph
    @30
    @31
    @15
    cN
    wceq
    xpcco2.m
    xpcco2.n
    cM
    cN
    cX
    cY
    op2ndg
    syl2anc
    wph
    @32
    @33
    @16
    cQ
    wceq
    xpcco2.p
    xpcco2.q
    cP
    cQ
    cX
    cY
    op2ndg
    syl2anc
    opeq12d
    wph
    @34
    @35
    @18
    cS
    wceq
    xpcco2.r
    xpcco2.s
    cR
    cS
    cX
    cY
    op2ndg
    syl2anc
    oveq12d
    wph
    @44
    @45
    @13
    cL
    wceq
    xpcco2.k
    xpcco2.l
    cK
    cL
    @41
    @42
    op2ndg
    syl2anc
    wph
    @39
    @40
    @14
    cG
    wceq
    xpcco2.f
    xpcco2.g
    cF
    cG
    @36
    @37
    op2ndg
    syl2anc
    oveq123d
    opeq12d
    eqtrd
end
