include "co.mm"
include "wcel.mm"
include "cful.mm"
include "cfth.mm"
include "cin.mm"
include "cbs.mm"
include "cfv.mm"
include "c1st.mm"
include "wf1o.mm"
include "c2nd.mm"
include "cop.mm"
include "cfunc.mm"
include "wrel.mm"
include "wceq.mm"
include "relfunc.mm"
include "ccat.mm"
include "catcbas.mm"
include "inss2.mm"
include "syl6eqss.mm"
include "sseldd.mm"
include "yoncl.mm"
include "1st2nd.mm"
include "sylancr.mm"
include "yonffth.mm"
include "eqeltrrd.mm"
include "wbr.mm"
include "crn.mm"
include "cvv.mm"
include "eqid.mm"
include "oppccat.mm"
include "syl.mm"
include "setccat.mm"
include "fuccat.mm"
include "fvex.mm"
include "rnex.mm"
include "a1i.mm"
include "wfn.mm"
include "wf.mm"
include "fucbas.mm"
include "1st2ndbr.mm"
include "funcf1.mm"
include "ffn.mm"
include "dffn3.mm"
include "sylib.mm"
include "ffthres2c.mm"
include "df-br.mm"
include "3bitr3g.mm"
include "mpbid.mm"
include "eqeltrd.mm"
include "wf1.mm"
include "cv.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "fveq2d.mm"
include "simpl.mm"
include "jca.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "id.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "chom.mm"
include "adantr.mm"
include "simprr.mm"
include "simprl.mm"
include "yon11.mm"
include "eqtrd.mm"
include "chvarv.mm"
include "sylan2.mm"
include "syl5ib.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"
include "f1f1orn.mm"
include "wb.mm"
include "wss.mm"
include "frn.mm"
include "ressbas2.mm"
include "f1oeq3.mm"
include "catciso.mm"
include "mpbir2and.mm"

theorem yoniso
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cS: class S
  let cU: class U
  let cE: class E
  let cF: class F
  let cI: class I
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume yoniso.y: |- Y = ( Yon ` C )
  assume yoniso.o: |- O = ( oppCat ` C )
  assume yoniso.s: |- S = ( SetCat ` U )
  assume yoniso.d: |- D = ( CatCat ` V )
  assume yoniso.b: |- B = ( Base ` D )
  assume yoniso.i: |- I = ( Iso ` D )
  assume yoniso.q: |- Q = ( O FuncCat S )
  assume yoniso.e: |- E = ( Q |`s ran ( 1st ` Y ) )
  assume yoniso.v: |- ( ph -> V e. X )
  assume yoniso.c: |- ( ph -> C e. B )
  assume yoniso.u: |- ( ph -> U e. W )
  assume yoniso.h: |- ( ph -> ran ( Homf ` C ) C_ U )
  assume yoniso.eb: |- ( ph -> E e. B )
  assume yoniso.1: |- ( ( ph /\ ( x e. ( Base ` C ) /\ y e. ( Base ` C ) ) ) -> ( F ` ( x ( Hom ` C ) y ) ) = y )

  disjoint x y
  disjoint C x
  disjoint C y
  disjoint F y
  disjoint ph x
  disjoint ph y
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> Y e. ( C I E ) )

  proof
    wph
    cY
    cC
    cE
    cI
    co
    wcel
    cY
    cC
    cE
    cful
    co
    cC
    cE
    cfth
    co
    cin
    #
    wcel
    cC
    cbs
    cfv
    #
    cE
    cbs
    cfv
    #
    cY
    c1st
    cfv
    #
    wf1o
    #
    wph
    cY
    @3
    cY
    c2nd
    cfv
    #
    cop
    #
    @0
    wph
    cC
    cQ
    cfunc
    co
    #
    wrel
    #
    cY
    @7
    wcel
    #
    cY
    @6
    wceq
    cC
    cQ
    relfunc
    #
    wph
    cC
    cQ
    cS
    cU
    cO
    cW
    cY
    yoniso.y
    wph
    cB
    ccat
    cC
    wph
    cB
    cV
    ccat
    cin
    ccat
    wph
    cB
    cD
    cV
    cX
    yoniso.d
    yoniso.b
    yoniso.v
    catcbas
    cV
    ccat
    inss2
    syl6eqss
    yoniso.c
    sseldd
    #
    yoniso.o
    yoniso.s
    yoniso.q
    yoniso.u
    yoniso.h
    yoncl
    #
    cY
    @7
    1st2nd
    sylancr
    #
    wph
    @6
    cC
    cQ
    cful
    co
    cC
    cQ
    cfth
    co
    cin
    #
    wcel
    #
    @6
    @0
    wcel
    #
    wph
    cY
    @6
    @14
    @13
    wph
    cC
    cQ
    cS
    cU
    cO
    cW
    cY
    yoniso.y
    yoniso.o
    yoniso.s
    yoniso.q
    @11
    yoniso.u
    yoniso.h
    yonffth
    eqeltrrd
    wph
    @3
    @5
    @14
    wbr
    @3
    @5
    @0
    wbr
    @15
    @16
    wph
    @1
    cC
    cQ
    @3
    crn
    #
    cE
    @3
    @5
    cvv
    @1
    eqid
    #
    yoniso.e
    wph
    cO
    cS
    cQ
    yoniso.q
    wph
    cC
    ccat
    wcel
    #
    cO
    ccat
    wcel
    @11
    cC
    cO
    yoniso.o
    oppccat
    syl
    wph
    cU
    cW
    wcel
    cS
    ccat
    wcel
    yoniso.u
    cS
    cU
    cW
    yoniso.s
    setccat
    syl
    fuccat
    @17
    cvv
    wcel
    wph
    @3
    cY
    c1st
    fvex
    rnex
    a1i
    wph
    @3
    @1
    wfn
    #
    @1
    @17
    @3
    wf
    wph
    @1
    cO
    cS
    cfunc
    co
    #
    @3
    wf
    #
    @20
    wph
    @1
    @21
    cC
    cQ
    @3
    @5
    @18
    cO
    cS
    cQ
    yoniso.q
    fucbas
    #
    wph
    @8
    @9
    @3
    @5
    @7
    wbr
    @10
    @12
    cY
    @7
    1st2ndbr
    sylancr
    funcf1
    #
    @1
    @21
    @3
    ffn
    syl
    @1
    @3
    dffn3
    sylib
    ffthres2c
    @3
    @5
    @14
    df-br
    @3
    @5
    @0
    df-br
    3bitr3g
    mpbid
    eqeltrd
    wph
    @1
    @17
    @3
    wf1o
    #
    @4
    wph
    @1
    @21
    @3
    wf1
    #
    @25
    wph
    @22
    vx
    cv
    #
    @3
    cfv
    #
    vy
    cv
    #
    @3
    cfv
    #
    wceq
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    @1
    wral
    vx
    @1
    wral
    @26
    @24
    wph
    @33
    vx
    vy
    @1
    @1
    @31
    @27
    @28
    c1st
    cfv
    #
    cfv
    #
    cF
    cfv
    #
    @27
    @30
    c1st
    cfv
    #
    cfv
    #
    cF
    cfv
    #
    wceq
    wph
    @27
    @1
    wcel
    #
    @29
    @1
    wcel
    #
    wa
    #
    wa
    #
    @32
    @31
    @35
    @38
    cF
    @31
    @27
    @34
    @37
    @28
    @30
    c1st
    fveq2
    fveq1d
    fveq2d
    @43
    @36
    @27
    @39
    @29
    @42
    wph
    @40
    @40
    wa
    #
    @36
    @27
    wceq
    #
    @42
    @40
    @40
    @40
    @41
    simpl
    #
    @46
    jca
    @43
    @39
    @29
    wceq
    #
    wi
    wph
    @44
    wa
    #
    @45
    wi
    vy
    vx
    vy
    vx
    weq
    #
    @43
    @48
    @47
    @45
    @49
    @42
    @44
    wph
    @49
    @41
    @40
    @40
    @29
    @27
    @1
    eleq1
    anbi2d
    anbi2d
    @49
    @39
    @36
    @29
    @27
    @49
    @38
    @35
    cF
    @49
    @27
    @37
    @34
    @49
    @30
    @28
    c1st
    @29
    @27
    @3
    fveq2
    fveq2d
    fveq1d
    fveq2d
    @49
    id
    eqeq12d
    imbi12d
    @43
    @39
    @27
    @29
    cC
    chom
    cfv
    #
    co
    #
    cF
    cfv
    @29
    @43
    @38
    @51
    cF
    @43
    @1
    cC
    @50
    @29
    cY
    @27
    yoniso.y
    @18
    wph
    @19
    @42
    @11
    adantr
    wph
    @40
    @41
    simprr
    @50
    eqid
    wph
    @40
    @41
    simprl
    yon11
    fveq2d
    yoniso.1
    eqtrd
    #
    chvarv
    sylan2
    @52
    eqeq12d
    syl5ib
    ralrimivva
    vx
    vy
    @1
    @21
    @3
    dff13
    sylanbrc
    @1
    @21
    @3
    f1f1orn
    syl
    wph
    @17
    @2
    wceq
    #
    @25
    @4
    wb
    wph
    @17
    @21
    wss
    #
    @53
    wph
    @22
    @54
    @24
    @1
    @21
    @3
    frn
    syl
    @17
    @21
    cE
    cQ
    yoniso.e
    @23
    ressbas2
    syl
    @17
    @2
    @1
    @3
    f1oeq3
    syl
    mpbid
    wph
    cB
    cD
    @1
    @2
    cV
    cY
    cI
    cX
    cC
    cE
    yoniso.d
    yoniso.b
    @18
    @2
    eqid
    yoniso.v
    yoniso.c
    yoniso.eb
    yoniso.i
    catciso
    mpbir2and
end
