include "ccat.mm"
include "wcel.mm"
include "wa.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cop.mm"
include "cful.mm"
include "co.mm"
include "cfth.mm"
include "cin.mm"
include "cfunc.mm"
include "wrel.mm"
include "wceq.mm"
include "relfunc.mm"
include "cress.mm"
include "resscat.mm"
include "syl5eqel.mm"
include "idfucl.mm"
include "syl.mm"
include "1st2nd.mm"
include "sylancr.mm"
include "wbr.mm"
include "cv.mm"
include "chom.mm"
include "wf1o.mm"
include "cbs.mm"
include "wral.mm"
include "chomf.mm"
include "cxp.mm"
include "cres.mm"
include "cresc.mm"
include "cvv.mm"
include "eqidd.mm"
include "ccomf.mm"
include "eqid.mm"
include "ressinbas.mm"
include "adantl.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "simpl.mm"
include "wss.mm"
include "inss2.mm"
include "a1i.mm"
include "fullresc.mm"
include "simpld.mm"
include "eqtrd.mm"
include "simprd.mm"
include "ovex.mm"
include "eqeltri.mm"
include "funcpropd.mm"
include "csubc.mm"
include "fullsubc.mm"
include "funcres2.mm"
include "eqsstrd.mm"
include "sseldd.mm"
include "eqeltrrd.mm"
include "df-br.mm"
include "sylibr.mm"
include "cid.mm"
include "f1oi.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "idfu2nd.mm"
include "resshom.mm"
include "ad2antlr.mm"
include "idfu1.mm"
include "oveq123d.mm"
include "f1oeq123d.mm"
include "mpbiri.mm"
include "ralrimivva.mm"
include "isffth2.mm"
include "sylanbrc.mm"
include "sylib.mm"
include "eqeltrd.mm"

theorem ressffth
  let cC: class C
  let cD: class D
  let cS: class S
  let cI: class I
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume ressffth.d: |- D = ( C |`s S )
  assume ressffth.i: |- I = ( idFunc ` D )


  assert |- ( ( C e. Cat /\ S e. V ) -> I e. ( ( D Full C ) i^i ( D Faith C ) ) )

  proof
    cC
    ccat
    wcel
    #
    cS
    cV
    wcel
    #
    wa
    #
    cI
    cI
    c1st
    cfv
    #
    cI
    c2nd
    cfv
    #
    cop
    #
    cD
    cC
    cful
    co
    cD
    cC
    cfth
    co
    cin
    #
    @2
    cD
    cD
    cfunc
    co
    #
    wrel
    cI
    @7
    wcel
    #
    cI
    @5
    wceq
    cD
    cD
    relfunc
    @2
    cD
    ccat
    wcel
    #
    @8
    @2
    cD
    cC
    cS
    cress
    co
    #
    ccat
    ressffth.d
    cC
    cS
    cV
    resscat
    syl5eqel
    #
    cD
    cI
    ressffth.i
    idfucl
    syl
    #
    cI
    @7
    1st2nd
    sylancr
    #
    @2
    @3
    @4
    @6
    wbr
    #
    @5
    @6
    wcel
    @2
    @3
    @4
    cD
    cC
    cfunc
    co
    #
    wbr
    #
    vx
    cv
    #
    vy
    cv
    #
    cD
    chom
    cfv
    #
    co
    #
    @17
    @3
    cfv
    #
    @18
    @3
    cfv
    #
    cC
    chom
    cfv
    #
    co
    #
    @17
    @18
    @4
    co
    #
    wf1o
    #
    vy
    cD
    cbs
    cfv
    #
    wral
    vx
    @27
    wral
    @14
    @2
    @5
    @15
    wcel
    @16
    @2
    cI
    @5
    @15
    @13
    @2
    @7
    @15
    cI
    @2
    @7
    cD
    cC
    cC
    chomf
    cfv
    #
    cS
    cC
    cbs
    cfv
    #
    cin
    #
    @30
    cxp
    cres
    #
    cresc
    co
    #
    cfunc
    co
    #
    @15
    @2
    cD
    cD
    cD
    @32
    cvv
    @2
    cD
    chomf
    cfv
    #
    eqidd
    @2
    cD
    ccomf
    cfv
    #
    eqidd
    @2
    @34
    cC
    @30
    cress
    co
    #
    chomf
    cfv
    #
    @32
    chomf
    cfv
    #
    @2
    cD
    @36
    chomf
    @2
    cD
    @10
    @36
    ressffth.d
    @1
    @10
    @36
    wceq
    @0
    cS
    @29
    cC
    cV
    @29
    eqid
    #
    ressinbas
    adantl
    syl5eq
    #
    fveq2d
    @2
    @37
    @38
    wceq
    #
    @36
    ccomf
    cfv
    #
    @32
    ccomf
    cfv
    #
    wceq
    #
    @2
    @29
    cC
    @36
    @30
    @32
    @28
    @39
    @28
    eqid
    #
    @0
    @1
    simpl
    #
    @30
    @29
    wss
    @2
    cS
    @29
    inss2
    a1i
    #
    @36
    eqid
    @32
    eqid
    fullresc
    #
    simpld
    eqtrd
    @2
    @35
    @42
    @43
    @2
    cD
    @36
    ccomf
    @40
    fveq2d
    @2
    @41
    @44
    @48
    simprd
    eqtrd
    cD
    cvv
    wcel
    @2
    cD
    @10
    cvv
    ressffth.d
    cC
    cS
    cress
    ovex
    eqeltri
    a1i
    #
    @49
    @49
    @32
    cvv
    wcel
    @2
    cC
    @31
    cresc
    ovex
    a1i
    funcpropd
    @2
    @31
    cC
    csubc
    cfv
    wcel
    @33
    @15
    wss
    @2
    @29
    cC
    @30
    @28
    @39
    @45
    @46
    @47
    fullsubc
    cD
    cC
    @31
    funcres2
    syl
    eqsstrd
    @12
    sseldd
    eqeltrrd
    @3
    @4
    @15
    df-br
    sylibr
    @2
    @26
    vx
    vy
    @27
    @27
    @2
    @17
    @27
    wcel
    #
    @18
    @27
    wcel
    #
    wa
    #
    wa
    #
    @26
    @20
    @20
    cid
    @20
    cres
    #
    wf1o
    @20
    f1oi
    @53
    @20
    @20
    @24
    @20
    @25
    @54
    @53
    @27
    cD
    @19
    cI
    @17
    @18
    ressffth.i
    @27
    eqid
    #
    @2
    @9
    @52
    @11
    adantr
    #
    @19
    eqid
    #
    @2
    @50
    @51
    simprl
    #
    @2
    @50
    @51
    simprr
    #
    idfu2nd
    @53
    @20
    eqidd
    @53
    @21
    @17
    @22
    @18
    @23
    @19
    @1
    @23
    @19
    wceq
    @0
    @52
    cS
    cC
    cD
    @23
    cV
    ressffth.d
    @23
    eqid
    #
    resshom
    ad2antlr
    @53
    @27
    cD
    cI
    @17
    ressffth.i
    @55
    @56
    @58
    idfu1
    @53
    @27
    cD
    cI
    @18
    ressffth.i
    @55
    @56
    @59
    idfu1
    oveq123d
    f1oeq123d
    mpbiri
    ralrimivva
    vx
    vy
    @27
    cD
    cC
    @3
    @4
    @19
    @23
    @55
    @57
    @60
    isffth2
    sylanbrc
    @3
    @4
    @6
    df-br
    sylib
    eqeltrd
end
