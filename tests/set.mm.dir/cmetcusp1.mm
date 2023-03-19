include "c0.mm"
include "wne.mm"
include "ccms.mm"
include "wcel.mm"
include "cmetu.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cusp.mm"
include "cv.mm"
include "ccfilu.mm"
include "ctopn.mm"
include "cflim.mm"
include "co.mm"
include "wi.mm"
include "cfil.mm"
include "wral.mm"
include "ccusp.mm"
include "cxme.mm"
include "cmt.mm"
include "cmsms.mm"
include "msxms.mm"
include "syl.mm"
include "xmsusp.mm"
include "syl3an2.mm"
include "wa.mm"
include "ccfil.mm"
include "simpl3.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "cxmt.mm"
include "wb.mm"
include "simpl1.mm"
include "cms.mm"
include "cme.mm"
include "cmscmet.mm"
include "cmetmet.mm"
include "metxmet.mm"
include "3syl.mm"
include "3ad2ant2.mm"
include "adantr.mm"
include "simpr.mm"
include "cfilucfil4.mm"
include "syl3anc.mm"
include "bitrd.mm"
include "cmopn.mm"
include "eqid.mm"
include "iscmet.mm"
include "simprbi.mm"
include "xmstopn.mm"
include "oveq1d.mm"
include "neeq1d.mm"
include "ralbidv.mm"
include "mpbird.mm"
include "r19.21bi.mm"
include "ex.mm"
include "sylbid.mm"
include "ralrimiva.mm"
include "iscusp2.mm"
include "sylanbrc.mm"

theorem cmetcusp1
  let cD: class D
  let cU: class U
  let cF: class F
  let cX: class X
  let vc: setvar c
  assume cmetcusp1.x: |- X = ( Base ` F )
  assume cmetcusp1.d: |- D = ( ( dist ` F ) |` ( X X. X ) )
  assume cmetcusp1.u: |- U = ( UnifSt ` F )


  assert |- ( ( X =/= (/) /\ F e. CMetSp /\ U = ( metUnif ` D ) ) -> F e. CUnifSp )

  proof
    cX
    c0
    wne
    #
    cF
    ccms
    wcel
    #
    cU
    cD
    cmetu
    cfv
    #
    wceq
    #
    w3a
    #
    cF
    cusp
    wcel
    #
    vc
    cv
    #
    cU
    ccfilu
    cfv
    #
    wcel
    #
    cF
    ctopn
    cfv
    #
    @6
    cflim
    co
    #
    c0
    wne
    #
    wi
    #
    vc
    cX
    cfil
    cfv
    #
    wral
    cF
    ccusp
    wcel
    @1
    @0
    cF
    cxme
    wcel
    #
    @3
    @5
    @1
    cF
    cmt
    wcel
    @14
    cF
    cmsms
    cF
    msxms
    syl
    #
    cD
    cU
    cF
    cX
    cmetcusp1.x
    cmetcusp1.d
    cmetcusp1.u
    xmsusp
    syl3an2
    @4
    @12
    vc
    @13
    @4
    @6
    @13
    wcel
    #
    wa
    #
    @8
    @6
    cD
    ccfil
    cfv
    #
    wcel
    #
    @11
    @17
    @8
    @6
    @2
    ccfilu
    cfv
    #
    wcel
    #
    @19
    @17
    @7
    @20
    @6
    @17
    cU
    @2
    ccfilu
    @0
    @1
    @3
    @16
    simpl3
    fveq2d
    eleq2d
    @17
    @0
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @16
    @21
    @19
    wb
    @0
    @1
    @3
    @16
    simpl1
    @4
    @22
    @16
    @1
    @0
    @22
    @3
    @1
    cD
    cX
    cms
    cfv
    wcel
    #
    cD
    cX
    cme
    cfv
    wcel
    #
    @22
    cD
    cF
    cX
    cmetcusp1.x
    cmetcusp1.d
    cmscmet
    #
    cD
    cX
    cmetmet
    cD
    cX
    metxmet
    3syl
    3ad2ant2
    adantr
    @4
    @16
    simpr
    @6
    cD
    cX
    cfilucfil4
    syl3anc
    bitrd
    @4
    @19
    @11
    wi
    #
    @16
    @1
    @0
    @26
    @3
    @1
    @19
    @11
    @1
    @11
    vc
    @18
    @1
    @11
    vc
    @18
    wral
    cD
    cmopn
    cfv
    #
    @6
    cflim
    co
    #
    c0
    wne
    #
    vc
    @18
    wral
    #
    @1
    @23
    @30
    @25
    @23
    @24
    @30
    cD
    vc
    @27
    cX
    @27
    eqid
    iscmet
    simprbi
    syl
    @1
    @11
    @29
    vc
    @18
    @1
    @10
    @28
    c0
    @1
    @9
    @27
    @6
    cflim
    @1
    @14
    @9
    @27
    wceq
    @15
    cD
    @9
    cF
    cX
    @9
    eqid
    #
    cmetcusp1.x
    cmetcusp1.d
    xmstopn
    syl
    oveq1d
    neeq1d
    ralbidv
    mpbird
    r19.21bi
    ex
    3ad2ant2
    adantr
    sylbid
    ralrimiva
    cX
    cU
    @9
    cF
    vc
    cmetcusp1.x
    cmetcusp1.u
    @31
    iscusp2
    sylanbrc
end
