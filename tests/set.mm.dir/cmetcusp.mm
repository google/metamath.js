include "c0.mm"
include "wne.mm"
include "cms.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cmetu.mm"
include "ctus.mm"
include "cusp.mm"
include "cv.mm"
include "cuss.mm"
include "ccfilu.mm"
include "ctopn.mm"
include "cflim.mm"
include "co.mm"
include "wi.mm"
include "cbs.mm"
include "cfil.mm"
include "wral.mm"
include "ccusp.mm"
include "cpsmet.mm"
include "cust.mm"
include "cme.mm"
include "cxmt.mm"
include "cmetmet.mm"
include "metxmet.mm"
include "xmetpsmet.mm"
include "3syl.mm"
include "anim2i.mm"
include "metuust.mm"
include "eqid.mm"
include "tususp.mm"
include "cmopn.mm"
include "simpll.mm"
include "ccfil.mm"
include "simprd.mm"
include "cxp.mm"
include "cima.mm"
include "cc0.mm"
include "cico.mm"
include "wss.mm"
include "wrex.mm"
include "crp.mm"
include "syl.mm"
include "ad3antlr.mm"
include "wb.mm"
include "tusbas.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "adantr.mm"
include "wceq.mm"
include "tususs.mm"
include "adantlr.mm"
include "cfbas.mm"
include "cfilucfil2.mm"
include "simplbda.mm"
include "syl2anc.mm"
include "iscfil.mm"
include "syl12anc.mm"
include "cmetcvg.mm"
include "cutop.mm"
include "tustopn.mm"
include "xmetutop.mm"
include "eqtr3d.mm"
include "oveq1d.mm"
include "neeq1d.mm"
include "ex.mm"
include "ralrimiva.mm"
include "iscusp.mm"
include "sylanbrc.mm"

theorem cmetcusp
  let cD: class D
  let cX: class X
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( X =/= (/) /\ D e. ( CMet ` X ) ) -> ( toUnifSp ` ( metUnif ` D ) ) e. CUnifSp )

  proof
    cX
    c0
    wne
    #
    cD
    cX
    cms
    cfv
    wcel
    #
    wa
    #
    cD
    cmetu
    cfv
    #
    ctus
    cfv
    #
    cusp
    wcel
    #
    vc
    cv
    #
    @4
    cuss
    cfv
    #
    ccfilu
    cfv
    #
    wcel
    #
    @4
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
    @4
    cbs
    cfv
    #
    cfil
    cfv
    #
    wral
    @4
    ccusp
    wcel
    @2
    @0
    cD
    cX
    cpsmet
    cfv
    wcel
    #
    wa
    #
    @3
    cX
    cust
    cfv
    wcel
    #
    @5
    @1
    @16
    @0
    @1
    cD
    cX
    cme
    cfv
    wcel
    #
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @16
    cD
    cX
    cmetmet
    #
    cD
    cX
    metxmet
    #
    cD
    cX
    xmetpsmet
    3syl
    anim2i
    #
    cD
    cX
    metuust
    #
    @3
    @4
    cX
    @4
    eqid
    #
    tususp
    3syl
    @2
    @13
    vc
    @15
    @2
    @6
    @15
    wcel
    #
    wa
    #
    @9
    @12
    @27
    @9
    wa
    #
    @2
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
    @12
    @2
    @26
    @9
    simpll
    #
    @28
    @1
    @6
    cD
    ccfil
    cfv
    wcel
    #
    @31
    @28
    @0
    @1
    @32
    simprd
    @28
    @20
    @6
    cX
    cfil
    cfv
    #
    wcel
    #
    cD
    vy
    cv
    #
    @36
    cxp
    cima
    cc0
    vx
    cv
    cico
    co
    wss
    vy
    @6
    wrex
    vx
    crp
    wral
    #
    @33
    @1
    @20
    @0
    @26
    @9
    @1
    @19
    @20
    @21
    @22
    syl
    #
    ad3antlr
    @27
    @35
    @9
    @2
    @35
    @26
    @2
    @17
    @18
    @35
    @26
    wb
    @23
    @24
    @18
    @34
    @15
    @6
    @18
    cX
    @14
    cfil
    @3
    @4
    cX
    @25
    tusbas
    fveq2d
    eleq2d
    3syl
    biimpar
    adantr
    @28
    @2
    @6
    @3
    ccfilu
    cfv
    #
    wcel
    #
    @37
    @32
    @2
    @9
    @40
    @26
    @2
    @40
    @9
    @2
    @39
    @8
    @6
    @2
    @17
    @18
    @39
    @8
    wceq
    @23
    @24
    @18
    @3
    @7
    ccfilu
    @3
    @4
    cX
    @25
    tususs
    fveq2d
    3syl
    eleq2d
    biimpar
    adantlr
    @2
    @40
    @6
    cX
    cfbas
    cfv
    wcel
    #
    @37
    @2
    @17
    @40
    @41
    @37
    wa
    wb
    @23
    vx
    vy
    @6
    cD
    cX
    cfilucfil2
    syl
    simplbda
    syl2anc
    @20
    @33
    @35
    @37
    wa
    vx
    vy
    cD
    @6
    cX
    iscfil
    biimpar
    syl12anc
    cD
    @6
    @29
    cX
    @29
    eqid
    cmetcvg
    syl2anc
    @2
    @12
    @31
    @2
    @11
    @30
    c0
    @2
    @10
    @29
    @6
    cflim
    @2
    @3
    cutop
    cfv
    #
    @10
    @29
    @2
    @17
    @18
    @42
    @10
    wceq
    @23
    @24
    @3
    @42
    @4
    cX
    @25
    @42
    eqid
    tustopn
    3syl
    @2
    @0
    @20
    wa
    @42
    @29
    wceq
    @1
    @20
    @0
    @38
    anim2i
    cD
    cX
    xmetutop
    syl
    eqtr3d
    oveq1d
    neeq1d
    biimpar
    syl2anc
    ex
    ralrimiva
    @4
    vc
    iscusp
    sylanbrc
end
