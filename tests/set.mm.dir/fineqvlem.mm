include "wcel.mm"
include "cfn.mm"
include "wn.mm"
include "wa.mm"
include "cpw.mm"
include "cvv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "pwexg.mm"
include "adantr.mm"
include "syl.mm"
include "cv.mm"
include "cen.mm"
include "crab.mm"
include "wss.mm"
include "ssrab2.mm"
include "wb.mm"
include "elpw2g.mm"
include "mpbiri.mm"
include "a1d.mm"
include "wceq.mm"
include "wi.mm"
include "wex.mm"
include "isinf.mm"
include "r19.21bi.mm"
include "ad2ant2lr.mm"
include "selpw.mm"
include "biimpri.mm"
include "anim1i.mm"
include "breq1.mm"
include "elrab.mm"
include "sylibr.mm"
include "eximi.mm"
include "eleq2.mm"
include "biimpcd.mm"
include "adantl.mm"
include "simprbi.mm"
include "ensym.mm"
include "entr.mm"
include "sylan.mm"
include "syl2an.mm"
include "ex.mm"
include "nneneq.mm"
include "biimpd.mm"
include "ad2antlr.mm"
include "3syld.mm"
include "exlimddv.mm"
include "breq2.mm"
include "rabbidv.mm"
include "impbid1.mm"
include "dom2d.mm"
include "mpd.mm"

theorem fineqvlem
  let cA: class A
  let cV: class V
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e


  assert |- ( ( A e. V /\ -. A e. Fin ) -> _om ~<_ ~P ~P A )

  proof
    cA
    cV
    wcel
    #
    cA
    cfn
    wcel
    wn
    #
    wa
    #
    cA
    cpw
    #
    cpw
    #
    cvv
    wcel
    #
    com
    @4
    cdom
    wbr
    @2
    @3
    cvv
    wcel
    #
    @5
    @0
    @6
    @1
    cA
    cV
    pwexg
    adantr
    #
    @3
    cvv
    pwexg
    syl
    @2
    vb
    vc
    com
    @4
    vd
    cv
    #
    vb
    cv
    #
    cen
    wbr
    #
    vd
    @3
    crab
    #
    @8
    vc
    cv
    #
    cen
    wbr
    #
    vd
    @3
    crab
    #
    cvv
    @2
    @11
    @4
    wcel
    #
    @9
    com
    wcel
    #
    @2
    @15
    @11
    @3
    wss
    #
    @10
    vd
    @3
    ssrab2
    @2
    @6
    @15
    @17
    wb
    @7
    @11
    @3
    cvv
    elpw2g
    syl
    mpbiri
    a1d
    @2
    @16
    @12
    com
    wcel
    #
    wa
    #
    @11
    @14
    wceq
    #
    @9
    @12
    wceq
    #
    wb
    @2
    @19
    wa
    #
    @20
    @21
    @22
    ve
    cv
    #
    @11
    wcel
    #
    @20
    @21
    wi
    ve
    @22
    @23
    cA
    wss
    #
    @23
    @9
    cen
    wbr
    #
    wa
    #
    ve
    wex
    #
    @24
    ve
    wex
    @1
    @16
    @28
    @0
    @18
    @1
    @28
    vb
    com
    ve
    cA
    vb
    isinf
    r19.21bi
    ad2ant2lr
    @27
    @24
    ve
    @27
    @23
    @3
    wcel
    #
    @26
    wa
    @24
    @25
    @29
    @26
    @29
    @25
    ve
    cA
    selpw
    biimpri
    anim1i
    @10
    @26
    vd
    @23
    @3
    @8
    @23
    @9
    cen
    breq1
    elrab
    #
    sylibr
    eximi
    syl
    @22
    @24
    wa
    @20
    @23
    @14
    wcel
    #
    @9
    @12
    cen
    wbr
    #
    @21
    @24
    @20
    @31
    wi
    @22
    @20
    @24
    @31
    @11
    @14
    @23
    eleq2
    biimpcd
    adantl
    @24
    @31
    @32
    wi
    @22
    @24
    @31
    @32
    @24
    @26
    @23
    @12
    cen
    wbr
    #
    @32
    @31
    @24
    @29
    @26
    @30
    simprbi
    @31
    @29
    @33
    @13
    @33
    vd
    @23
    @3
    @8
    @23
    @12
    cen
    breq1
    elrab
    simprbi
    @26
    @9
    @23
    cen
    wbr
    @33
    @32
    @23
    @9
    ensym
    @9
    @23
    @12
    entr
    sylan
    syl2an
    ex
    adantl
    @19
    @32
    @21
    wi
    @2
    @24
    @19
    @32
    @21
    @9
    @12
    nneneq
    biimpd
    ad2antlr
    3syld
    exlimddv
    @21
    @10
    @13
    vd
    @3
    @9
    @12
    @8
    cen
    breq2
    rabbidv
    impbid1
    ex
    dom2d
    mpd
end
