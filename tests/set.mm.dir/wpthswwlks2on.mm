include "cusgr.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "cspthson.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "wex.mm"
include "c2.mm"
include "cwwlksnon.mm"
include "crab.mm"
include "cc0.mm"
include "wceq.mm"
include "cwwlksn.mm"
include "cwwspthsnon.mm"
include "w3a.mm"
include "wb.mm"
include "wwlknon.mm"
include "a1i.mm"
include "anbi1d.mm"
include "3anass.mm"
include "anbi1i.mm"
include "anass.mm"
include "bitri.mm"
include "syl6bb.mm"
include "rabbidva2.mm"
include "wi.mm"
include "cwlks.mm"
include "chash.mm"
include "cupgr.mm"
include "usgrupgr.mm"
include "wlklnwwlknupgr.mm"
include "syl.mm"
include "bicomd.mm"
include "adantr.mm"
include "cwlkson.mm"
include "simprl.mm"
include "fveq2.mm"
include "ad2antll.mm"
include "simprr.mm"
include "eqtrd.mm"
include "cvtx.mm"
include "cvv.mm"
include "cfz.mm"
include "wf.mm"
include "eqid.mm"
include "wlkp.mm"
include "oveq2.mm"
include "feq2d.mm"
include "syl5ibcom.mm"
include "imp.mm"
include "id.mm"
include "cn0.mm"
include "2nn0.mm"
include "0elfz.mm"
include "mp1i.mm"
include "ffvelrnd.mm"
include "nn0fz0.mm"
include "mpbi.mm"
include "jca.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "syl5ib.mm"
include "adantl.mm"
include "vex.mm"
include "pm3.2i.mm"
include "iswlkon.mm"
include "sylancl.mm"
include "mpbir3and.mm"
include "simplll.mm"
include "simpllr.mm"
include "usgr2wlkspth.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "ex.mm"
include "eximdv.mm"
include "com23.mm"
include "sylbid.mm"
include "pm4.71d.mm"
include "rabbidva.mm"
include "iswspthsnon.mm"
include "iswwlksnon.mm"
include "3eqtr4g.mm"

theorem wpthswwlks2on
  let cA: class A
  let cB: class B
  let cG: class G
  let vf: setvar f
  let vw: setvar w
  let cV: class V


  assert |- ( ( G e. USGraph /\ A =/= B ) -> ( A ( 2 WSPathsNOn G ) B ) = ( A ( 2 WWalksNOn G ) B ) )

  proof
    cG
    cusgr
    wcel
    #
    cA
    cB
    wne
    #
    wa
    #
    vf
    cv
    #
    vw
    cv
    #
    cA
    cB
    cG
    cspthson
    cfv
    co
    wbr
    #
    vf
    wex
    #
    vw
    cA
    cB
    c2
    cG
    cwwlksnon
    co
    co
    #
    crab
    #
    cc0
    @4
    cfv
    #
    cA
    wceq
    #
    c2
    @4
    cfv
    #
    cB
    wceq
    #
    wa
    #
    vw
    c2
    cG
    cwwlksn
    co
    #
    crab
    #
    cA
    cB
    c2
    cG
    cwwspthsnon
    co
    co
    @7
    @2
    @8
    @13
    @6
    wa
    #
    vw
    @14
    crab
    @15
    @2
    @6
    @16
    vw
    @7
    @14
    @2
    @4
    @7
    wcel
    #
    @6
    wa
    @4
    @14
    wcel
    #
    @10
    @12
    w3a
    #
    @6
    wa
    #
    @18
    @16
    wa
    #
    @2
    @17
    @19
    @6
    @17
    @19
    wb
    @2
    cA
    cB
    cG
    c2
    @4
    wwlknon
    a1i
    anbi1d
    @20
    @18
    @13
    wa
    #
    @6
    wa
    @21
    @19
    @22
    @6
    @18
    @10
    @12
    3anass
    anbi1i
    @18
    @13
    @6
    anass
    bitri
    syl6bb
    rabbidva2
    @2
    @16
    @13
    vw
    @14
    @2
    @18
    wa
    #
    @13
    @16
    @23
    @13
    @6
    @2
    @18
    @13
    @6
    wi
    #
    @2
    @18
    @3
    @4
    cG
    cwlks
    cfv
    wbr
    #
    @3
    chash
    cfv
    #
    c2
    wceq
    #
    wa
    #
    vf
    wex
    #
    @24
    @0
    @18
    @29
    wb
    @1
    @0
    @29
    @18
    @0
    cG
    cupgr
    wcel
    @29
    @18
    wb
    cG
    usgrupgr
    @4
    vf
    cG
    c2
    wlklnwwlknupgr
    syl
    bicomd
    adantr
    @2
    @13
    @29
    @6
    @2
    @13
    @29
    @6
    wi
    @2
    @13
    wa
    #
    @28
    @5
    vf
    @30
    @28
    @5
    @30
    @28
    wa
    #
    @3
    @4
    cA
    cB
    cG
    cwlkson
    cfv
    co
    wbr
    #
    @5
    @31
    @32
    @25
    @10
    @26
    @4
    cfv
    #
    cB
    wceq
    #
    @30
    @25
    @27
    simprl
    @30
    @10
    @28
    @2
    @10
    @12
    simprl
    adantr
    @31
    @33
    @11
    cB
    @27
    @33
    @11
    wceq
    @30
    @25
    @26
    c2
    @4
    fveq2
    ad2antll
    @30
    @12
    @28
    @2
    @10
    @12
    simprr
    adantr
    eqtrd
    @31
    cA
    cG
    cvtx
    cfv
    #
    wcel
    #
    cB
    @35
    wcel
    #
    wa
    #
    @3
    cvv
    wcel
    #
    @4
    cvv
    wcel
    #
    wa
    @32
    @25
    @10
    @34
    w3a
    wb
    @30
    @28
    @38
    @13
    @28
    @38
    wi
    @2
    @28
    @9
    @35
    wcel
    #
    @11
    @35
    wcel
    #
    wa
    #
    @13
    @38
    @28
    cc0
    c2
    cfz
    co
    #
    @35
    @4
    wf
    #
    @43
    @25
    @27
    @45
    @25
    cc0
    @26
    cfz
    co
    #
    @35
    @4
    wf
    @27
    @45
    @4
    @3
    cG
    @35
    @35
    eqid
    #
    wlkp
    @27
    @46
    @44
    @35
    @4
    @26
    c2
    cc0
    cfz
    oveq2
    feq2d
    syl5ibcom
    imp
    @45
    @41
    @42
    @45
    @44
    @35
    cc0
    @4
    @45
    id
    #
    c2
    cn0
    wcel
    #
    cc0
    @44
    wcel
    @45
    2nn0
    c2
    0elfz
    mp1i
    ffvelrnd
    @45
    @44
    @35
    c2
    @4
    @48
    c2
    @44
    wcel
    #
    @45
    @49
    @50
    2nn0
    c2
    nn0fz0
    mpbi
    a1i
    ffvelrnd
    jca
    syl
    @10
    @41
    @36
    @12
    @42
    @37
    @9
    cA
    @35
    eleq1
    @11
    cB
    @35
    eleq1
    bi2anan9
    syl5ib
    adantl
    imp
    @39
    @40
    vf
    vex
    vw
    vex
    pm3.2i
    cA
    cB
    @4
    cvv
    @3
    cG
    @35
    cvv
    @47
    iswlkon
    sylancl
    mpbir3and
    @31
    @0
    @27
    @1
    @32
    @5
    wb
    @0
    @1
    @13
    @28
    simplll
    @30
    @25
    @27
    simprr
    @0
    @1
    @13
    @28
    simpllr
    cA
    cB
    @4
    @3
    cG
    usgr2wlkspth
    syl3anc
    mpbid
    ex
    eximdv
    ex
    com23
    sylbid
    imp
    pm4.71d
    bicomd
    rabbidva
    eqtrd
    vw
    cA
    cB
    vf
    cG
    c2
    @35
    @47
    iswspthsnon
    vw
    cA
    cB
    cG
    c2
    @35
    @47
    iswwlksnon
    3eqtr4g
end
