include "cusgr.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
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
include "wb.mm"
include "wwlknonOLD.mm"
include "3ad2ant2.mm"
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
include "3ad2ant1.mm"
include "cwlkson.mm"
include "simprl.mm"
include "adantr.mm"
include "fveq2.mm"
include "ad2antll.mm"
include "simprr.mm"
include "eqtrd.mm"
include "cvv.mm"
include "simpll2.mm"
include "vex.mm"
include "pm3.2i.mm"
include "iswlkon.mm"
include "sylancl.mm"
include "mpbir3and.mm"
include "simpll1.mm"
include "simpll3.mm"
include "usgr2wlkspth.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "ex.mm"
include "eximdv.mm"
include "com23.mm"
include "sylbid.mm"
include "imp.mm"
include "pm4.71d.mm"
include "rabbidva.mm"
include "iswspthsnonOLD.mm"
include "iswwlksnonOLD.mm"
include "3eqtr4d.mm"

theorem wpthswwlks2onOLD
  let cA: class A
  let cB: class B
  let cG: class G
  let cV: class V
  let vf: setvar f
  let vw: setvar w
  assume wpthswwlks2onOLD.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. USGraph /\ ( A e. V /\ B e. V ) /\ A =/= B ) -> ( A ( 2 WSPathsNOn G ) B ) = ( A ( 2 WWalksNOn G ) B ) )

  proof
    cG
    cusgr
    wcel
    #
    cA
    cV
    wcel
    cB
    cV
    wcel
    wa
    #
    cA
    cB
    wne
    #
    w3a
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
    @5
    cfv
    cA
    wceq
    #
    c2
    @5
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
    #
    @8
    @3
    @9
    @13
    @7
    wa
    #
    vw
    @14
    crab
    @15
    @3
    @7
    @17
    vw
    @8
    @14
    @3
    @5
    @8
    wcel
    #
    @7
    wa
    @5
    @14
    wcel
    #
    @10
    @12
    w3a
    #
    @7
    wa
    #
    @19
    @17
    wa
    #
    @3
    @18
    @20
    @7
    @1
    @0
    @18
    @20
    wb
    @2
    cA
    cB
    cG
    c2
    cV
    @5
    wpthswwlks2onOLD.v
    wwlknonOLD
    3ad2ant2
    anbi1d
    @21
    @19
    @13
    wa
    #
    @7
    wa
    @22
    @20
    @23
    @7
    @19
    @10
    @12
    3anass
    anbi1i
    @19
    @13
    @7
    anass
    bitri
    syl6bb
    rabbidva2
    @3
    @17
    @13
    vw
    @14
    @3
    @19
    wa
    #
    @13
    @17
    @24
    @13
    @7
    @3
    @19
    @13
    @7
    wi
    #
    @3
    @19
    @4
    @5
    cG
    cwlks
    cfv
    wbr
    #
    @4
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
    @25
    @0
    @1
    @19
    @30
    wb
    @2
    @0
    @30
    @19
    @0
    cG
    cupgr
    wcel
    @30
    @19
    wb
    cG
    usgrupgr
    @5
    vf
    cG
    c2
    wlklnwwlknupgr
    syl
    bicomd
    3ad2ant1
    @3
    @13
    @30
    @7
    @3
    @13
    @30
    @7
    wi
    @3
    @13
    wa
    #
    @29
    @6
    vf
    @31
    @29
    @6
    @31
    @29
    wa
    #
    @4
    @5
    cA
    cB
    cG
    cwlkson
    cfv
    co
    wbr
    #
    @6
    @32
    @33
    @26
    @10
    @27
    @5
    cfv
    #
    cB
    wceq
    #
    @31
    @26
    @28
    simprl
    @31
    @10
    @29
    @3
    @10
    @12
    simprl
    adantr
    @32
    @34
    @11
    cB
    @28
    @34
    @11
    wceq
    @31
    @26
    @27
    c2
    @5
    fveq2
    ad2antll
    @31
    @12
    @29
    @3
    @10
    @12
    simprr
    adantr
    eqtrd
    @32
    @1
    @4
    cvv
    wcel
    #
    @5
    cvv
    wcel
    #
    wa
    @33
    @26
    @10
    @35
    w3a
    wb
    @0
    @1
    @2
    @13
    @29
    simpll2
    @36
    @37
    vf
    vex
    vw
    vex
    pm3.2i
    cA
    cB
    @5
    cvv
    @4
    cG
    cV
    cvv
    wpthswwlks2onOLD.v
    iswlkon
    sylancl
    mpbir3and
    @32
    @0
    @28
    @2
    @33
    @6
    wb
    @0
    @1
    @2
    @13
    @29
    simpll1
    @31
    @26
    @28
    simprr
    @0
    @1
    @2
    @13
    @29
    simpll3
    cA
    cB
    @5
    @4
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
    @1
    @0
    @16
    @9
    wceq
    @2
    vw
    cA
    cB
    vf
    cG
    c2
    cV
    wpthswwlks2onOLD.v
    iswspthsnonOLD
    3ad2ant2
    @1
    @0
    @8
    @15
    wceq
    @2
    vw
    cA
    cB
    cG
    c2
    cV
    wpthswwlks2onOLD.v
    iswwlksnonOLD
    3ad2ant2
    3eqtr4d
end
