include "cvv.mm"
include "wcel.mm"
include "wfun.mm"
include "wss.mm"
include "w3a.mm"
include "csupp.mm"
include "co.mm"
include "wi.mm"
include "wa.mm"
include "cdm.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "funss.mm"
include "impcom.mm"
include "funfn.mm"
include "biimpi.mm"
include "syl.mm"
include "adantr.mm"
include "jca.mm"
include "3adant3.mm"
include "dmss.mm"
include "3ad2ant2.mm"
include "dmexg.mm"
include "3ad2ant3.mm"
include "simpr.mm"
include "3jca.mm"
include "funssfv.mm"
include "3expa.mm"
include "eqeq1.mm"
include "biimpd.mm"
include "ralrimiva.mm"
include "suppfnss.mm"
include "sylc.mm"
include "expcom.mm"
include "wn.mm"
include "c0.mm"
include "ssid.mm"
include "con3i.mm"
include "supp0prc.mm"
include "sseq12d.mm"
include "mpbiri.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem funsssuppss
  let cF: class F
  let cG: class G
  let cV: class V
  let cZ: class Z
  let vx: setvar x


  assert |- ( ( Fun G /\ F C_ G /\ G e. V ) -> ( F supp Z ) C_ ( G supp Z ) )

  proof
    cZ
    cvv
    wcel
    #
    cG
    wfun
    #
    cF
    cG
    wss
    #
    cG
    cV
    wcel
    #
    w3a
    #
    cF
    cZ
    csupp
    co
    #
    cG
    cZ
    csupp
    co
    #
    wss
    #
    wi
    @4
    @0
    @7
    @4
    @0
    wa
    #
    cF
    cF
    cdm
    #
    wfn
    #
    cG
    cG
    cdm
    #
    wfn
    #
    wa
    #
    @9
    @11
    wss
    #
    @11
    cvv
    wcel
    #
    @0
    w3a
    #
    wa
    vx
    cv
    #
    cG
    cfv
    #
    cZ
    wceq
    #
    @17
    cF
    cfv
    #
    cZ
    wceq
    #
    wi
    #
    vx
    @9
    wral
    #
    @7
    @8
    @13
    @16
    @4
    @13
    @0
    @1
    @2
    @13
    @3
    @1
    @2
    wa
    #
    @10
    @12
    @24
    cF
    wfun
    #
    @10
    @2
    @1
    @25
    cF
    cG
    funss
    impcom
    @25
    @10
    cF
    funfn
    biimpi
    syl
    @1
    @12
    @2
    @1
    @12
    cG
    funfn
    biimpi
    adantr
    jca
    3adant3
    adantr
    @8
    @14
    @15
    @0
    @4
    @14
    @0
    @2
    @1
    @14
    @3
    cF
    cG
    dmss
    3ad2ant2
    adantr
    @4
    @15
    @0
    @3
    @1
    @15
    @2
    cG
    cV
    dmexg
    3ad2ant3
    adantr
    @4
    @0
    simpr
    3jca
    jca
    @4
    @23
    @0
    @1
    @2
    @23
    @3
    @24
    @22
    vx
    @9
    @24
    @17
    @9
    wcel
    #
    wa
    @18
    @20
    wceq
    #
    @22
    @1
    @2
    @26
    @27
    @17
    cG
    cF
    funssfv
    3expa
    @27
    @19
    @21
    @18
    @20
    cZ
    eqeq1
    biimpd
    syl
    ralrimiva
    3adant3
    adantr
    vx
    @9
    @11
    cF
    cG
    cvv
    cvv
    cZ
    suppfnss
    sylc
    expcom
    @0
    wn
    #
    @7
    @4
    @28
    @7
    c0
    c0
    wss
    c0
    ssid
    @28
    @5
    c0
    @6
    c0
    @28
    cF
    cvv
    wcel
    #
    @0
    wa
    #
    wn
    @5
    c0
    wceq
    @30
    @0
    @29
    @0
    simpr
    con3i
    cF
    cZ
    supp0prc
    syl
    @28
    cG
    cvv
    wcel
    #
    @0
    wa
    #
    wn
    @6
    c0
    wceq
    @32
    @0
    @31
    @0
    simpr
    con3i
    cG
    cZ
    supp0prc
    syl
    sseq12d
    mpbiri
    a1d
    pm2.61i
end
