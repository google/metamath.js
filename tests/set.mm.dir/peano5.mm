include "c0.mm"
include "wcel.mm"
include "cv.mm"
include "csuc.mm"
include "wi.mm"
include "com.mm"
include "wral.mm"
include "wa.mm"
include "cdif.mm"
include "wceq.mm"
include "wss.mm"
include "cin.mm"
include "wrex.mm"
include "wn.mm"
include "eldifn.mm"
include "adantl.mm"
include "wne.mm"
include "eldifi.mm"
include "elndif.mm"
include "eleq1.mm"
include "biimpcd.mm"
include "necon3bd.mm"
include "mpan9.mm"
include "nnsuc.mm"
include "syl2anc.mm"
include "adantlr.mm"
include "adantr.mm"
include "nfra1.mm"
include "nfv.mm"
include "nfan.mm"
include "rsp.mm"
include "vex.mm"
include "sucid.mm"
include "eleq2.mm"
include "mpbiri.mm"
include "peano2b.mm"
include "syl6bbr.mm"
include "minel.mm"
include "neldif.mm"
include "sylan2.mm"
include "exp32.mm"
include "syl6bi.mm"
include "mpid.mm"
include "syl5.mm"
include "impd.mm"
include "eleq1a.mm"
include "com12.mm"
include "imim12d.mm"
include "com13.mm"
include "sylan9.mm"
include "rexlimd.mm"
include "a1i.mm"
include "imp41.mm"
include "mpd.mm"
include "mtand.mm"
include "nrexdv.mm"
include "word.mm"
include "ordom.mm"
include "difss.mm"
include "tz7.5.mm"
include "mp3an12.mm"
include "necon1bi.mm"
include "syl.mm"
include "ssdif0.mm"
include "sylibr.mm"

theorem peano5
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( ( (/) e. A /\ A. x e. _om ( x e. A -> suc x e. A ) ) -> _om C_ A )

  proof
    c0
    cA
    wcel
    #
    vx
    cv
    #
    cA
    wcel
    #
    @1
    csuc
    #
    cA
    wcel
    #
    wi
    #
    vx
    com
    wral
    #
    wa
    #
    com
    cA
    cdif
    #
    c0
    wceq
    #
    com
    cA
    wss
    @7
    @8
    vy
    cv
    #
    cin
    c0
    wceq
    #
    vy
    @8
    wrex
    #
    wn
    @9
    @7
    @11
    vy
    @8
    @7
    @10
    @8
    wcel
    #
    wa
    #
    @11
    @10
    cA
    wcel
    #
    @13
    @15
    wn
    @7
    @10
    com
    cA
    eldifn
    adantl
    @14
    @11
    wa
    @10
    @3
    wceq
    #
    vx
    com
    wrex
    #
    @15
    @14
    @17
    @11
    @0
    @13
    @17
    @6
    @0
    @13
    wa
    @10
    com
    wcel
    #
    @10
    c0
    wne
    #
    @17
    @13
    @18
    @0
    @10
    com
    cA
    eldifi
    #
    adantl
    @0
    c0
    @8
    wcel
    #
    wn
    @13
    @19
    c0
    cA
    com
    elndif
    @13
    @21
    @10
    c0
    @10
    c0
    wceq
    @13
    @21
    @10
    c0
    @8
    eleq1
    biimpcd
    necon3bd
    mpan9
    vx
    @10
    nnsuc
    syl2anc
    adantlr
    adantr
    @0
    @6
    @13
    @11
    @17
    @15
    wi
    #
    @6
    @13
    @11
    @22
    wi
    wi
    wi
    @0
    @6
    @13
    @11
    @22
    @6
    @13
    @11
    wa
    #
    wa
    @16
    @15
    vx
    com
    @6
    @23
    vx
    @5
    vx
    com
    nfra1
    @23
    vx
    nfv
    nfan
    @15
    vx
    nfv
    @6
    @1
    com
    wcel
    #
    @5
    @23
    @16
    @15
    wi
    @5
    vx
    com
    rsp
    @16
    @5
    @23
    @15
    @16
    @23
    @2
    @4
    @15
    @16
    @13
    @11
    @2
    @13
    @18
    @16
    @11
    @2
    wi
    #
    @20
    @16
    @18
    @1
    @10
    wcel
    #
    @25
    @16
    @26
    @1
    @3
    wcel
    @1
    vx
    vex
    sucid
    @10
    @3
    @1
    eleq2
    mpbiri
    @16
    @18
    @24
    @26
    @25
    wi
    @16
    @18
    @3
    com
    wcel
    @24
    @10
    @3
    com
    eleq1
    @1
    peano2b
    syl6bbr
    @24
    @26
    @11
    @2
    @26
    @11
    wa
    @24
    @1
    @8
    wcel
    wn
    @2
    @1
    @10
    @8
    minel
    @1
    com
    cA
    neldif
    sylan2
    exp32
    syl6bi
    mpid
    syl5
    impd
    @4
    @16
    @15
    @3
    cA
    @10
    eleq1a
    com12
    imim12d
    com13
    sylan9
    rexlimd
    exp32
    a1i
    imp41
    mpd
    mtand
    nrexdv
    @12
    @8
    c0
    com
    word
    @8
    com
    wss
    @8
    c0
    wne
    @12
    ordom
    com
    cA
    difss
    vy
    com
    @8
    tz7.5
    mp3an12
    necon1bi
    syl
    com
    cA
    ssdif0
    sylibr
end
