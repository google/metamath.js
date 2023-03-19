include "cfrgr.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "cs3.mm"
include "c2.mm"
include "cwwlksnon.mm"
include "co.mm"
include "wceq.mm"
include "cvtx.mm"
include "cfv.mm"
include "wi.mm"
include "simp3l.mm"
include "eqid.mm"
include "wwlks2onv.mm"
include "sylan.mm"
include "simp3r.mm"
include "cumgr.mm"
include "wb.mm"
include "cusgr.mm"
include "frgrusgr.mm"
include "usgrumgr.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "simpr3.mm"
include "simpl.mm"
include "simpr1.mm"
include "3jca.mm"
include "wwlks2onsym.mm"
include "syl2anr.mm"
include "cv.mm"
include "wreu.mm"
include "3simpb.mm"
include "ad2antlr.mm"
include "simpr2.mm"
include "frgr2wwlkeu.mm"
include "syl3anc.mm"
include "crio.mm"
include "s3eq2.mm"
include "eleq1d.mm"
include "riota2.mm"
include "ad4ant14.mm"
include "simplr2.mm"
include "eqtr2.mm"
include "expcom.mm"
include "syl6bi.mm"
include "com23.mm"
include "sylbid.mm"
include "mpdan.mm"
include "expimpd.mm"
include "ex.mm"
include "3ad2ant2.mm"
include "mpcom.mm"
include "com24.mm"
include "imp.mm"
include "mpd.mm"

theorem frgr2wwlkeqm
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cG: class G
  let cX: class X
  let cY: class Y
  let vx: setvar x


  assert |- ( ( G e. FriendGraph /\ A =/= B /\ ( P e. X /\ Q e. Y ) ) -> ( ( <" A P B "> e. ( A ( 2 WWalksNOn G ) B ) /\ <" B Q A "> e. ( B ( 2 WWalksNOn G ) A ) ) -> Q = P ) )

  proof
    cG
    cfrgr
    wcel
    #
    cA
    cB
    wne
    #
    cP
    cX
    wcel
    #
    cQ
    cY
    wcel
    #
    wa
    #
    w3a
    #
    cA
    cP
    cB
    cs3
    #
    cA
    cB
    c2
    cG
    cwwlksnon
    co
    #
    co
    #
    wcel
    #
    cB
    cQ
    cA
    cs3
    cB
    cA
    @7
    co
    wcel
    #
    cQ
    cP
    wceq
    #
    @5
    @9
    wa
    cA
    cG
    cvtx
    cfv
    #
    wcel
    #
    cP
    @12
    wcel
    #
    cB
    @12
    wcel
    #
    w3a
    #
    @10
    @11
    wi
    #
    @5
    @2
    @9
    @16
    @0
    @1
    @2
    @3
    simp3l
    cA
    cP
    cB
    cX
    cG
    @12
    @12
    eqid
    #
    wwlks2onv
    sylan
    @5
    @9
    @16
    @17
    wi
    @5
    @10
    @16
    @9
    @11
    @5
    @10
    @16
    @9
    @11
    wi
    #
    wi
    #
    @15
    cQ
    @12
    wcel
    #
    @13
    w3a
    #
    @5
    @10
    wa
    #
    @20
    @5
    @3
    @10
    @22
    @0
    @1
    @2
    @3
    simp3r
    cB
    cQ
    cA
    cY
    cG
    @12
    @18
    wwlks2onv
    sylan
    @21
    @15
    @23
    @20
    wi
    @13
    @21
    @16
    @23
    @19
    @21
    @16
    @23
    @19
    wi
    @21
    @16
    wa
    #
    @5
    @10
    @19
    @24
    @5
    wa
    #
    @10
    cA
    cQ
    cB
    cs3
    #
    @8
    wcel
    #
    @19
    @5
    cG
    cumgr
    wcel
    #
    @22
    @10
    @27
    wb
    @24
    @0
    @1
    @28
    @4
    @0
    cG
    cusgr
    wcel
    @28
    cG
    frgrusgr
    cG
    usgrumgr
    syl
    3ad2ant1
    @24
    @15
    @21
    @13
    @21
    @13
    @14
    @15
    simpr3
    @21
    @16
    simpl
    @21
    @13
    @14
    @15
    simpr1
    3jca
    cB
    cQ
    cA
    cG
    @12
    @18
    wwlks2onsym
    syl2anr
    @25
    cA
    vx
    cv
    #
    cB
    cs3
    #
    @8
    wcel
    #
    vx
    @12
    wreu
    #
    @27
    @19
    wi
    @25
    @0
    @13
    @15
    wa
    #
    @1
    @32
    @24
    @0
    @1
    @4
    simpr1
    @16
    @33
    @21
    @5
    @13
    @14
    @15
    3simpb
    ad2antlr
    @24
    @0
    @1
    @4
    simpr2
    cA
    cB
    cG
    @12
    vx
    @18
    frgr2wwlkeu
    syl3anc
    @25
    @32
    wa
    #
    @27
    @31
    vx
    @12
    crio
    #
    cQ
    wceq
    #
    @19
    @21
    @32
    @27
    @36
    wb
    @16
    @5
    @31
    @27
    vx
    @12
    cQ
    @29
    cQ
    wceq
    @30
    @26
    @8
    cA
    @29
    cB
    cQ
    s3eq2
    eleq1d
    riota2
    ad4ant14
    @34
    @9
    @36
    @11
    @34
    @9
    @35
    cP
    wceq
    #
    @36
    @11
    wi
    @25
    @14
    @32
    @9
    @37
    wb
    @13
    @14
    @15
    @21
    @5
    simplr2
    @31
    @9
    vx
    @12
    cP
    @29
    cP
    wceq
    @30
    @6
    @8
    cA
    @29
    cB
    cP
    s3eq2
    eleq1d
    riota2
    sylan
    @36
    @37
    @11
    @35
    cQ
    cP
    eqtr2
    expcom
    syl6bi
    com23
    sylbid
    mpdan
    sylbid
    expimpd
    ex
    com23
    3ad2ant2
    mpcom
    ex
    com24
    imp
    mpd
    expimpd
end
