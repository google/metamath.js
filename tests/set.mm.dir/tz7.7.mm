include "word.mm"
include "wtr.mm"
include "wa.mm"
include "wcel.mm"
include "wss.mm"
include "wne.mm"
include "wi.mm"
include "cep.mm"
include "wfr.mm"
include "ordtr.mm"
include "ordfr.mm"
include "tz7.2.mm"
include "3exp.mm"
include "sylc.mm"
include "adantr.mm"
include "cdif.mm"
include "c0.mm"
include "pssdifn0.mm"
include "cv.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "difss.mm"
include "tz7.5.mm"
include "mp3an2.mm"
include "eldifi.mm"
include "trss.mm"
include "difin0ss.mm"
include "com12.mm"
include "syl56.mm"
include "syl.mm"
include "ad2antrr.mm"
include "imp32.mm"
include "wn.mm"
include "eleq1.mm"
include "biimpcd.mm"
include "eldifn.mm"
include "nsyli.mm"
include "imp.mm"
include "adantll.mm"
include "adantl.mm"
include "trel.mm"
include "expcomd.mm"
include "ex.mm"
include "adantld.mm"
include "w3o.mm"
include "wwe.mm"
include "ordwe.mm"
include "ssel2.mm"
include "anim12i.mm"
include "wecmpep.mm"
include "syl2an.mm"
include "adantlr.mm"
include "ecase23d.mm"
include "exp44.mm"
include "com34.mm"
include "imp31.mm"
include "ssrdv.mm"
include "adantrr.mm"
include "eqssd.mm"
include "ad2antrl.mm"
include "eqeltrrd.mm"
include "rexlimdvaa.mm"
include "syl5.mm"
include "exp4b.mm"
include "com23.mm"
include "adantrd.mm"
include "pm2.43i.mm"
include "syl7.mm"
include "exp4a.mm"
include "pm2.43d.mm"
include "impd.mm"
include "impbid.mm"

theorem tz7.7
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( Ord A /\ Tr B ) -> ( B e. A <-> ( B C_ A /\ B =/= A ) ) )

  proof
    cA
    word
    #
    cB
    wtr
    #
    wa
    #
    cB
    cA
    wcel
    #
    cB
    cA
    wss
    #
    cB
    cA
    wne
    #
    wa
    #
    @0
    @3
    @6
    wi
    #
    @1
    @0
    cA
    wtr
    #
    cA
    cep
    wfr
    #
    @7
    cA
    ordtr
    #
    cA
    ordfr
    @8
    @9
    @3
    @6
    cA
    cB
    tz7.2
    3exp
    sylc
    adantr
    @2
    @4
    @5
    @3
    @2
    @4
    @5
    @3
    wi
    @2
    @4
    @4
    @5
    @3
    @6
    cA
    cB
    cdif
    #
    c0
    wne
    #
    @2
    @4
    @3
    cB
    cA
    pssdifn0
    @2
    @4
    @12
    @3
    wi
    #
    wi
    #
    @2
    @0
    @14
    @1
    @2
    @4
    @0
    @13
    @2
    @4
    @0
    @12
    @3
    @0
    @12
    wa
    @11
    vx
    cv
    #
    cin
    c0
    wceq
    #
    vx
    @11
    wrex
    #
    @2
    @4
    wa
    #
    @3
    @0
    @11
    cA
    wss
    @12
    @17
    cA
    cB
    difss
    vx
    cA
    @11
    tz7.5
    mp3an2
    @18
    @16
    @3
    vx
    @11
    @18
    @15
    @11
    wcel
    #
    @16
    wa
    wa
    #
    @15
    cB
    cA
    @20
    @15
    cB
    @18
    @19
    @16
    @15
    cB
    wss
    #
    @0
    @19
    @16
    @21
    wi
    #
    wi
    #
    @1
    @4
    @0
    @8
    @23
    @10
    @19
    @15
    cA
    wcel
    #
    @8
    @15
    cA
    wss
    #
    @22
    @15
    cA
    cB
    eldifi
    #
    cA
    @15
    trss
    @16
    @25
    @21
    cA
    cB
    @15
    difin0ss
    com12
    syl56
    syl
    ad2antrr
    imp32
    @18
    @19
    cB
    @15
    wss
    @16
    @18
    @19
    wa
    vy
    cB
    @15
    @2
    @4
    @19
    vy
    cv
    #
    cB
    wcel
    #
    @27
    @15
    wcel
    #
    wi
    @2
    @4
    @28
    @19
    @29
    @2
    @4
    @28
    @19
    @29
    @2
    @4
    @28
    wa
    #
    @19
    wa
    #
    wa
    @29
    @27
    @15
    wceq
    #
    @15
    @27
    wcel
    #
    @31
    @32
    wn
    #
    @2
    @28
    @19
    @34
    @4
    @28
    @19
    @34
    @28
    @32
    @15
    cB
    wcel
    #
    @19
    @32
    @28
    @35
    @27
    @15
    cB
    eleq1
    biimpcd
    @15
    cA
    cB
    eldifn
    #
    nsyli
    imp
    adantll
    adantl
    @1
    @31
    @33
    wn
    #
    @0
    @1
    @30
    @19
    @37
    @1
    @28
    @19
    @37
    wi
    #
    @4
    @1
    @28
    @38
    @1
    @28
    wa
    @33
    @35
    @19
    @1
    @28
    @33
    @35
    wi
    @1
    @33
    @28
    @35
    cB
    @15
    @27
    trel
    expcomd
    imp
    @36
    nsyli
    ex
    adantld
    imp32
    adantll
    @0
    @31
    @29
    @32
    @33
    w3o
    #
    @1
    @0
    cA
    cep
    wwe
    @27
    cA
    wcel
    #
    @24
    wa
    @39
    @31
    cA
    ordwe
    @30
    @40
    @19
    @24
    cB
    cA
    @27
    ssel2
    @26
    anim12i
    vy
    vx
    cA
    wecmpep
    syl2an
    adantlr
    ecase23d
    exp44
    com34
    imp31
    ssrdv
    adantrr
    eqssd
    @19
    @24
    @18
    @16
    @26
    ad2antrl
    eqeltrrd
    rexlimdvaa
    syl5
    exp4b
    com23
    adantrd
    pm2.43i
    syl7
    exp4a
    pm2.43d
    impd
    impbid
end
