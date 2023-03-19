include "cat.mm"
include "wcel.mm"
include "wa.mm"
include "c0h.mm"
include "wne.mm"
include "chj.mm"
include "co.mm"
include "wpss.mm"
include "wss.mm"
include "wn.mm"
include "wi.mm"
include "cv.mm"
include "wrex.mm"
include "hatomici.mm"
include "ccv.mm"
include "wbr.mm"
include "wceq.mm"
include "cin.mm"
include "nssne2.mm"
include "adantrl.mm"
include "atnemeq0.mm"
include "syl5ib.mm"
include "cch.mm"
include "wb.mm"
include "atelch.mm"
include "cvp.mm"
include "chjcom.mm"
include "sylan2.mm"
include "breq2d.mm"
include "bitrd.mm"
include "sylan.mm"
include "sylibd.mm"
include "ancoms.mm"
include "adantlr.mm"
include "imp.mm"
include "w3a.mm"
include "chub1.mm"
include "syl2an.mm"
include "3adant3.mm"
include "adantr.mm"
include "pssss.mm"
include "sstr.mm"
include "adantl.mm"
include "incom.mm"
include "syl5eq.mm"
include "adantrr.mm"
include "atexch.mm"
include "syl3an1.mm"
include "mp2and.mm"
include "simp1.mm"
include "simp3.mm"
include "chjcl.mm"
include "3jca.mm"
include "syl3an.mm"
include "chlub.mm"
include "syl.mm"
include "mpbi2and.mm"
include "3adant2.mm"
include "anim12i.mm"
include "syld3an3.mm"
include "mpbid.mm"
include "syl3anl.mm"
include "eqssd.mm"
include "anassrs.mm"
include "psseq2d.mm"
include "ex.mm"
include "ibd.mm"
include "exp32.mm"
include "3expa.mm"
include "an32s.mm"
include "com34.mm"
include "imp45.mm"
include "simpr.mm"
include "jca.mm"
include "cvnbtwn3.mm"
include "mp3an3.mm"
include "exp4a.mm"
include "com23.mm"
include "imp4a.mm"
include "eleq1d.mm"
include "biimprcd.mm"
include "exp4c.mm"
include "pm2.43b.mm"
include "exp4d.mm"
include "rexlimdva.mm"
include "syl5.mm"
include "imp32.mm"

theorem atcvatlem
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  assume atoml.1: |- A e. CH


  assert |- ( ( ( B e. HAtoms /\ C e. HAtoms ) /\ ( A =/= 0H /\ A C. ( B vH C ) ) ) -> ( -. B C_ A -> A e. HAtoms ) )

  proof
    cB
    cat
    wcel
    #
    cC
    cat
    wcel
    #
    wa
    #
    cA
    c0h
    wne
    #
    cA
    cB
    cC
    chj
    co
    #
    wpss
    #
    cB
    cA
    wss
    wn
    #
    cA
    cat
    wcel
    #
    wi
    #
    @3
    vx
    cv
    #
    cA
    wss
    #
    vx
    cat
    wrex
    @2
    @5
    @8
    wi
    #
    vx
    cA
    atoml.1
    hatomici
    @2
    @10
    @11
    vx
    cat
    @2
    @9
    cat
    wcel
    #
    wa
    #
    @10
    @5
    @6
    @7
    @2
    @12
    @10
    @5
    @6
    wa
    #
    wa
    #
    @7
    wi
    #
    @2
    @12
    @16
    @12
    @2
    @12
    @15
    @7
    @13
    @15
    wa
    #
    @7
    @12
    @17
    cA
    @9
    cat
    @17
    @9
    cB
    @9
    chj
    co
    #
    ccv
    wbr
    #
    cA
    @18
    wpss
    #
    cA
    @9
    wceq
    #
    @13
    @15
    @19
    @0
    @12
    @15
    @19
    wi
    #
    @1
    @12
    @0
    @22
    @12
    @0
    wa
    #
    @15
    @9
    cB
    cin
    #
    c0h
    wceq
    #
    @19
    @15
    @9
    cB
    wne
    #
    @23
    @25
    @10
    @6
    @26
    @5
    @9
    cB
    cA
    nssne2
    #
    adantrl
    @9
    cB
    atnemeq0
    #
    syl5ib
    @12
    @9
    cch
    wcel
    #
    @0
    @25
    @19
    wb
    @9
    atelch
    #
    @29
    @0
    wa
    #
    @25
    @9
    @9
    cB
    chj
    co
    #
    ccv
    wbr
    @19
    @9
    cB
    cvp
    @31
    @32
    @18
    @9
    ccv
    @0
    @29
    cB
    cch
    wcel
    #
    @32
    @18
    wceq
    cB
    atelch
    #
    @9
    cB
    chjcom
    sylan2
    breq2d
    bitrd
    sylan
    sylibd
    ancoms
    adantlr
    imp
    @13
    @10
    @5
    @6
    @20
    @13
    @10
    @6
    @5
    @20
    @0
    @12
    @1
    @10
    @6
    @5
    @20
    wi
    #
    wi
    wi
    #
    @0
    @12
    @1
    @36
    @0
    @12
    @1
    w3a
    #
    @10
    @6
    @35
    @37
    @10
    @6
    wa
    #
    wa
    #
    @5
    @20
    @39
    @5
    @5
    @20
    wb
    @39
    @5
    wa
    @4
    @18
    cA
    @37
    @38
    @5
    @4
    @18
    wceq
    @37
    @38
    @5
    wa
    #
    wa
    #
    @4
    @18
    @41
    cB
    @18
    wss
    #
    cC
    @18
    wss
    #
    @4
    @18
    wss
    #
    @37
    @42
    @40
    @0
    @12
    @42
    @1
    @0
    @33
    @29
    @42
    @12
    @34
    @30
    cB
    @9
    chub1
    syl2an
    3adant3
    adantr
    @41
    @9
    @4
    wss
    #
    cB
    @9
    cin
    #
    c0h
    wceq
    #
    @43
    @40
    @45
    @37
    @10
    @5
    @45
    @6
    @5
    @10
    cA
    @4
    wss
    @45
    cA
    @4
    pssss
    @9
    cA
    @4
    sstr
    sylan2
    adantlr
    #
    adantl
    @37
    @38
    @47
    @5
    @39
    @46
    @24
    c0h
    cB
    @9
    incom
    @37
    @38
    @25
    @0
    @12
    @38
    @25
    wi
    #
    @1
    @12
    @0
    @49
    @38
    @26
    @23
    @25
    @27
    @28
    syl5ib
    ancoms
    3adant3
    imp
    syl5eq
    adantrr
    @37
    @45
    @47
    wa
    @43
    wi
    #
    @40
    @0
    @33
    @12
    @1
    @50
    @34
    cB
    @9
    cC
    atexch
    syl3an1
    adantr
    mp2and
    @37
    @42
    @43
    wa
    @44
    wb
    #
    @40
    @37
    @33
    cC
    cch
    wcel
    #
    @18
    cch
    wcel
    #
    w3a
    #
    @51
    @0
    @33
    @12
    @29
    @1
    @52
    @54
    @34
    @30
    cC
    atelch
    #
    @33
    @29
    @52
    w3a
    #
    @33
    @52
    @53
    @33
    @29
    @52
    simp1
    @33
    @29
    @52
    simp3
    @33
    @29
    @53
    @52
    cB
    @9
    chjcl
    #
    3adant3
    3jca
    syl3an
    cB
    cC
    @18
    chlub
    syl
    adantr
    mpbi2and
    @0
    @33
    @12
    @29
    @1
    @52
    @40
    @18
    @4
    wss
    #
    @34
    @30
    @55
    @56
    @40
    wa
    cB
    @4
    wss
    #
    @45
    wa
    #
    @58
    @56
    @59
    @40
    @45
    @33
    @52
    @59
    @29
    cB
    cC
    chub1
    3adant2
    @48
    anim12i
    @56
    @60
    @58
    wb
    #
    @40
    @33
    @29
    @52
    @4
    cch
    wcel
    #
    @61
    @33
    @52
    @62
    @29
    cB
    cC
    chjcl
    3adant2
    cB
    @9
    @4
    chlub
    syld3an3
    adantr
    mpbid
    syl3anl
    eqssd
    anassrs
    psseq2d
    ex
    ibd
    exp32
    3expa
    an32s
    com34
    imp45
    @13
    @10
    @19
    @20
    wa
    @21
    wi
    #
    @14
    @13
    @10
    @63
    @0
    @12
    @10
    @63
    wi
    #
    @1
    @0
    @12
    wa
    @29
    @53
    wa
    #
    @64
    @0
    @33
    @29
    @65
    @12
    @34
    @30
    @33
    @29
    wa
    @29
    @53
    @33
    @29
    simpr
    @57
    jca
    syl2an
    @65
    @10
    @19
    @20
    @21
    @65
    @19
    @10
    @20
    @21
    wi
    @65
    @19
    @10
    @20
    @21
    @29
    @53
    cA
    cch
    wcel
    @19
    @10
    @20
    wa
    @21
    wi
    wi
    atoml.1
    @9
    @18
    cA
    cvnbtwn3
    mp3an3
    exp4a
    com23
    imp4a
    syl
    adantlr
    imp
    adantrr
    mp2and
    eleq1d
    biimprcd
    exp4c
    pm2.43b
    imp
    exp4d
    rexlimdva
    syl5
    imp32
end
