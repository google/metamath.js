include "con0.mm"
include "wcel.mm"
include "wlim.mm"
include "wa.mm"
include "c0.mm"
include "comu.mm"
include "co.mm"
include "word.mm"
include "wceq.mm"
include "cv.mm"
include "csuc.mm"
include "wrex.mm"
include "wo.mm"
include "wn.mm"
include "limelon.mm"
include "omcl.mm"
include "eloni.mm"
include "syl.mm"
include "sylan2.mm"
include "adantr.mm"
include "0ellim.mm"
include "n0i.mm"
include "anim12ci.mm"
include "adantll.mm"
include "wb.mm"
include "om00.mm"
include "notbid.mm"
include "ioran.mm"
include "syl6bb.mm"
include "mpbird.mm"
include "ciun.mm"
include "vex.mm"
include "sucid.mm"
include "omlim.mm"
include "eqeq1.mm"
include "biimpac.mm"
include "sylan.mm"
include "syl5eleq.mm"
include "eliun.mm"
include "sylib.mm"
include "adantlr.mm"
include "wi.mm"
include "onelon.mm"
include "onnbtwn.mm"
include "imnan.mm"
include "sylibr.mm"
include "com12.mm"
include "adantl.mm"
include "mpd.mm"
include "simpl.mm"
include "jca.mm"
include "anim2i.mm"
include "anassrs.mm"
include "c1o.mm"
include "coa.mm"
include "ordsucelsuc.mm"
include "oa1suc.mm"
include "eleq2d.mm"
include "bitr4d.mm"
include "wss.mm"
include "ordgt0ge1.mm"
include "1on.mm"
include "oaword.mm"
include "mp3an1.mm"
include "syldan.mm"
include "bitrd.mm"
include "biimpa.mm"
include "omsuc.mm"
include "sseqtr4d.mm"
include "sseld.mm"
include "sylbid.mm"
include "eleq1.mm"
include "biimprd.mm"
include "syl9.mm"
include "com23.mm"
include "adantlrl.mm"
include "sucelon.mm"
include "w3a.mm"
include "omord.mm"
include "syl6bir.mm"
include "syl3an2b.mm"
include "3comr.mm"
include "3expb.mm"
include "syl6d.mm"
include "an32s.mm"
include "imp.mm"
include "mtod.mm"
include "exp31.mm"
include "rexlimdv.mm"
include "pm2.01da.mm"
include "nrexdv.mm"
include "sylanbrc.mm"
include "dflim3.mm"

theorem omlimcl
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v


  assert |- ( ( ( A e. On /\ ( B e. C /\ Lim B ) ) /\ (/) e. A ) -> Lim ( A .o B ) )

  proof
    cA
    con0
    wcel
    #
    cB
    cC
    wcel
    #
    cB
    wlim
    #
    wa
    #
    wa
    #
    c0
    cA
    wcel
    #
    wa
    #
    cA
    cB
    comu
    co
    #
    word
    #
    @7
    c0
    wceq
    #
    @7
    vy
    cv
    #
    csuc
    #
    wceq
    #
    vy
    con0
    wrex
    #
    wo
    wn
    #
    @7
    wlim
    @4
    @8
    @5
    @3
    @0
    cB
    con0
    wcel
    #
    @8
    cB
    cC
    limelon
    #
    @0
    @15
    wa
    #
    @7
    con0
    wcel
    @8
    cA
    cB
    omcl
    @7
    eloni
    syl
    sylan2
    adantr
    @6
    @9
    wn
    #
    @13
    wn
    @14
    @6
    @18
    cA
    c0
    wceq
    #
    wn
    #
    cB
    c0
    wceq
    #
    wn
    #
    wa
    #
    @3
    @5
    @23
    @0
    @2
    @5
    @23
    @1
    @2
    @22
    @5
    @20
    @2
    c0
    cB
    wcel
    @22
    cB
    0ellim
    cB
    c0
    n0i
    syl
    cA
    c0
    n0i
    anim12ci
    adantll
    adantll
    @4
    @18
    @23
    wb
    #
    @5
    @3
    @0
    @15
    @24
    @16
    @17
    @18
    @19
    @21
    wo
    #
    wn
    @23
    @17
    @9
    @25
    cA
    cB
    om00
    notbid
    @19
    @21
    ioran
    syl6bb
    sylan2
    adantr
    mpbird
    @6
    @12
    vy
    con0
    @6
    @12
    wn
    #
    @10
    con0
    wcel
    @6
    @12
    @6
    @12
    wa
    @10
    cA
    vx
    cv
    #
    comu
    co
    #
    wcel
    #
    vx
    cB
    wrex
    #
    @26
    @4
    @12
    @30
    @5
    @4
    @12
    wa
    #
    @10
    vx
    cB
    @28
    ciun
    #
    wcel
    @30
    @31
    @10
    @11
    @32
    @10
    vy
    vex
    sucid
    @4
    @7
    @32
    wceq
    #
    @12
    @11
    @32
    wceq
    #
    vx
    cA
    cB
    cC
    omlim
    @12
    @33
    @34
    @7
    @11
    @32
    eqeq1
    biimpac
    sylan
    syl5eleq
    vx
    @10
    cB
    @28
    eliun
    sylib
    adantlr
    @6
    @30
    @26
    wi
    @12
    @6
    @29
    @26
    vx
    cB
    @6
    @27
    cB
    wcel
    #
    @29
    @26
    @6
    @35
    wa
    #
    @29
    wa
    @12
    cB
    @27
    csuc
    #
    wcel
    #
    @36
    @38
    wn
    #
    @29
    @4
    @35
    @39
    @5
    @3
    @35
    @39
    @0
    @3
    @35
    wa
    #
    @27
    con0
    wcel
    #
    @39
    @3
    @15
    @35
    @41
    @16
    cB
    @27
    onelon
    #
    sylan
    @35
    @41
    @39
    wi
    @3
    @41
    @35
    @39
    @41
    @35
    @38
    wa
    wn
    @35
    @39
    wi
    @27
    cB
    onnbtwn
    @35
    @38
    imnan
    sylibr
    com12
    adantl
    mpd
    adantll
    adantlr
    adantr
    @36
    @29
    @12
    @38
    wi
    #
    @4
    @35
    @5
    @29
    @43
    wi
    #
    @4
    @35
    wa
    @0
    @15
    @41
    wa
    #
    wa
    #
    @5
    @44
    @0
    @3
    @35
    @46
    @40
    @45
    @0
    @3
    @15
    @35
    @45
    @16
    @15
    @35
    wa
    @15
    @41
    @15
    @35
    simpl
    @42
    jca
    sylan
    anim2i
    anassrs
    @46
    @5
    wa
    @29
    @12
    @7
    cA
    @37
    comu
    co
    #
    wcel
    #
    @38
    @0
    @41
    @5
    @29
    @12
    @48
    wi
    wi
    @15
    @0
    @41
    wa
    #
    @5
    wa
    #
    @12
    @29
    @48
    @50
    @29
    @11
    @47
    wcel
    #
    @12
    @48
    @50
    @29
    @11
    @28
    c1o
    coa
    co
    #
    wcel
    #
    @51
    @49
    @29
    @53
    wb
    #
    @5
    @49
    @28
    con0
    wcel
    #
    @54
    cA
    @27
    omcl
    #
    @55
    @29
    @11
    @28
    csuc
    #
    wcel
    #
    @53
    @55
    @28
    word
    @29
    @58
    wb
    @28
    eloni
    @10
    @28
    ordsucelsuc
    syl
    @55
    @52
    @57
    @11
    @28
    oa1suc
    eleq2d
    bitr4d
    syl
    adantr
    @50
    @52
    @47
    @11
    @50
    @52
    @28
    cA
    coa
    co
    #
    @47
    @49
    @5
    @52
    @59
    wss
    #
    @49
    @5
    c1o
    cA
    wss
    #
    @60
    @0
    @5
    @61
    wb
    #
    @41
    @0
    cA
    word
    @62
    cA
    eloni
    cA
    ordgt0ge1
    syl
    adantr
    @0
    @41
    @55
    @61
    @60
    wb
    #
    @56
    c1o
    con0
    wcel
    @0
    @55
    @63
    1on
    c1o
    cA
    @28
    oaword
    mp3an1
    syldan
    bitrd
    biimpa
    @49
    @47
    @59
    wceq
    @5
    cA
    @27
    omsuc
    adantr
    sseqtr4d
    sseld
    sylbid
    @12
    @48
    @51
    @7
    @11
    @47
    eleq1
    biimprd
    syl9
    com23
    adantlrl
    @46
    @48
    @38
    wi
    #
    @5
    @0
    @15
    @41
    @64
    @15
    @41
    @0
    @64
    @41
    @15
    @37
    con0
    wcel
    #
    @0
    @64
    @27
    sucelon
    @15
    @65
    @0
    w3a
    @48
    @38
    @5
    wa
    @38
    cB
    @37
    cA
    omord
    @38
    @5
    simpl
    syl6bir
    syl3an2b
    3comr
    3expb
    adantr
    syl6d
    sylan
    an32s
    imp
    mtod
    exp31
    rexlimdv
    adantr
    mpd
    pm2.01da
    adantr
    nrexdv
    @9
    @13
    ioran
    sylanbrc
    vy
    @7
    dflim3
    sylanbrc
end
