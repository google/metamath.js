include "cat.mm"
include "wcel.mm"
include "chj.mm"
include "co.mm"
include "cort.mm"
include "cfv.mm"
include "cin.mm"
include "c0h.mm"
include "wceq.mm"
include "wo.mm"
include "csn.mm"
include "cun.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "wss.mm"
include "wrex.mm"
include "cch.mm"
include "atelch.mm"
include "chjcl.mm"
include "sylancr.mm"
include "choccli.mm"
include "chincl.mm"
include "sylancl.mm"
include "hatomic.mm"
include "sylan.mm"
include "wi.mm"
include "wb.mm"
include "inss2.mm"
include "sstr.mm"
include "mpan2.mm"
include "pjococi.mm"
include "oveq1i.mm"
include "ineq1i.mm"
include "incom.mm"
include "eqtr3i.mm"
include "pjoml3.mm"
include "mpan.mm"
include "imp.mm"
include "syl5eq.mm"
include "syl2an.mm"
include "ad2ant2lr.mm"
include "inss1.mm"
include "chub1.mm"
include "adantr.mm"
include "chlub.mm"
include "mp3an1.mm"
include "sylan2.mm"
include "biimpd.mm"
include "ancoms.mm"
include "mpand.mm"
include "adantrr.mm"
include "anim12i.mm"
include "ad2antlr.mm"
include "pm3.22.mm"
include "adantl.mm"
include "csh.mm"
include "chsh.mm"
include "chshii.mm"
include "orthin.mm"
include "jca.mm"
include "atexch.mm"
include "sylc.mm"
include "expd.mm"
include "syl3c.mm"
include "eqssd.mm"
include "ineq1d.mm"
include "eqtr3d.mm"
include "eleq1d.mm"
include "exp43.mm"
include "com24.mm"
include "imp31.mm"
include "ibd.mm"
include "ex.mm"
include "com23.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "necon1bd.mm"
include "orrd.mm"
include "elun.mm"
include "fvex.mm"
include "inex2.mm"
include "elsn.mm"
include "orbi2i.mm"
include "bitri.mm"
include "sylibr.mm"

theorem atomli
  let cA: class A
  let cB: class B
  let vx: setvar x
  let cC: class C
  assume atoml.1: |- A e. CH


  assert |- ( B e. HAtoms -> ( ( A vH B ) i^i ( _|_ ` A ) ) e. ( HAtoms u. { 0H } ) )

  proof
    cB
    cat
    wcel
    #
    cA
    cB
    chj
    co
    #
    cA
    cort
    cfv
    #
    cin
    #
    cat
    wcel
    #
    @3
    c0h
    wceq
    #
    wo
    #
    @3
    cat
    c0h
    csn
    #
    cun
    wcel
    #
    @0
    @4
    @5
    @0
    @4
    @3
    c0h
    @0
    @3
    c0h
    wne
    #
    @4
    @0
    @9
    wa
    #
    vx
    cv
    #
    @3
    wss
    #
    vx
    cat
    wrex
    #
    @4
    @0
    @3
    cch
    wcel
    #
    @9
    @13
    @0
    @1
    cch
    wcel
    #
    @2
    cch
    wcel
    #
    @14
    @0
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    @15
    atoml.1
    cB
    atelch
    #
    cA
    cB
    chjcl
    #
    sylancr
    cA
    atoml.1
    choccli
    #
    @1
    @2
    chincl
    sylancl
    vx
    @3
    hatomic
    sylan
    @10
    @12
    @4
    vx
    cat
    @10
    @12
    @11
    cat
    wcel
    #
    @4
    @10
    @12
    @22
    @4
    wi
    @10
    @12
    wa
    @22
    @4
    @0
    @9
    @12
    @22
    @22
    @4
    wb
    #
    wi
    @0
    @22
    @12
    @9
    @23
    @0
    @22
    @12
    @9
    @23
    @0
    @22
    wa
    #
    @12
    @9
    wa
    #
    wa
    #
    @11
    @3
    cat
    @26
    cA
    @11
    chj
    co
    #
    @2
    cin
    #
    @11
    @3
    @22
    @12
    @28
    @11
    wceq
    #
    @0
    @9
    @22
    @11
    cch
    wcel
    #
    @11
    @2
    wss
    #
    @29
    @12
    @11
    atelch
    #
    @12
    @3
    @2
    wss
    @31
    @1
    @2
    inss2
    @11
    @3
    @2
    sstr
    mpan2
    #
    @30
    @31
    wa
    #
    @28
    @2
    @2
    cort
    cfv
    #
    @11
    chj
    co
    #
    cin
    #
    @11
    @36
    @2
    cin
    @28
    @37
    @36
    @27
    @2
    @35
    cA
    @11
    chj
    cA
    atoml.1
    pjococi
    oveq1i
    ineq1i
    @36
    @2
    incom
    eqtr3i
    @30
    @31
    @37
    @11
    wceq
    #
    @16
    @30
    @31
    @38
    wi
    @21
    @2
    @11
    pjoml3
    mpan
    imp
    syl5eq
    syl2an
    ad2ant2lr
    @26
    @27
    @1
    @2
    @26
    @27
    @1
    @24
    @12
    @27
    @1
    wss
    #
    @9
    @12
    @24
    @11
    @1
    wss
    #
    @39
    @12
    @3
    @1
    wss
    @40
    @1
    @2
    inss1
    @11
    @3
    @1
    sstr
    mpan2
    #
    @24
    @40
    @39
    @0
    @18
    @30
    @40
    @39
    wi
    @22
    @19
    @32
    @18
    @30
    wa
    cA
    @1
    wss
    #
    @40
    @39
    @18
    @42
    @30
    @17
    @18
    @42
    atoml.1
    cA
    cB
    chub1
    mpan
    adantr
    @30
    @18
    @42
    @40
    wa
    #
    @39
    wi
    @30
    @18
    wa
    @43
    @39
    @18
    @30
    @15
    @43
    @39
    wb
    #
    @17
    @18
    @15
    atoml.1
    @20
    mpan
    @17
    @30
    @15
    @44
    atoml.1
    cA
    @11
    @1
    chlub
    mp3an1
    sylan2
    biimpd
    ancoms
    mpand
    syl2an
    imp
    sylan2
    adantrr
    @26
    @18
    @27
    cch
    wcel
    #
    wa
    #
    cA
    @27
    wss
    #
    cB
    @27
    wss
    #
    @1
    @27
    wss
    #
    @24
    @46
    @25
    @0
    @18
    @22
    @45
    @19
    @22
    @17
    @30
    @45
    atoml.1
    @32
    cA
    @11
    chjcl
    sylancr
    anim12i
    adantr
    @22
    @47
    @0
    @25
    @22
    @17
    @30
    @47
    atoml.1
    @32
    cA
    @11
    chub1
    sylancr
    ad2antlr
    @26
    @22
    @0
    wa
    #
    @40
    cA
    @11
    cin
    #
    c0h
    wceq
    #
    wa
    #
    @48
    @24
    @50
    @25
    @0
    @22
    pm3.22
    adantr
    @22
    @12
    @53
    @0
    @9
    @22
    @12
    wa
    @40
    @52
    @12
    @40
    @22
    @41
    adantl
    @22
    @30
    @31
    @52
    @12
    @32
    @33
    @34
    @51
    @11
    cA
    cin
    #
    c0h
    cA
    @11
    incom
    @30
    @31
    @54
    c0h
    wceq
    #
    @30
    @11
    csh
    wcel
    cA
    csh
    wcel
    @31
    @55
    wi
    @11
    chsh
    cA
    atoml.1
    chshii
    @11
    cA
    orthin
    sylancl
    imp
    syl5eq
    syl2an
    jca
    ad2ant2lr
    @17
    @22
    @0
    @53
    @48
    wi
    atoml.1
    cA
    @11
    cB
    atexch
    mp3an1
    sylc
    @46
    @47
    @48
    @49
    @46
    @47
    @48
    wa
    #
    @49
    @17
    @18
    @45
    @56
    @49
    wb
    atoml.1
    cA
    cB
    @27
    chlub
    mp3an1
    biimpd
    expd
    syl3c
    eqssd
    ineq1d
    eqtr3d
    eleq1d
    exp43
    com24
    imp31
    ibd
    ex
    com23
    rexlimdv
    mpd
    ex
    necon1bd
    orrd
    @8
    @4
    @3
    @7
    wcel
    #
    wo
    @6
    @3
    cat
    @7
    elun
    @57
    @5
    @4
    @3
    c0h
    @2
    @1
    cA
    cort
    fvex
    inex2
    elsn
    orbi2i
    bitri
    sylibr
end
