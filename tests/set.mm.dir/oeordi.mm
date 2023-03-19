include "con0.mm"
include "wcel.mm"
include "c2o.mm"
include "cdif.mm"
include "coe.mm"
include "co.mm"
include "cv.mm"
include "wi.mm"
include "csuc.mm"
include "wceq.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "imbi2d.mm"
include "wa.mm"
include "comu.mm"
include "c1o.mm"
include "eldifi.mm"
include "oecl.mm"
include "sylan.mm"
include "om1.mm"
include "syl.mm"
include "ondif2.mm"
include "simprbi.mm"
include "adantr.mm"
include "c0.mm"
include "simpr.mm"
include "dif20el.mm"
include "oen0.mm"
include "syl21anc.mm"
include "omordi.mm"
include "mpd.mm"
include "eqeltrrd.mm"
include "oesuc.mm"
include "eleqtrrd.mm"
include "expcom.mm"
include "suceloni.mm"
include "syl2an.mm"
include "ontr1.mm"
include "mpan2d.mm"
include "a2d.mm"
include "wral.mm"
include "wlim.mm"
include "bi2.04.mm"
include "ralbii.mm"
include "r19.21v.mm"
include "bitri.mm"
include "ciun.mm"
include "limsuc.mm"
include "biimpa.mm"
include "cvv.mm"
include "elex.mm"
include "sucexb.mm"
include "sucidg.mm"
include "sylbir.mm"
include "eleq2.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "mpid.mm"
include "anc2li.mm"
include "eliuni.mm"
include "syl6.mm"
include "adantl.mm"
include "simpl.mm"
include "vex.mm"
include "oelim.mm"
include "mpanlr1.mm"
include "adantlr.mm"
include "sylibrd.mm"
include "ex.mm"
include "syl5bi.mm"
include "tfindsg2.mm"
include "impancom.mm"

theorem oeordi
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( B e. On /\ C e. ( On \ 2o ) ) -> ( A e. B -> ( C ^o A ) e. ( C ^o B ) ) )

  proof
    cB
    con0
    wcel
    cA
    cB
    wcel
    cC
    con0
    c2o
    cdif
    wcel
    #
    cC
    cA
    coe
    co
    #
    cC
    cB
    coe
    co
    #
    wcel
    #
    @0
    @1
    cC
    vx
    cv
    #
    coe
    co
    #
    wcel
    #
    wi
    #
    @0
    @1
    cC
    cA
    csuc
    #
    coe
    co
    #
    wcel
    #
    wi
    @0
    @1
    cC
    vy
    cv
    #
    coe
    co
    #
    wcel
    #
    wi
    #
    @0
    @1
    cC
    @11
    csuc
    #
    coe
    co
    #
    wcel
    #
    wi
    @0
    @3
    wi
    vx
    vy
    cB
    cA
    @4
    @8
    wceq
    #
    @6
    @10
    @0
    @18
    @5
    @9
    @1
    @4
    @8
    cC
    coe
    oveq2
    eleq2d
    imbi2d
    @4
    @11
    wceq
    #
    @6
    @13
    @0
    @19
    @5
    @12
    @1
    @4
    @11
    cC
    coe
    oveq2
    eleq2d
    imbi2d
    @4
    @15
    wceq
    #
    @6
    @17
    @0
    @20
    @5
    @16
    @1
    @4
    @15
    cC
    coe
    oveq2
    eleq2d
    imbi2d
    @4
    cB
    wceq
    #
    @6
    @3
    @0
    @21
    @5
    @2
    @1
    @4
    cB
    cC
    coe
    oveq2
    eleq2d
    imbi2d
    @0
    cA
    con0
    wcel
    #
    @10
    @0
    @22
    wa
    #
    @1
    @1
    cC
    comu
    co
    #
    @9
    @23
    @1
    c1o
    comu
    co
    #
    @1
    @24
    @23
    @1
    con0
    wcel
    #
    @25
    @1
    wceq
    @0
    cC
    con0
    wcel
    #
    @22
    @26
    cC
    con0
    c2o
    eldifi
    #
    cC
    cA
    oecl
    sylan
    #
    @1
    om1
    syl
    @23
    c1o
    cC
    wcel
    #
    @25
    @24
    wcel
    #
    @0
    @30
    @22
    @0
    @27
    @30
    cC
    ondif2
    simprbi
    #
    adantr
    @23
    @27
    @26
    c0
    @1
    wcel
    #
    @30
    @31
    wi
    @0
    @27
    @22
    @28
    adantr
    #
    @29
    @23
    @27
    @22
    c0
    cC
    wcel
    #
    @33
    @34
    @0
    @22
    simpr
    @0
    @35
    @22
    cC
    dif20el
    #
    adantr
    cC
    cA
    oen0
    syl21anc
    c1o
    cC
    @1
    omordi
    syl21anc
    mpd
    eqeltrrd
    @0
    @27
    @22
    @9
    @24
    wceq
    @28
    cC
    cA
    oesuc
    sylan
    eleqtrrd
    expcom
    @11
    con0
    wcel
    #
    cA
    @11
    wcel
    #
    wa
    @0
    @13
    @17
    @37
    @0
    @13
    @17
    wi
    #
    wi
    @38
    @0
    @37
    @39
    @0
    @37
    wa
    #
    @13
    @12
    @16
    wcel
    #
    @17
    @40
    @12
    @12
    cC
    comu
    co
    #
    @16
    @40
    @12
    c1o
    comu
    co
    #
    @12
    @42
    @40
    @12
    con0
    wcel
    #
    @43
    @12
    wceq
    @0
    @27
    @37
    @44
    @28
    cC
    @11
    oecl
    sylan
    #
    @12
    om1
    syl
    @40
    @30
    @43
    @42
    wcel
    #
    @0
    @30
    @37
    @32
    adantr
    @40
    @27
    @44
    c0
    @12
    wcel
    #
    @30
    @46
    wi
    @0
    @27
    @37
    @28
    adantr
    #
    @45
    @40
    @27
    @37
    @35
    @47
    @48
    @0
    @37
    simpr
    @0
    @35
    @37
    @36
    adantr
    cC
    @11
    oen0
    syl21anc
    c1o
    cC
    @12
    omordi
    syl21anc
    mpd
    eqeltrrd
    @0
    @27
    @37
    @16
    @42
    wceq
    @28
    cC
    @11
    oesuc
    sylan
    eleqtrrd
    @40
    @16
    con0
    wcel
    #
    @13
    @41
    wa
    @17
    wi
    @0
    @27
    @15
    con0
    wcel
    @49
    @37
    @28
    @11
    suceloni
    cC
    @15
    oecl
    syl2an
    @1
    @12
    @16
    ontr1
    syl
    mpan2d
    expcom
    adantr
    a2d
    @38
    @14
    wi
    #
    vy
    @4
    wral
    #
    @0
    @38
    @13
    wi
    #
    vy
    @4
    wral
    #
    wi
    #
    @4
    wlim
    #
    cA
    @4
    wcel
    #
    wa
    #
    @7
    @51
    @0
    @52
    wi
    #
    vy
    @4
    wral
    @54
    @50
    @58
    vy
    @4
    @38
    @0
    @13
    bi2.04
    ralbii
    @0
    @52
    vy
    @4
    r19.21v
    bitri
    @57
    @0
    @53
    @6
    @57
    @0
    @53
    @6
    wi
    @57
    @0
    wa
    #
    @53
    @1
    vy
    @4
    @12
    ciun
    #
    wcel
    #
    @6
    @57
    @53
    @61
    wi
    #
    @0
    @57
    @8
    @4
    wcel
    #
    @62
    @55
    @56
    @63
    @4
    cA
    limsuc
    biimpa
    @63
    @53
    @63
    @10
    wa
    @61
    @63
    @53
    @10
    @63
    @53
    cA
    @8
    wcel
    #
    @10
    @63
    @8
    cvv
    wcel
    #
    @64
    @8
    @4
    elex
    @65
    cA
    cvv
    wcel
    @64
    cA
    sucexb
    cA
    cvv
    sucidg
    sylbir
    syl
    @52
    @64
    @10
    wi
    vy
    @8
    @4
    @11
    @8
    wceq
    #
    @38
    @64
    @13
    @10
    @11
    @8
    cA
    eleq2
    @66
    @12
    @9
    @1
    @11
    @8
    cC
    coe
    oveq2
    #
    eleq2d
    imbi12d
    rspcv
    mpid
    anc2li
    vy
    @8
    @12
    @9
    @4
    @1
    @67
    eliuni
    syl6
    syl
    adantr
    @59
    @5
    @60
    @1
    @55
    @0
    @5
    @60
    wceq
    #
    @56
    @55
    @0
    wa
    @27
    @55
    @35
    @68
    @0
    @27
    @55
    @28
    adantl
    @55
    @0
    simpl
    @0
    @35
    @55
    @36
    adantl
    @27
    @4
    cvv
    wcel
    @55
    @35
    @68
    vx
    vex
    vy
    cC
    @4
    cvv
    oelim
    mpanlr1
    syl21anc
    adantlr
    eleq2d
    sylibrd
    ex
    a2d
    syl5bi
    tfindsg2
    impancom
end
