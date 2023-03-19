include "con0.mm"
include "wcel.mm"
include "coe.mm"
include "co.mm"
include "comu.mm"
include "wceq.mm"
include "cv.mm"
include "c0.mm"
include "csuc.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "c1o.mm"
include "oecl.mm"
include "mpan.mm"
include "oe0.mm"
include "syl.mm"
include "om0.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "eqtr4d.mm"
include "wi.mm"
include "wa.mm"
include "oveq1.mm"
include "oesuc.mm"
include "sylan.mm"
include "coa.mm"
include "omsuc.mm"
include "omcl.mm"
include "oeoa.mm"
include "mp3an1.mm"
include "anabss1.mm"
include "eqtrd.mm"
include "syl5ibr.mm"
include "expcom.mm"
include "wlim.mm"
include "wral.mm"
include "ciun.mm"
include "iuneq2.mm"
include "cvv.mm"
include "vex.mm"
include "oen0.mm"
include "mpan2.mm"
include "oelim.mm"
include "sylanl1.mm"
include "sylan2.mm"
include "mpanl1.mm"
include "mpanr1.mm"
include "omlim.mm"
include "wne.mm"
include "a1i.mm"
include "word.mm"
include "limord.mm"
include "ordelon.mm"
include "anassrs.mm"
include "ralrimiva.mm"
include "0ellim.mm"
include "ne0i.mm"
include "adantl.mm"
include "wss.mm"
include "w3a.mm"
include "oewordi.mm"
include "mp3an3.mm"
include "3impia.mm"
include "onoviun.mm"
include "syl3anc.mm"
include "tfinds3.mm"
include "impcom.mm"

theorem oeoelem
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume oeoelem.1: |- A e. On
  assume oeoelem.2: |- (/) e. A


  assert |- ( ( B e. On /\ C e. On ) -> ( ( A ^o B ) ^o C ) = ( A ^o ( B .o C ) ) )

  proof
    cC
    con0
    wcel
    cB
    con0
    wcel
    #
    cA
    cB
    coe
    co
    #
    cC
    coe
    co
    #
    cA
    cB
    cC
    comu
    co
    #
    coe
    co
    #
    wceq
    #
    @1
    vx
    cv
    #
    coe
    co
    #
    cA
    cB
    @6
    comu
    co
    #
    coe
    co
    #
    wceq
    #
    @1
    c0
    coe
    co
    #
    cA
    cB
    c0
    comu
    co
    #
    coe
    co
    #
    wceq
    @1
    vy
    cv
    #
    coe
    co
    #
    cA
    cB
    @14
    comu
    co
    #
    coe
    co
    #
    wceq
    #
    @1
    @14
    csuc
    #
    coe
    co
    #
    cA
    cB
    @19
    comu
    co
    #
    coe
    co
    #
    wceq
    #
    @5
    @0
    vx
    vy
    cC
    @6
    c0
    wceq
    #
    @7
    @11
    @9
    @13
    @6
    c0
    @1
    coe
    oveq2
    @24
    @8
    @12
    cA
    coe
    @6
    c0
    cB
    comu
    oveq2
    oveq2d
    eqeq12d
    @6
    @14
    wceq
    #
    @7
    @15
    @9
    @17
    @6
    @14
    @1
    coe
    oveq2
    @25
    @8
    @16
    cA
    coe
    @6
    @14
    cB
    comu
    oveq2
    oveq2d
    eqeq12d
    @6
    @19
    wceq
    #
    @7
    @20
    @9
    @22
    @6
    @19
    @1
    coe
    oveq2
    @26
    @8
    @21
    cA
    coe
    @6
    @19
    cB
    comu
    oveq2
    oveq2d
    eqeq12d
    @6
    cC
    wceq
    #
    @7
    @2
    @9
    @4
    @6
    cC
    @1
    coe
    oveq2
    @27
    @8
    @3
    cA
    coe
    @6
    cC
    cB
    comu
    oveq2
    oveq2d
    eqeq12d
    @0
    @11
    c1o
    @13
    @0
    @1
    con0
    wcel
    #
    @11
    c1o
    wceq
    cA
    con0
    wcel
    #
    @0
    @28
    oeoelem.1
    cA
    cB
    oecl
    #
    mpan
    #
    @1
    oe0
    syl
    @0
    @13
    cA
    c0
    coe
    co
    #
    c1o
    @0
    @12
    c0
    cA
    coe
    cB
    om0
    oveq2d
    @29
    @32
    c1o
    wceq
    oeoelem.1
    cA
    oe0
    ax-mp
    syl6eq
    eqtr4d
    @0
    @14
    con0
    wcel
    #
    @18
    @23
    wi
    @18
    @23
    @0
    @33
    wa
    #
    @15
    @1
    comu
    co
    #
    @17
    @1
    comu
    co
    #
    wceq
    @15
    @17
    @1
    comu
    oveq1
    @34
    @20
    @35
    @22
    @36
    @0
    @28
    @33
    @20
    @35
    wceq
    @31
    @1
    @14
    oesuc
    sylan
    @34
    @22
    cA
    @16
    cB
    coa
    co
    #
    coe
    co
    #
    @36
    @34
    @21
    @37
    cA
    coe
    cB
    @14
    omsuc
    oveq2d
    @0
    @33
    @38
    @36
    wceq
    #
    @34
    @16
    con0
    wcel
    #
    @0
    @39
    cB
    @14
    omcl
    #
    @29
    @40
    @0
    @39
    oeoelem.1
    cA
    @16
    cB
    oeoa
    mp3an1
    sylan
    anabss1
    eqtrd
    eqeq12d
    syl5ibr
    expcom
    @0
    @6
    wlim
    #
    @18
    vy
    @6
    wral
    #
    @10
    wi
    @43
    @10
    @0
    @42
    wa
    #
    vy
    @6
    @15
    ciun
    #
    vy
    @6
    @17
    ciun
    #
    wceq
    vy
    @6
    @15
    @17
    iuneq2
    @44
    @7
    @45
    @9
    @46
    @0
    @6
    cvv
    wcel
    #
    @42
    @7
    @45
    wceq
    #
    vx
    vex
    #
    @29
    @0
    @47
    @42
    wa
    #
    @48
    oeoelem.1
    @29
    @0
    wa
    #
    @50
    @48
    @51
    @51
    @50
    wa
    c0
    @1
    wcel
    #
    @48
    @51
    c0
    cA
    wcel
    #
    @52
    oeoelem.2
    cA
    cB
    oen0
    mpan2
    @51
    @28
    @50
    @52
    @48
    @30
    vy
    @1
    @6
    cvv
    oelim
    sylanl1
    sylan2
    anabss1
    mpanl1
    mpanr1
    @44
    @9
    cA
    vy
    @6
    @16
    ciun
    #
    coe
    co
    #
    @46
    @44
    @8
    @54
    cA
    coe
    @0
    @47
    @42
    @8
    @54
    wceq
    @49
    vy
    cB
    @6
    cvv
    omlim
    mpanr1
    oveq2d
    @44
    @47
    @40
    vy
    @6
    wral
    @6
    c0
    wne
    #
    @55
    @46
    wceq
    @47
    @44
    @49
    a1i
    @44
    @40
    vy
    @6
    @0
    @42
    @14
    @6
    wcel
    #
    @40
    @42
    @57
    wa
    @0
    @33
    @40
    @42
    @6
    word
    @57
    @33
    @6
    limord
    @6
    @14
    ordelon
    sylan
    @41
    sylan2
    anassrs
    ralrimiva
    @42
    @56
    @0
    @42
    c0
    @6
    wcel
    @56
    @6
    0ellim
    @6
    c0
    ne0i
    syl
    adantl
    vz
    vw
    vy
    cA
    cvv
    coe
    @6
    @16
    vw
    cv
    #
    cvv
    wcel
    #
    @58
    wlim
    #
    cA
    @58
    coe
    co
    #
    vz
    @58
    cA
    vz
    cv
    #
    coe
    co
    #
    ciun
    wceq
    #
    vw
    vex
    @29
    @59
    @60
    wa
    #
    @64
    oeoelem.1
    @29
    @65
    wa
    @53
    @64
    oeoelem.2
    vz
    cA
    @58
    cvv
    oelim
    mpan2
    mpan
    mpan
    @62
    con0
    wcel
    #
    @58
    con0
    wcel
    #
    @62
    @58
    wss
    #
    @63
    @61
    wss
    #
    @66
    @67
    @29
    @68
    @69
    wi
    #
    oeoelem.1
    @66
    @67
    @29
    w3a
    @53
    @70
    oeoelem.2
    @62
    @58
    cA
    oewordi
    mpan2
    mp3an3
    3impia
    onoviun
    syl3anc
    eqtrd
    eqeq12d
    syl5ibr
    expcom
    tfinds3
    impcom
end
