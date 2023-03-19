include "con0.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "csuc.mm"
include "comu.mm"
include "co.mm"
include "wrex.mm"
include "coa.mm"
include "wceq.mm"
include "simp2.mm"
include "wss.mm"
include "sucelon.mm"
include "sylib.mm"
include "simp1.mm"
include "on0eln0.mm"
include "biimpar.mm"
include "3adant2.mm"
include "omword2.mm"
include "syl21anc.mm"
include "sucidg.mm"
include "ssel.mm"
include "syl5.mm"
include "sylc.mm"
include "suceq.mm"
include "oveq2d.mm"
include "eleq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wn.mm"
include "wral.mm"
include "wa.mm"
include "weq.mm"
include "onminex.mm"
include "wi.mm"
include "wlim.mm"
include "w3o.mm"
include "word.mm"
include "vex.mm"
include "elon.mm"
include "ordzsl.mm"
include "bitri.mm"
include "noel.mm"
include "oveq2.mm"
include "om0x.mm"
include "syl6eq.mm"
include "mtbiri.mm"
include "a1i.mm"
include "simp3.mm"
include "raleq.mm"
include "sucid.mm"
include "notbid.mm"
include "rspcv.mm"
include "ax-mp.mm"
include "syl6bi.mm"
include "3expia.mm"
include "rexlimdvw.mm"
include "ralnex.mm"
include "ciun.mm"
include "cvv.mm"
include "simpr.mm"
include "simpl.mm"
include "omlim.mm"
include "syl12anc.mm"
include "eliun.mm"
include "wel.mm"
include "limord.mm"
include "3ad2ant1.mm"
include "sylibr.mm"
include "onelon.mm"
include "suceloni.mm"
include "syl.mm"
include "sssucid.mm"
include "omwordi.mm"
include "mpi.mm"
include "syl3anc.mm"
include "sseld.mm"
include "reximdvai.mm"
include "syl5bi.mm"
include "sylbid.mm"
include "con3d.mm"
include "expimpd.mm"
include "com12.mm"
include "3ad2antl1.mm"
include "3jaod.mm"
include "impr.mm"
include "wb.mm"
include "simpl1.mm"
include "simprr.mm"
include "omcl.mm"
include "simpl2.mm"
include "ontri1.mm"
include "mpbird.mm"
include "oawordex.mm"
include "mpbid.mm"
include "3adantr1.mm"
include "simp3r.mm"
include "simp21.mm"
include "simp11.mm"
include "simp23.mm"
include "omsuc.mm"
include "eleqtrd.mm"
include "eqeltrd.mm"
include "simp3l.mm"
include "oaord.mm"
include "jca.mm"
include "reximdv2.mm"
include "mpd.mm"
include "expcom.mm"
include "com13.mm"

theorem omeulem1
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vz: setvar z

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint A w
  disjoint A z
  disjoint w x
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint B w
  disjoint B z
  assert |- ( ( A e. On /\ B e. On /\ A =/= (/) ) -> E. x e. On E. y e. A ( ( A .o x ) +o y ) = B )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    cA
    c0
    wne
    #
    w3a
    #
    cB
    cA
    vx
    cv
    #
    csuc
    #
    comu
    co
    #
    wcel
    #
    vx
    con0
    wrex
    #
    cA
    @4
    comu
    co
    #
    vy
    cv
    #
    coa
    co
    #
    cB
    wceq
    #
    vy
    cA
    wrex
    #
    vx
    con0
    wrex
    #
    @3
    @1
    cB
    cA
    cB
    csuc
    #
    comu
    co
    #
    wcel
    #
    @8
    @0
    @1
    @2
    simp2
    #
    @3
    @15
    @16
    wss
    #
    @1
    @17
    @3
    @15
    con0
    wcel
    #
    @0
    c0
    cA
    wcel
    #
    @19
    @3
    @1
    @20
    @18
    cB
    sucelon
    sylib
    @0
    @1
    @2
    simp1
    @0
    @2
    @21
    @1
    @0
    @21
    @2
    cA
    on0eln0
    biimpar
    3adant2
    @15
    cA
    omword2
    syl21anc
    @18
    @1
    cB
    @15
    wcel
    @19
    @17
    cB
    con0
    sucidg
    @15
    @16
    cB
    ssel
    syl5
    sylc
    @7
    @17
    vx
    cB
    con0
    @4
    cB
    wceq
    #
    @6
    @16
    cB
    @22
    @5
    @15
    cA
    comu
    @4
    cB
    suceq
    oveq2d
    eleq2d
    rspcev
    syl2anc
    @8
    @7
    cB
    cA
    vz
    cv
    #
    csuc
    #
    comu
    co
    #
    wcel
    #
    wn
    #
    vz
    @4
    wral
    #
    wa
    #
    vx
    con0
    wrex
    @3
    @14
    @7
    @26
    vx
    vz
    vx
    vz
    weq
    #
    @6
    @25
    cB
    @30
    @5
    @24
    cA
    comu
    @4
    @23
    suceq
    oveq2d
    eleq2d
    onminex
    @3
    @29
    @13
    vx
    con0
    @29
    @4
    con0
    wcel
    #
    @3
    @13
    @7
    @28
    @31
    @3
    @13
    wi
    @3
    @7
    @28
    @31
    w3a
    #
    @13
    @3
    @32
    wa
    #
    @12
    vy
    con0
    wrex
    #
    @13
    @3
    @28
    @31
    @34
    @7
    @3
    @28
    @31
    wa
    #
    wa
    #
    @9
    cB
    wss
    #
    @34
    @36
    @37
    cB
    @9
    wcel
    #
    wn
    #
    @3
    @28
    @31
    @39
    @31
    @4
    c0
    wceq
    #
    @4
    vw
    cv
    #
    csuc
    #
    wceq
    #
    vw
    con0
    wrex
    #
    @4
    wlim
    #
    w3o
    #
    @3
    @28
    wa
    #
    @39
    @31
    @4
    word
    #
    @46
    @4
    vx
    vex
    #
    elon
    #
    vw
    @4
    ordzsl
    bitri
    @47
    @40
    @39
    @44
    @45
    @40
    @39
    wi
    @47
    @40
    @38
    cB
    c0
    wcel
    cB
    noel
    @40
    @9
    c0
    cB
    @40
    @9
    cA
    c0
    comu
    co
    c0
    @4
    c0
    cA
    comu
    oveq2
    cA
    om0x
    syl6eq
    eleq2d
    mtbiri
    a1i
    @47
    @43
    @39
    vw
    con0
    @3
    @28
    @43
    @39
    @3
    @28
    @43
    w3a
    #
    @43
    cB
    cA
    @42
    comu
    co
    #
    wcel
    #
    wn
    #
    @39
    @3
    @28
    @43
    simp3
    #
    @51
    @43
    @28
    @54
    @55
    @3
    @28
    @43
    simp2
    @43
    @28
    @27
    vz
    @42
    wral
    #
    @54
    @27
    vz
    @4
    @42
    raleq
    @41
    @42
    wcel
    @56
    @54
    wi
    @41
    vw
    vex
    sucid
    @27
    @54
    vz
    @41
    @42
    vz
    vw
    weq
    #
    @26
    @53
    @57
    @25
    @52
    cB
    @57
    @24
    @42
    cA
    comu
    @23
    @41
    suceq
    oveq2d
    eleq2d
    notbid
    rspcv
    ax-mp
    syl6bi
    sylc
    @43
    @39
    @54
    @43
    @38
    @53
    @43
    @9
    @52
    cB
    @4
    @42
    cA
    comu
    oveq2
    eleq2d
    notbid
    biimpar
    syl2anc
    3expia
    rexlimdvw
    @0
    @1
    @28
    @45
    @39
    wi
    @2
    @45
    @0
    @28
    wa
    @39
    @45
    @0
    @28
    @39
    @28
    @26
    vz
    @4
    wrex
    #
    wn
    @45
    @0
    wa
    #
    @39
    @26
    vz
    @4
    ralnex
    @59
    @38
    @58
    @59
    @38
    cB
    vz
    @4
    cA
    @23
    comu
    co
    #
    ciun
    #
    wcel
    #
    @58
    @59
    @9
    @61
    cB
    @59
    @0
    @4
    cvv
    wcel
    #
    @45
    @9
    @61
    wceq
    @45
    @0
    simpr
    @63
    @59
    @49
    a1i
    @45
    @0
    simpl
    vz
    cA
    @4
    cvv
    omlim
    syl12anc
    eleq2d
    @62
    cB
    @60
    wcel
    #
    vz
    @4
    wrex
    @59
    @58
    vz
    cB
    @4
    @60
    eliun
    @59
    @64
    @26
    vz
    @4
    @45
    @0
    vz
    vx
    wel
    #
    @64
    @26
    wi
    @45
    @0
    @65
    w3a
    #
    @60
    @25
    cB
    @66
    @23
    con0
    wcel
    #
    @24
    con0
    wcel
    #
    @0
    @60
    @25
    wss
    #
    @66
    @31
    @65
    @67
    @66
    @48
    @31
    @45
    @0
    @48
    @65
    @4
    limord
    3ad2ant1
    @50
    sylibr
    @45
    @0
    @65
    simp3
    @4
    @23
    onelon
    syl2anc
    #
    @66
    @67
    @68
    @70
    @23
    suceloni
    syl
    @45
    @0
    @65
    simp2
    @67
    @68
    @0
    w3a
    @23
    @24
    wss
    @69
    @23
    sssucid
    @23
    @24
    cA
    omwordi
    mpi
    syl3anc
    sseld
    3expia
    reximdvai
    syl5bi
    sylbid
    con3d
    syl5bi
    expimpd
    com12
    3ad2antl1
    3jaod
    syl5bi
    impr
    @36
    @9
    con0
    wcel
    #
    @1
    @37
    @39
    wb
    @36
    @0
    @31
    @71
    @0
    @1
    @2
    @35
    simpl1
    @3
    @28
    @31
    simprr
    cA
    @4
    omcl
    #
    syl2anc
    #
    @0
    @1
    @2
    @35
    simpl2
    #
    @9
    cB
    ontri1
    syl2anc
    mpbird
    @36
    @71
    @1
    @37
    @34
    wb
    @73
    @74
    vy
    @9
    cB
    oawordex
    syl2anc
    mpbid
    3adantr1
    @33
    @12
    @12
    vy
    con0
    cA
    @3
    @32
    @10
    con0
    wcel
    #
    @12
    wa
    #
    @10
    cA
    wcel
    #
    @12
    wa
    @3
    @32
    @76
    w3a
    #
    @77
    @12
    @78
    @77
    @11
    @9
    cA
    coa
    co
    #
    wcel
    #
    @78
    @11
    cB
    @79
    @3
    @32
    @75
    @12
    simp3r
    #
    @78
    cB
    @6
    @79
    @3
    @7
    @28
    @31
    @76
    simp21
    @78
    @0
    @31
    @6
    @79
    wceq
    @0
    @1
    @2
    @32
    @76
    simp11
    #
    @3
    @7
    @28
    @31
    @76
    simp23
    #
    cA
    @4
    omsuc
    syl2anc
    eleqtrd
    eqeltrd
    @78
    @75
    @0
    @71
    @77
    @80
    wb
    @3
    @32
    @75
    @12
    simp3l
    @82
    @78
    @0
    @31
    @71
    @82
    @83
    @72
    syl2anc
    @10
    cA
    @9
    oaord
    syl3anc
    mpbird
    @81
    jca
    3expia
    reximdv2
    mpd
    expcom
    3expia
    com13
    reximdvai
    syl5
    mpd
end
