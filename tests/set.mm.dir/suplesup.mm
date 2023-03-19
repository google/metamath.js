include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cpnf.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wcel.mm"
include "wss.mm"
include "cr.mm"
include "ressxr.mm"
include "syl6ss.mm"
include "supxrcl.mm"
include "syl.mm"
include "adantr.mm"
include "eqidd.mm"
include "simpr.mm"
include "cv.mm"
include "wrex.mm"
include "wral.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "peano2re.mm"
include "adantl.mm"
include "wb.mm"
include "supxrunb2.mm"
include "mpbird.mm"
include "breq1.mm"
include "rexbidv.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "wi.mm"
include "w3a.mm"
include "cmin.mm"
include "crp.mm"
include "1rp.mm"
include "a1i.mm"
include "r19.21bi.mm"
include "oveq2.mm"
include "breq1d.mm"
include "adantlr.mm"
include "3adant3.mm"
include "nfv.mm"
include "simp11r.mm"
include "sseldi.mm"
include "sselda.mm"
include "1red.mm"
include "resubcld.mm"
include "3ad2ant1.mm"
include "3ad2antl1.mm"
include "simp3.mm"
include "simp1r.mm"
include "ltaddsubd.mm"
include "mpbid.mm"
include "xrlttrd.mm"
include "3exp.mm"
include "reximdai.mm"
include "mpd.mm"
include "rexlimdv.mm"
include "ad2antrr.mm"
include "xrltled.mm"
include "ex.mm"
include "adantllr.mm"
include "reximdva.mm"
include "ralrimiva.mm"
include "supxrunb1.mm"
include "3eqtr4d.mm"
include "xreqled.mm"
include "wn.mm"
include "c0.mm"
include "cmnf.mm"
include "supeq1.mm"
include "xrsup0.mm"
include "eqtrd.mm"
include "mnfle.mm"
include "eqbrtrd.mm"
include "simpll.mm"
include "wne.mm"
include "neqne.mm"
include "supxrgtmnf.mm"
include "simpl.mm"
include "nltpnft.mm"
include "3syl.mm"
include "mtbid.mm"
include "notnotr.mm"
include "jca.mm"
include "xrrebnd.mm"
include "c2.mm"
include "cdiv.mm"
include "rphalfcld.mm"
include "ltsubrpd.mm"
include "rpre.mm"
include "2re.mm"
include "cc0.mm"
include "2ne0.mm"
include "redivcld.mm"
include "supxrlub.mm"
include "rphalfcl.mm"
include "3ad2ant2.mm"
include "3adant2.mm"
include "ad5ant134.mm"
include "cc.mm"
include "recn.mm"
include "recnd.mm"
include "halfcld.mm"
include "subsub4d.mm"
include "2halvesd.mm"
include "oveq2d.mm"
include "eqtr2d.mm"
include "adantll.mm"
include "ad3antrrr.mm"
include "sylanl2.mm"
include "ad2antlr.mm"
include "simp-6l.mm"
include "simplr.mm"
include "simp-6r.mm"
include "ad5antlr.mm"
include "rehalfcld.mm"
include "simp-4r.mm"
include "simpllr.mm"
include "ltsub1dd.mm"
include "rexlimdva.mm"
include "supxrgere.mm"
include "pm2.61dan.mm"

theorem suplesup
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vr: setvar r
  let vw: setvar w
  assume suplesup.a: |- ( ph -> A C_ RR )
  assume suplesup.b: |- ( ph -> B C_ RR* )
  assume suplesup.c: |- ( ph -> A. x e. A A. y e. RR+ E. z e. B ( x - y ) < z )

  disjoint A x
  disjoint A z
  disjoint x z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint x y
  disjoint y z
  disjoint ph x
  disjoint ph z
  disjoint A r
  disjoint A w
  disjoint r w
  disjoint r x
  disjoint w x
  disjoint w z
  disjoint B w
  disjoint w y
  disjoint ph w
  assert |- ( ph -> sup ( A , RR* , < ) <_ sup ( B , RR* , < ) )

  proof
    wph
    cA
    cxr
    clt
    csup
    #
    cpnf
    wceq
    #
    @0
    cB
    cxr
    clt
    csup
    #
    cle
    wbr
    #
    wph
    @1
    wa
    #
    @0
    @2
    wph
    @0
    cxr
    wcel
    #
    @1
    wph
    cA
    cxr
    wss
    #
    @5
    wph
    cA
    cr
    cxr
    suplesup.a
    ressxr
    syl6ss
    #
    cA
    supxrcl
    syl
    #
    adantr
    @4
    cpnf
    cpnf
    @0
    @2
    @4
    cpnf
    eqidd
    wph
    @1
    simpr
    #
    @4
    vw
    cv
    #
    vz
    cv
    #
    cle
    wbr
    #
    vz
    cB
    wrex
    #
    vw
    cr
    wral
    #
    @2
    cpnf
    wceq
    #
    @4
    @13
    vw
    cr
    @4
    @10
    cr
    wcel
    #
    wa
    #
    @10
    @11
    clt
    wbr
    #
    vz
    cB
    wrex
    #
    @13
    @17
    @10
    c1
    caddc
    co
    #
    vx
    cv
    #
    clt
    wbr
    #
    vx
    cA
    wrex
    #
    @19
    @17
    @20
    cr
    wcel
    #
    vr
    cv
    #
    @21
    clt
    wbr
    #
    vx
    cA
    wrex
    #
    vr
    cr
    wral
    #
    @23
    @16
    @24
    @4
    @10
    peano2re
    adantl
    @4
    @28
    @16
    @4
    @28
    @1
    @9
    @4
    @6
    @28
    @1
    wb
    wph
    @6
    @1
    @7
    adantr
    vr
    vx
    cA
    supxrunb2
    syl
    mpbird
    adantr
    @27
    @23
    vr
    @20
    cr
    @25
    @20
    wceq
    @26
    @22
    vx
    cA
    @25
    @20
    @21
    clt
    breq1
    rexbidv
    rspcva
    syl2anc
    @17
    @22
    @19
    vx
    cA
    wph
    @16
    @21
    cA
    wcel
    #
    @22
    @19
    wi
    wi
    @1
    wph
    @16
    wa
    #
    @29
    @22
    @19
    @30
    @29
    @22
    w3a
    #
    @21
    c1
    cmin
    co
    #
    @11
    clt
    wbr
    #
    vz
    cB
    wrex
    #
    @19
    @30
    @29
    @34
    @22
    wph
    @29
    @34
    @16
    wph
    @29
    wa
    #
    c1
    crp
    wcel
    #
    @21
    vy
    cv
    #
    cmin
    co
    #
    @11
    clt
    wbr
    #
    vz
    cB
    wrex
    #
    vy
    crp
    wral
    #
    @34
    @36
    @35
    1rp
    a1i
    wph
    @41
    vx
    cA
    suplesup.c
    r19.21bi
    #
    @40
    @34
    vy
    c1
    crp
    @37
    c1
    wceq
    #
    @39
    @33
    vz
    cB
    @43
    @38
    @32
    @11
    clt
    @37
    c1
    @21
    cmin
    oveq2
    breq1d
    rexbidv
    rspcva
    syl2anc
    adantlr
    3adant3
    @31
    @33
    @18
    vz
    cB
    @31
    vz
    nfv
    @31
    @11
    cB
    wcel
    #
    @33
    @18
    @31
    @44
    @33
    w3a
    #
    @10
    @32
    @11
    @45
    cr
    cxr
    @10
    ressxr
    wph
    @16
    @29
    @22
    @44
    @33
    simp11r
    sseldi
    @45
    cr
    cxr
    @32
    ressxr
    @31
    @44
    @32
    cr
    wcel
    #
    @33
    @30
    @29
    @46
    @22
    wph
    @29
    @46
    @16
    @35
    @21
    c1
    wph
    cA
    cr
    @21
    suplesup.a
    sselda
    #
    @35
    1red
    resubcld
    adantlr
    3adant3
    3ad2ant1
    sseldi
    @31
    @44
    @11
    cxr
    wcel
    #
    @33
    @30
    @29
    @44
    @48
    @22
    wph
    @44
    @48
    @16
    wph
    cB
    cxr
    @11
    suplesup.b
    sselda
    #
    adantlr
    #
    3ad2antl1
    3adant3
    @31
    @44
    @10
    @32
    clt
    wbr
    #
    @33
    @31
    @22
    @51
    @30
    @29
    @22
    simp3
    @31
    @10
    c1
    @21
    wph
    @16
    @29
    @22
    simp1r
    @31
    1red
    @30
    @29
    @21
    cr
    wcel
    #
    @22
    wph
    @29
    @52
    @16
    @47
    adantlr
    #
    3adant3
    ltaddsubd
    mpbid
    3ad2ant1
    @31
    @44
    @33
    simp3
    xrlttrd
    3exp
    reximdai
    mpd
    3exp
    adantlr
    rexlimdv
    mpd
    @17
    @18
    @12
    vz
    cB
    wph
    @16
    @44
    @18
    @12
    wi
    @1
    @30
    @44
    wa
    #
    @18
    @12
    @54
    @18
    wa
    @10
    @11
    @30
    @10
    cxr
    wcel
    @44
    @18
    wph
    cr
    cxr
    @10
    cr
    cxr
    wss
    wph
    ressxr
    a1i
    sselda
    ad2antrr
    @54
    @48
    @18
    @50
    adantr
    @54
    @18
    simpr
    xrltled
    ex
    adantllr
    reximdva
    mpd
    ralrimiva
    wph
    @14
    @15
    wb
    #
    @1
    wph
    cB
    cxr
    wss
    #
    @55
    suplesup.b
    vw
    vz
    cB
    supxrunb1
    syl
    adantr
    mpbid
    3eqtr4d
    xreqled
    wph
    @1
    wn
    #
    wa
    #
    cA
    c0
    wceq
    #
    @3
    wph
    @59
    @3
    @57
    wph
    @59
    wa
    @0
    cmnf
    @2
    cle
    @59
    @0
    cmnf
    wceq
    wph
    @59
    @0
    c0
    cxr
    clt
    csup
    #
    cmnf
    cxr
    cA
    c0
    clt
    supeq1
    @60
    cmnf
    wceq
    @59
    xrsup0
    a1i
    eqtrd
    adantl
    wph
    cmnf
    @2
    cle
    wbr
    #
    @59
    wph
    @2
    cxr
    wcel
    #
    @61
    wph
    @56
    @62
    suplesup.b
    cB
    supxrcl
    syl
    @2
    mnfle
    syl
    adantr
    eqbrtrd
    adantlr
    @58
    @59
    wn
    #
    wa
    #
    wph
    @0
    cr
    wcel
    #
    @3
    wph
    @57
    @63
    simpll
    #
    @64
    @65
    cmnf
    @0
    clt
    wbr
    #
    @0
    cpnf
    clt
    wbr
    #
    wa
    #
    @64
    @67
    @68
    wph
    @63
    @67
    @57
    wph
    @63
    wa
    cA
    cr
    wss
    #
    cA
    c0
    wne
    #
    @67
    wph
    @70
    @63
    suplesup.a
    adantr
    @63
    @71
    wph
    cA
    c0
    neqne
    adantl
    cA
    supxrgtmnf
    syl2anc
    adantlr
    @58
    @68
    @63
    @58
    @68
    wn
    #
    wn
    @68
    @58
    @1
    @72
    wph
    @57
    simpr
    @58
    wph
    @5
    @1
    @72
    wb
    wph
    @57
    simpl
    @8
    @0
    nltpnft
    3syl
    mtbid
    @68
    notnotr
    syl
    adantr
    jca
    @64
    @5
    @65
    @69
    wb
    @64
    wph
    @5
    @66
    @8
    syl
    @0
    xrrebnd
    syl
    mpbird
    wph
    @65
    wa
    #
    vw
    vz
    cB
    @0
    @73
    vw
    nfv
    wph
    @56
    @65
    suplesup.b
    adantr
    wph
    @65
    simpr
    #
    @73
    @10
    crp
    wcel
    #
    wa
    #
    @0
    @10
    c2
    cdiv
    co
    #
    cmin
    co
    #
    @21
    clt
    wbr
    #
    vx
    cA
    wrex
    #
    @0
    @10
    cmin
    co
    #
    @11
    clt
    wbr
    #
    vz
    cB
    wrex
    #
    @76
    @78
    @0
    clt
    wbr
    #
    @80
    @76
    @0
    @77
    @73
    @65
    @75
    @74
    adantr
    #
    @76
    @10
    @73
    @75
    simpr
    rphalfcld
    ltsubrpd
    @76
    @6
    @78
    cxr
    wcel
    @84
    @80
    wb
    wph
    @6
    @65
    @75
    @7
    ad2antrr
    @76
    cr
    cxr
    @78
    ressxr
    @76
    @0
    @77
    @85
    @75
    @77
    cr
    wcel
    #
    @73
    @75
    @10
    c2
    @10
    rpre
    #
    c2
    cr
    wcel
    @75
    2re
    a1i
    c2
    cc0
    wne
    @75
    2ne0
    a1i
    redivcld
    #
    adantl
    #
    resubcld
    #
    sseldi
    vx
    cA
    @78
    supxrlub
    syl2anc
    mpbid
    @76
    @79
    @83
    vx
    cA
    @76
    @29
    wa
    #
    @79
    @83
    @91
    @79
    wa
    #
    @21
    @77
    cmin
    co
    #
    @11
    clt
    wbr
    #
    vz
    cB
    wrex
    #
    @83
    wph
    @75
    @29
    @95
    @65
    @79
    wph
    @75
    @29
    w3a
    @77
    crp
    wcel
    #
    @41
    @95
    @75
    wph
    @96
    @29
    @10
    rphalfcl
    3ad2ant2
    wph
    @29
    @41
    @75
    @42
    3adant2
    @40
    @95
    vy
    @77
    crp
    @37
    @77
    wceq
    #
    @39
    @94
    vz
    cB
    @97
    @38
    @93
    @11
    clt
    @37
    @77
    @21
    cmin
    oveq2
    breq1d
    rexbidv
    rspcva
    syl2anc
    ad5ant134
    @92
    @94
    @82
    vz
    cB
    @92
    @44
    wa
    #
    @94
    @82
    @98
    @94
    wa
    #
    @81
    @78
    @77
    cmin
    co
    #
    @11
    clt
    @91
    @81
    @100
    wceq
    #
    @79
    @44
    @94
    @76
    @101
    @29
    @65
    @75
    @101
    wph
    @65
    @75
    wa
    #
    @100
    @0
    @77
    @77
    caddc
    co
    #
    cmin
    co
    #
    @81
    @102
    @0
    @77
    @77
    @65
    @0
    cc
    wcel
    @75
    @0
    recn
    adantr
    @102
    @10
    @75
    @10
    cc
    wcel
    @65
    @75
    @10
    @87
    recnd
    #
    adantl
    halfcld
    #
    @106
    subsub4d
    @75
    @104
    @81
    wceq
    @65
    @75
    @103
    @10
    @0
    cmin
    @75
    @10
    @105
    2halvesd
    oveq2d
    adantl
    eqtr2d
    adantll
    adantr
    ad3antrrr
    @99
    @100
    @93
    @11
    @99
    cr
    cxr
    @100
    ressxr
    @91
    @100
    cr
    wcel
    #
    @79
    @44
    @94
    @76
    @107
    @29
    @76
    @78
    @77
    @90
    @89
    resubcld
    adantr
    ad3antrrr
    sseldi
    @99
    cr
    cxr
    @93
    ressxr
    @91
    @93
    cr
    wcel
    #
    @79
    @44
    @94
    wph
    @75
    @29
    @108
    @65
    wph
    @75
    wa
    @29
    wa
    @21
    @77
    @75
    wph
    @16
    @29
    @52
    @87
    @53
    sylanl2
    @75
    @86
    wph
    @29
    @88
    ad2antlr
    resubcld
    adantllr
    ad3antrrr
    sseldi
    @99
    wph
    @44
    @48
    wph
    @65
    @75
    @29
    @79
    @44
    @94
    simp-6l
    #
    @92
    @44
    @94
    simplr
    @49
    syl2anc
    @99
    @78
    @21
    @77
    @99
    @0
    @77
    wph
    @65
    @75
    @29
    @79
    @44
    @94
    simp-6r
    @99
    @10
    @75
    @16
    @73
    @29
    @79
    @44
    @94
    @87
    ad5antlr
    rehalfcld
    #
    resubcld
    @99
    wph
    @29
    @52
    @109
    @76
    @29
    @79
    @44
    @94
    simp-4r
    @47
    syl2anc
    @110
    @91
    @79
    @44
    @94
    simpllr
    ltsub1dd
    @98
    @94
    simpr
    xrlttrd
    eqbrtrd
    ex
    reximdva
    mpd
    ex
    rexlimdva
    mpd
    supxrgere
    syl2anc
    pm2.61dan
    pm2.61dan
end
