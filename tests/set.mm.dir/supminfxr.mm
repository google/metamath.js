include "c0.mm"
include "wceq.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cv.mm"
include "cneg.mm"
include "wcel.mm"
include "cr.mm"
include "crab.mm"
include "cinf.mm"
include "cxne.mm"
include "wa.mm"
include "cmnf.mm"
include "supeq1.mm"
include "xrsup0.mm"
include "a1i.mm"
include "eqtrd.mm"
include "adantl.mm"
include "cpnf.mm"
include "eleq2.mm"
include "rabbidv.mm"
include "wn.mm"
include "wral.mm"
include "noel.mm"
include "rgen.mm"
include "rabeq0.mm"
include "mpbir.mm"
include "infeq1d.mm"
include "xrinf0.mm"
include "xnegeqd.mm"
include "xnegpnf.mm"
include "eqtr4d.mm"
include "wne.mm"
include "neqne.mm"
include "cle.mm"
include "wbr.mm"
include "wrex.mm"
include "wss.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simpr.mm"
include "w3a.mm"
include "negn0.mm"
include "ublbneg.mm"
include "ssrab2.mm"
include "infrenegsup.mm"
include "mp3an1.mm"
include "syl2an.mm"
include "3impa.mm"
include "elrabi.mm"
include "ssel2.mm"
include "wb.mm"
include "negeq.mm"
include "eleq1d.mm"
include "elrab3.mm"
include "renegcl.mm"
include "syl.mm"
include "recn.mm"
include "negnegd.mm"
include "3bitrd.mm"
include "eqrdav.mm"
include "supeq1d.mm"
include "3ad2ant1.mm"
include "negeqd.mm"
include "infrecl.mm"
include "suprcl.mm"
include "cc.mm"
include "negcon2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "syl3anc.mm"
include "supxrre.mm"
include "infxrre.mm"
include "sylanl1.mm"
include "rexnegd.mm"
include "3eqtr4d.mm"
include "sselda.mm"
include "adantlr.mm"
include "ltnled.mm"
include "rexbidva.mm"
include "rexnal.mm"
include "bitrd.mm"
include "ralbidva.mm"
include "ralnex.mm"
include "adantr.mm"
include "mpbird.mm"
include "xnegmnf.mm"
include "eqcomi.mm"
include "ressxr.mm"
include "sstrd.mm"
include "supxrunb2.mm"
include "simpl.mm"
include "breq1.mm"
include "rexbidv.mm"
include "rspcva.mm"
include "adantll.mm"
include "wi.mm"
include "renegcld.mm"
include "ad4ant13.mm"
include "recnd.mm"
include "eqeltrd.mm"
include "elrabd.mm"
include "ad3antlr.mm"
include "ltnegd.mm"
include "simpllr.mm"
include "negneg.mm"
include "3syl.mm"
include "breqtrd.mm"
include "rspcev.mm"
include "rexlimdva2.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "sstri.mm"
include "infxrunb2.mm"
include "ax-mp.mm"
include "sylib.mm"
include "syldan.mm"
include "pm2.61dan.mm"
include "sylan2.mm"

theorem supminfxr
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume supminfxr.1: |- ( ph -> A C_ RR )

  disjoint A x
  disjoint A v
  disjoint A w
  disjoint A y
  disjoint A z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint ph v
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> sup ( A , RR* , < ) = -e inf ( { x e. RR | -u x e. A } , RR* , < ) )

  proof
    wph
    cA
    c0
    wceq
    #
    cA
    cxr
    clt
    csup
    #
    vx
    cv
    #
    cneg
    #
    cA
    wcel
    #
    vx
    cr
    crab
    #
    cxr
    clt
    cinf
    #
    cxne
    #
    wceq
    #
    wph
    @0
    wa
    @1
    cmnf
    @7
    @0
    @1
    cmnf
    wceq
    wph
    @0
    @1
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
    @9
    cmnf
    wceq
    @0
    xrsup0
    a1i
    eqtrd
    adantl
    @0
    @7
    cmnf
    wceq
    wph
    @0
    @7
    cpnf
    cxne
    #
    cmnf
    @0
    @6
    cpnf
    @0
    @6
    c0
    cxr
    clt
    cinf
    #
    cpnf
    @0
    cxr
    @5
    c0
    clt
    @0
    @5
    @3
    c0
    wcel
    #
    vx
    cr
    crab
    #
    c0
    @0
    @4
    @12
    vx
    cr
    cA
    c0
    @3
    eleq2
    rabbidv
    @13
    c0
    wceq
    #
    @0
    @14
    @12
    wn
    #
    vx
    cr
    wral
    @15
    vx
    cr
    @15
    @2
    cr
    wcel
    @3
    noel
    a1i
    rgen
    @12
    vx
    cr
    rabeq0
    mpbir
    a1i
    eqtrd
    infeq1d
    @11
    cpnf
    wceq
    @0
    xrinf0
    a1i
    eqtrd
    xnegeqd
    @10
    cmnf
    wceq
    @0
    xnegpnf
    a1i
    eqtrd
    adantl
    eqtr4d
    @0
    wn
    wph
    cA
    c0
    wne
    #
    @8
    cA
    c0
    neqne
    wph
    @16
    wa
    #
    vz
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vz
    cA
    wral
    #
    vy
    cr
    wrex
    #
    @8
    @17
    @22
    wa
    #
    cA
    cr
    clt
    csup
    #
    @5
    cr
    clt
    cinf
    #
    cneg
    #
    @1
    @7
    @23
    cA
    cr
    wss
    #
    @16
    @22
    @24
    @26
    wceq
    #
    wph
    @27
    @16
    @22
    supminfxr.1
    ad2antrr
    #
    wph
    @16
    @22
    simplr
    #
    @17
    @22
    simpr
    #
    @27
    @16
    @22
    w3a
    #
    @25
    @24
    cneg
    #
    wceq
    #
    @28
    @32
    @25
    vw
    cv
    #
    cneg
    #
    @5
    wcel
    #
    vw
    cr
    crab
    #
    cr
    clt
    csup
    #
    cneg
    #
    @33
    @27
    @16
    @22
    @25
    @40
    wceq
    #
    @27
    @16
    wa
    #
    @5
    c0
    wne
    #
    @19
    @18
    cle
    wbr
    vz
    @5
    wral
    vy
    cr
    wrex
    #
    @41
    @22
    vx
    cA
    negn0
    #
    vy
    vz
    vx
    cA
    ublbneg
    #
    @5
    cr
    wss
    #
    @43
    @44
    @41
    @4
    vx
    cr
    ssrab2
    #
    vy
    vz
    vw
    @5
    infrenegsup
    mp3an1
    syl2an
    3impa
    @32
    @39
    @24
    @27
    @16
    @39
    @24
    wceq
    @22
    @27
    cr
    @38
    cA
    clt
    @27
    vy
    @38
    cA
    cr
    @19
    @38
    wcel
    #
    @19
    cr
    wcel
    #
    @27
    @37
    vw
    @19
    cr
    elrabi
    adantl
    cA
    cr
    @19
    ssel2
    @50
    @49
    @19
    cA
    wcel
    #
    wb
    @27
    @50
    @49
    @19
    cneg
    #
    @5
    wcel
    #
    @52
    cneg
    #
    cA
    wcel
    #
    @51
    @37
    @53
    vw
    @19
    cr
    @35
    @19
    wceq
    @36
    @52
    @5
    @35
    @19
    negeq
    eleq1d
    elrab3
    @50
    @52
    cr
    wcel
    @53
    @55
    wb
    @19
    renegcl
    @4
    @55
    vx
    @52
    cr
    @2
    @52
    wceq
    @3
    @54
    cA
    @2
    @52
    negeq
    eleq1d
    elrab3
    syl
    @50
    @54
    @19
    cA
    @50
    @19
    @19
    recn
    negnegd
    eleq1d
    3bitrd
    adantl
    eqrdav
    supeq1d
    3ad2ant1
    negeqd
    eqtrd
    @32
    @25
    cr
    wcel
    #
    @24
    cr
    wcel
    #
    @34
    @28
    wb
    #
    @27
    @16
    @22
    @56
    @42
    @43
    @44
    @56
    @22
    @45
    @46
    @47
    @43
    @44
    @56
    @48
    vy
    vz
    @5
    infrecl
    mp3an1
    syl2an
    #
    3impa
    vy
    vz
    cA
    suprcl
    @56
    @25
    cc
    wcel
    @24
    cc
    wcel
    @58
    @57
    @25
    recn
    @24
    recn
    @25
    @24
    negcon2
    syl2an
    syl2anc
    mpbid
    syl3anc
    @23
    @27
    @16
    @22
    @1
    @24
    wceq
    @29
    @30
    @31
    vy
    vz
    cA
    supxrre
    syl3anc
    @23
    @7
    @25
    cxne
    @26
    @23
    @6
    @25
    @23
    @47
    @43
    @44
    @6
    @25
    wceq
    @47
    @23
    @48
    a1i
    @23
    @27
    @16
    @43
    @29
    @30
    @45
    syl2anc
    @23
    @22
    @44
    @31
    @46
    syl
    vy
    vz
    @5
    infxrre
    syl3anc
    xnegeqd
    @23
    @25
    wph
    @27
    @16
    @22
    @56
    supminfxr.1
    @59
    sylanl1
    rexnegd
    eqtrd
    3eqtr4d
    wph
    @22
    wn
    #
    @8
    @16
    wph
    @60
    @19
    @18
    clt
    wbr
    #
    vz
    cA
    wrex
    #
    vy
    cr
    wral
    #
    @8
    wph
    @60
    wa
    @63
    @60
    wph
    @60
    simpr
    wph
    @63
    @60
    wb
    @60
    wph
    @63
    @21
    wn
    #
    vy
    cr
    wral
    #
    @60
    wph
    @62
    @64
    vy
    cr
    wph
    @50
    wa
    #
    @62
    @20
    wn
    #
    vz
    cA
    wrex
    #
    @64
    @66
    @61
    @67
    vz
    cA
    @66
    @18
    cA
    wcel
    #
    wa
    @19
    @18
    wph
    @50
    @69
    simplr
    wph
    @69
    @18
    cr
    wcel
    #
    @50
    wph
    cA
    cr
    @18
    supminfxr.1
    sselda
    #
    adantlr
    ltnled
    rexbidva
    @68
    @64
    wb
    @66
    @20
    vz
    cA
    rexnal
    a1i
    bitrd
    ralbidva
    @65
    @60
    wb
    wph
    @21
    vy
    cr
    ralnex
    a1i
    bitrd
    adantr
    mpbird
    wph
    @63
    wa
    #
    cpnf
    cmnf
    cxne
    #
    @1
    @7
    cpnf
    @73
    wceq
    @72
    @73
    cpnf
    xnegmnf
    eqcomi
    a1i
    @72
    @63
    @1
    cpnf
    wceq
    #
    wph
    @63
    simpr
    wph
    @63
    @74
    wb
    #
    @63
    wph
    cA
    cxr
    wss
    @75
    wph
    cA
    cr
    cxr
    supminfxr.1
    cr
    cxr
    wss
    wph
    ressxr
    a1i
    sstrd
    vy
    vz
    cA
    supxrunb2
    syl
    adantr
    mpbid
    @72
    @6
    cmnf
    @72
    @35
    vv
    cv
    #
    clt
    wbr
    #
    vw
    @5
    wrex
    #
    vv
    cr
    wral
    #
    @6
    cmnf
    wceq
    #
    @72
    @78
    vv
    cr
    @72
    @76
    cr
    wcel
    #
    wa
    @76
    cneg
    #
    @18
    clt
    wbr
    #
    vz
    cA
    wrex
    #
    @78
    @63
    @81
    @84
    wph
    @63
    @81
    wa
    @82
    cr
    wcel
    #
    @63
    @84
    @81
    @85
    @63
    @76
    renegcl
    #
    adantl
    @63
    @81
    simpl
    @62
    @84
    vy
    @82
    cr
    @19
    @82
    wceq
    @61
    @83
    vz
    cA
    @19
    @82
    @18
    clt
    breq1
    rexbidv
    rspcva
    syl2anc
    adantll
    wph
    @81
    @84
    @78
    wi
    @63
    wph
    @81
    wa
    #
    @83
    @78
    vz
    cA
    @87
    @69
    wa
    #
    @83
    wa
    #
    @18
    cneg
    #
    @5
    wcel
    @90
    @76
    clt
    wbr
    #
    @78
    @89
    @4
    @90
    cneg
    #
    cA
    wcel
    #
    vx
    @90
    cr
    @2
    @90
    wceq
    @3
    @92
    cA
    @2
    @90
    negeq
    eleq1d
    wph
    @69
    @90
    cr
    wcel
    @81
    @83
    wph
    @69
    wa
    #
    @18
    @71
    renegcld
    ad4ant13
    wph
    @69
    @93
    @81
    @83
    @94
    @92
    @18
    cA
    @94
    @18
    @94
    @18
    @71
    recnd
    negnegd
    wph
    @69
    simpr
    eqeltrd
    ad4ant13
    elrabd
    @89
    @90
    @82
    cneg
    #
    @76
    clt
    @89
    @83
    @90
    @95
    clt
    wbr
    @88
    @83
    simpr
    @89
    @82
    @18
    @81
    @85
    wph
    @69
    @83
    @86
    ad3antlr
    wph
    @69
    @70
    @81
    @83
    @71
    ad4ant13
    ltnegd
    mpbid
    @89
    @81
    @76
    cc
    wcel
    @95
    @76
    wceq
    wph
    @81
    @69
    @83
    simpllr
    @76
    recn
    @76
    negneg
    3syl
    breqtrd
    @77
    @91
    vw
    @90
    @5
    @35
    @90
    @76
    clt
    breq1
    rspcev
    syl2anc
    rexlimdva2
    adantlr
    mpd
    ralrimiva
    @5
    cxr
    wss
    @79
    @80
    wb
    @5
    cr
    cxr
    @48
    ressxr
    sstri
    vv
    vw
    @5
    infxrunb2
    ax-mp
    sylib
    xnegeqd
    3eqtr4d
    syldan
    adantlr
    pm2.61dan
    sylan2
    pm2.61dan
end
