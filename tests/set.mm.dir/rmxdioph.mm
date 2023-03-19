include "c1.mm"
include "cv.mm"
include "cfv.mm"
include "c2.mm"
include "cuz.mm"
include "wcel.mm"
include "c3.mm"
include "crmx.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cn0.mm"
include "cfz.mm"
include "cmap.mm"
include "crab.mm"
include "crmy.mm"
include "cexp.mm"
include "cmin.mm"
include "cmul.mm"
include "wrex.mm"
include "cdioph.mm"
include "wb.mm"
include "simpr.mm"
include "wf.mm"
include "elmapi.mm"
include "df-3.mm"
include "ssid.mm"
include "jm2.27dlem5.mm"
include "2nn.mm"
include "jm2.27dlem3.mm"
include "sselii.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "adantr.mm"
include "3nn.mm"
include "rmxdiophlem.mm"
include "syl3anc.mm"
include "pm5.32da.mm"
include "anass.mm"
include "rexbii.mm"
include "r19.42v.mm"
include "bitr2i.mm"
include "syl6bb.mm"
include "rabbiia.mm"
include "c4.mm"
include "wsbc.mm"
include "cres.mm"
include "3nn0.mm"
include "vex.mm"
include "resex.mm"
include "fvex.mm"
include "df-2.mm"
include "1nn.mm"
include "jm2.27dlem1.mm"
include "eleq1d.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "oveq1d.mm"
include "oveq1.mm"
include "oveqan12d.mm"
include "eqeq1d.mm"
include "sbc2ie.mm"
include "rabbii.mm"
include "4nn0.mm"
include "rmydioph.mm"
include "w3a.mm"
include "simp1.mm"
include "simp3.mm"
include "simp2.mm"
include "df-4.mm"
include "4nn.mm"
include "rabren3dioph.mm"
include "mp2an.mm"
include "cz.mm"
include "cmpt.mm"
include "cmzp.mm"
include "cvv.mm"
include "ovex.mm"
include "mzpproj.mm"
include "2nn0.mm"
include "mzpexpmpt.mm"
include "1z.mm"
include "mzpconstmpt.mm"
include "mzpsubmpt.mm"
include "mzpmulmpt.mm"
include "eqrabdioph.mm"
include "mp3an.mm"
include "anrabdioph.mm"
include "eqeltri.mm"
include "rexfrabdioph.mm"

theorem rmxdioph
  let va: setvar a
  let vb: setvar b
  let vc: setvar c


  assert |- { a e. ( NN0 ^m ( 1 ... 3 ) ) | ( ( a ` 1 ) e. ( ZZ>= ` 2 ) /\ ( a ` 3 ) = ( ( a ` 1 ) rmX ( a ` 2 ) ) ) } e. ( Dioph ` 3 )

  proof
    c1
    va
    cv
    #
    cfv
    #
    c2
    cuz
    cfv
    #
    wcel
    #
    c3
    @0
    cfv
    #
    @1
    c2
    @0
    cfv
    #
    crmx
    co
    wceq
    #
    wa
    #
    va
    cn0
    c1
    c3
    cfz
    co
    #
    cmap
    co
    #
    crab
    @3
    vb
    cv
    #
    @1
    @5
    crmy
    co
    #
    wceq
    #
    wa
    #
    @4
    c2
    cexp
    co
    #
    @1
    c2
    cexp
    co
    #
    c1
    cmin
    co
    #
    @10
    c2
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    c1
    wceq
    #
    wa
    #
    vb
    cn0
    wrex
    #
    va
    @9
    crab
    #
    c3
    cdioph
    cfv
    #
    @7
    @22
    va
    @9
    @0
    @9
    wcel
    #
    @7
    @3
    @12
    @20
    wa
    #
    vb
    cn0
    wrex
    #
    wa
    #
    @22
    @25
    @3
    @6
    @27
    @25
    @3
    wa
    @3
    @5
    cn0
    wcel
    #
    @4
    cn0
    wcel
    #
    @6
    @27
    wb
    @25
    @3
    simpr
    @25
    @29
    @3
    @25
    @8
    cn0
    @0
    wf
    #
    c2
    @8
    wcel
    @29
    @0
    cn0
    @8
    elmapi
    #
    c1
    c2
    cfz
    co
    #
    @8
    c2
    c2
    c3
    c3
    df-3
    @8
    ssid
    jm2.27dlem5
    #
    c2
    2nn
    jm2.27dlem3
    #
    sselii
    #
    @8
    cn0
    c2
    @0
    ffvelrn
    sylancl
    adantr
    @25
    @30
    @3
    @25
    @31
    c3
    @8
    wcel
    @30
    @32
    c3
    3nn
    jm2.27dlem3
    #
    @8
    cn0
    c3
    @0
    ffvelrn
    sylancl
    adantr
    vb
    @1
    @5
    @4
    rmxdiophlem
    syl3anc
    pm5.32da
    @22
    @3
    @26
    wa
    #
    vb
    cn0
    wrex
    @28
    @21
    @38
    vb
    cn0
    @3
    @12
    @20
    anass
    rexbii
    @3
    @26
    vb
    cn0
    r19.42v
    bitr2i
    syl6bb
    rabbiia
    c3
    cn0
    wcel
    @21
    vb
    c4
    vc
    cv
    #
    cfv
    #
    wsbc
    va
    @39
    @8
    cres
    #
    wsbc
    #
    vc
    cn0
    c1
    c4
    cfz
    co
    #
    cmap
    co
    #
    crab
    #
    c4
    cdioph
    cfv
    #
    wcel
    @23
    @24
    wcel
    3nn0
    @45
    c1
    @39
    cfv
    #
    @2
    wcel
    #
    @40
    @47
    c2
    @39
    cfv
    #
    crmy
    co
    #
    wceq
    #
    wa
    #
    c3
    @39
    cfv
    #
    c2
    cexp
    co
    #
    @47
    c2
    cexp
    co
    #
    c1
    cmin
    co
    #
    @40
    c2
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    c1
    wceq
    #
    wa
    #
    vc
    @44
    crab
    #
    @46
    @42
    @61
    vc
    @44
    @21
    @61
    va
    vb
    @41
    @40
    @39
    @8
    vc
    vex
    resex
    c4
    @39
    fvex
    @0
    @41
    wceq
    #
    @10
    @40
    wceq
    #
    wa
    #
    @13
    @52
    @20
    @60
    @65
    @3
    @48
    @12
    @51
    @63
    @3
    @48
    wb
    @64
    @63
    @1
    @47
    @2
    c1
    c3
    va
    vc
    c1
    c1
    cfz
    co
    #
    @8
    c1
    c1
    c2
    c3
    df-2
    @34
    jm2.27dlem5
    c1
    1nn
    jm2.27dlem3
    #
    sselii
    jm2.27dlem1
    #
    eleq1d
    adantr
    @65
    @10
    @40
    @11
    @50
    @63
    @64
    simpr
    @63
    @11
    @50
    wceq
    @64
    @63
    @1
    @47
    @5
    @49
    crmy
    @68
    c2
    c3
    va
    vc
    @36
    jm2.27dlem1
    oveq12d
    adantr
    eqeq12d
    anbi12d
    @65
    @19
    @59
    c1
    @65
    @14
    @54
    @18
    @58
    cmin
    @63
    @14
    @54
    wceq
    @64
    @63
    @4
    @53
    c2
    cexp
    c3
    c3
    va
    vc
    @37
    jm2.27dlem1
    oveq1d
    adantr
    @63
    @64
    @16
    @56
    @17
    @57
    cmul
    @63
    @15
    @55
    c1
    cmin
    @63
    @1
    @47
    c2
    cexp
    @68
    oveq1d
    oveq1d
    @10
    @40
    c2
    cexp
    oveq1
    oveqan12d
    oveq12d
    eqeq1d
    anbi12d
    sbc2ie
    rabbii
    @52
    vc
    @44
    crab
    @46
    wcel
    #
    @60
    vc
    @44
    crab
    @46
    wcel
    #
    @62
    @46
    wcel
    c4
    cn0
    wcel
    #
    c1
    @10
    cfv
    #
    @2
    wcel
    #
    c3
    @10
    cfv
    #
    @72
    c2
    @10
    cfv
    #
    crmy
    co
    #
    wceq
    #
    wa
    #
    vb
    @9
    crab
    @24
    wcel
    @69
    4nn0
    vb
    rmydioph
    @78
    @52
    c4
    c1
    c2
    c4
    vb
    vc
    @72
    @47
    wceq
    #
    @75
    @49
    wceq
    #
    @74
    @40
    wceq
    #
    w3a
    #
    @73
    @48
    @77
    @51
    @82
    @72
    @47
    @2
    @79
    @80
    @81
    simp1
    #
    eleq1d
    @82
    @74
    @40
    @76
    @50
    @79
    @80
    @81
    simp3
    @82
    @72
    @47
    @75
    @49
    crmy
    @83
    @79
    @80
    @81
    simp2
    oveq12d
    eqeq12d
    anbi12d
    @66
    @43
    c1
    c1
    c2
    c4
    df-2
    c2
    c3
    c4
    df-3
    c3
    c4
    c4
    df-4
    @43
    ssid
    jm2.27dlem5
    #
    jm2.27dlem5
    #
    jm2.27dlem5
    @67
    sselii
    #
    @33
    @43
    c2
    @85
    @35
    sselii
    c4
    4nn
    jm2.27dlem3
    #
    rabren3dioph
    mp2an
    @71
    vc
    cz
    @43
    cmap
    co
    #
    @59
    cmpt
    @43
    cmzp
    cfv
    #
    wcel
    #
    vc
    @88
    c1
    cmpt
    @89
    wcel
    #
    @70
    4nn0
    vc
    @88
    @54
    cmpt
    @89
    wcel
    #
    vc
    @88
    @58
    cmpt
    @89
    wcel
    #
    @90
    vc
    @88
    @53
    cmpt
    @89
    wcel
    #
    c2
    cn0
    wcel
    #
    @92
    @43
    cvv
    wcel
    #
    c3
    @43
    wcel
    @94
    c1
    c4
    cfz
    ovex
    #
    @8
    @43
    c3
    @84
    @37
    sselii
    vc
    @43
    c3
    mzpproj
    mp2an
    2nn0
    vc
    @53
    c2
    @43
    mzpexpmpt
    mp2an
    vc
    @88
    @56
    cmpt
    @89
    wcel
    #
    vc
    @88
    @57
    cmpt
    @89
    wcel
    #
    @93
    vc
    @88
    @55
    cmpt
    @89
    wcel
    #
    @91
    @98
    vc
    @88
    @47
    cmpt
    @89
    wcel
    #
    @95
    @100
    @96
    c1
    @43
    wcel
    @101
    @97
    @86
    vc
    @43
    c1
    mzpproj
    mp2an
    2nn0
    vc
    @47
    c2
    @43
    mzpexpmpt
    mp2an
    @96
    c1
    cz
    wcel
    @91
    @97
    1z
    vc
    c1
    @43
    mzpconstmpt
    mp2an
    #
    vc
    @55
    c1
    @43
    mzpsubmpt
    mp2an
    vc
    @88
    @40
    cmpt
    @89
    wcel
    #
    @95
    @99
    @96
    c4
    @43
    wcel
    @103
    @97
    @87
    vc
    @43
    c4
    mzpproj
    mp2an
    2nn0
    vc
    @40
    c2
    @43
    mzpexpmpt
    mp2an
    vc
    @56
    @57
    @43
    mzpmulmpt
    mp2an
    vc
    @54
    @58
    @43
    mzpsubmpt
    mp2an
    @102
    vc
    @59
    c1
    c4
    eqrabdioph
    mp3an
    @52
    @60
    vc
    c4
    anrabdioph
    mp2an
    eqeltri
    @21
    vb
    va
    vc
    c4
    c3
    df-4
    rexfrabdioph
    mp2an
    eqeltri
end
