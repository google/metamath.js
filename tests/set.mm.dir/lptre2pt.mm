include "cv.mm"
include "clp.mm"
include "cfv.mm"
include "wcel.mm"
include "wne.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wrex.mm"
include "c0.mm"
include "wex.mm"
include "n0.mm"
include "sylib.mm"
include "c2.mm"
include "cdiv.mm"
include "caddc.mm"
include "cioo.mm"
include "csn.mm"
include "cdif.mm"
include "cin.mm"
include "wi.mm"
include "cxr.mm"
include "wral.mm"
include "simpr.mm"
include "cr.mm"
include "wss.mm"
include "adantr.mm"
include "ctop.mm"
include "crn.mm"
include "ctg.mm"
include "retop.mm"
include "eqeltri.mm"
include "cuni.mm"
include "uniretop.mm"
include "unieqi.mm"
include "eqtr4i.mm"
include "lpss.mm"
include "sylancr.mm"
include "sseldd.mm"
include "islptre.mm"
include "mpbid.mm"
include "rpred.mm"
include "rehalfcld.mm"
include "resubcld.mm"
include "rexrd.mm"
include "readdcld.mm"
include "crp.mm"
include "rphalfcld.mm"
include "ltsubrpd.mm"
include "ltaddrpd.mm"
include "eliood.mm"
include "wceq.mm"
include "oveq1.mm"
include "eleq2d.mm"
include "ineq1d.mm"
include "neeq1d.mm"
include "imbi12d.mm"
include "oveq2.mm"
include "rspc2v.mm"
include "syl2anc.mm"
include "mp2d.mm"
include "elinel2.mm"
include "eldifad.mm"
include "adantl.mm"
include "elinel1.mm"
include "wn.mm"
include "eldifbd.mm"
include "eldifd.mm"
include "jca.mm"
include "ex.mm"
include "eximdv.mm"
include "mpd.mm"
include "df-rex.mm"
include "sylibr.mm"
include "eldifi.mm"
include "elioore.mm"
include "syl.mm"
include "eldifsni.mm"
include "w3a.mm"
include "resubcl.mm"
include "recnd.mm"
include "abscld.mm"
include "3adant3.mm"
include "simp2.mm"
include "cc.mm"
include "recn.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "subne0d.mm"
include "absrpcld.mm"
include "syl3anc.mm"
include "subcld.mm"
include "cc0.mm"
include "cle.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3.mm"
include "subge0d.mm"
include "abssubge0d.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "eleqtrd.mm"
include "3ad2ant3.mm"
include "simpl.mm"
include "ancoms.mm"
include "iooltub.mm"
include "pncan3d.mm"
include "breqtrd.mm"
include "gtned.mm"
include "cneg.mm"
include "0red.mm"
include "ltnled.mm"
include "mpbird.mm"
include "ltled.mm"
include "absnidd.mm"
include "negsubdi2d.mm"
include "eqtrd.mm"
include "3adantl3.mm"
include "nncand.mm"
include "oveq1d.mm"
include "ioogtlb.mm"
include "ltned.mm"
include "pm2.61dan.mm"
include "adantll.mm"
include "adantllr.mm"
include "adantlr.mm"
include "ad3antrrr.mm"
include "abs3difd.mm"
include "ad2antrr.mm"
include "simpll.mm"
include "sylan2.mm"
include "abssubd.mm"
include "3adant1.mm"
include "iooabslt.mm"
include "eqbrtrd.mm"
include "3jca.mm"
include "3ad2antl2.mm"
include "lttrd.mm"
include "syl2an.mm"
include "ltleaddd.mm"
include "2halvesd.mm"
include "lelttrd.mm"
include "jca32.mm"
include "reximdv.mm"
include "exlimddv.mm"

theorem lptre2pt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cE: class E
  let cJ: class J
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  assume lptre2pt.j: |- J = ( topGen ` ran (,) )
  assume lptre2pt.a: |- ( ph -> A C_ RR )
  assume lptre2pt.x: |- ( ph -> ( ( limPt ` J ) ` A ) =/= (/) )
  assume lptre2pt.e: |- ( ph -> E e. RR+ )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint E x
  disjoint E y
  disjoint J x
  disjoint J y
  disjoint ph x
  disjoint ph y
  disjoint A a
  disjoint A b
  disjoint A w
  disjoint a b
  disjoint a w
  disjoint a x
  disjoint b w
  disjoint b x
  disjoint w x
  disjoint w y
  disjoint E a
  disjoint E b
  disjoint E w
  disjoint J a
  disjoint J b
  disjoint J w
  disjoint a ph
  disjoint b ph
  disjoint ph w
  assert |- ( ph -> E. x e. A E. y e. A ( x =/= y /\ ( abs ` ( x - y ) ) < E ) )

  proof
    wph
    vw
    cv
    #
    cA
    cJ
    clp
    cfv
    cfv
    #
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    wne
    #
    @3
    @4
    cmin
    co
    #
    cabs
    cfv
    #
    cE
    clt
    wbr
    #
    wa
    #
    vy
    cA
    wrex
    #
    vx
    cA
    wrex
    #
    vw
    wph
    @1
    c0
    wne
    @2
    vw
    wex
    lptre2pt.x
    vw
    @1
    n0
    sylib
    wph
    @2
    wa
    #
    @3
    @0
    cE
    c2
    cdiv
    co
    #
    cmin
    co
    #
    @0
    @13
    caddc
    co
    #
    cioo
    co
    #
    @0
    csn
    #
    cdif
    wcel
    #
    vx
    cA
    wrex
    #
    @11
    @12
    @3
    cA
    wcel
    #
    @18
    wa
    #
    vx
    wex
    #
    @19
    @12
    @3
    @16
    cA
    @17
    cdif
    #
    cin
    #
    wcel
    #
    vx
    wex
    #
    @22
    @12
    @24
    c0
    wne
    #
    @26
    @12
    @0
    va
    cv
    #
    vb
    cv
    #
    cioo
    co
    #
    wcel
    #
    @30
    @23
    cin
    #
    c0
    wne
    #
    wi
    #
    vb
    cxr
    wral
    va
    cxr
    wral
    #
    @0
    @16
    wcel
    #
    @27
    @12
    @2
    @35
    wph
    @2
    simpr
    #
    @12
    cA
    @0
    cJ
    va
    vb
    lptre2pt.j
    wph
    cA
    cr
    wss
    #
    @2
    lptre2pt.a
    adantr
    #
    @12
    @1
    cr
    @0
    @12
    cJ
    ctop
    wcel
    @38
    @1
    cr
    wss
    cJ
    cioo
    crn
    ctg
    cfv
    #
    ctop
    lptre2pt.j
    retop
    eqeltri
    @39
    cA
    cJ
    cr
    cr
    @40
    cuni
    cJ
    cuni
    uniretop
    cJ
    @40
    lptre2pt.j
    unieqi
    eqtr4i
    lpss
    sylancr
    @37
    sseldd
    #
    islptre
    mpbid
    #
    @12
    @14
    @15
    @0
    @12
    @14
    @12
    @0
    @13
    @41
    @12
    cE
    wph
    cE
    cr
    wcel
    #
    @2
    wph
    cE
    lptre2pt.e
    rpred
    #
    adantr
    rehalfcld
    #
    resubcld
    rexrd
    #
    @12
    @15
    @12
    @0
    @13
    @41
    @45
    readdcld
    rexrd
    #
    @41
    @12
    @0
    @13
    @41
    wph
    @13
    crp
    wcel
    @2
    wph
    cE
    lptre2pt.e
    rphalfcld
    adantr
    #
    ltsubrpd
    @12
    @0
    @13
    @41
    @48
    ltaddrpd
    eliood
    @12
    @14
    cxr
    wcel
    @15
    cxr
    wcel
    @35
    @36
    @27
    wi
    #
    wi
    @46
    @47
    @34
    @49
    @0
    @14
    @29
    cioo
    co
    #
    wcel
    #
    @50
    @23
    cin
    #
    c0
    wne
    #
    wi
    va
    vb
    @14
    @15
    cxr
    cxr
    @28
    @14
    wceq
    #
    @31
    @51
    @33
    @53
    @54
    @30
    @50
    @0
    @28
    @14
    @29
    cioo
    oveq1
    #
    eleq2d
    @54
    @32
    @52
    c0
    @54
    @30
    @50
    @23
    @55
    ineq1d
    neeq1d
    imbi12d
    @29
    @15
    wceq
    #
    @51
    @36
    @53
    @27
    @56
    @50
    @16
    @0
    @29
    @15
    @14
    cioo
    oveq2
    #
    eleq2d
    @56
    @52
    @24
    c0
    @56
    @50
    @16
    @23
    @57
    ineq1d
    neeq1d
    imbi12d
    rspc2v
    syl2anc
    mp2d
    vx
    @24
    n0
    sylib
    @12
    @25
    @21
    vx
    @12
    @25
    @21
    @12
    @25
    wa
    #
    @20
    @18
    @25
    @20
    @12
    @25
    @3
    cA
    @17
    @3
    @16
    @23
    elinel2
    #
    eldifad
    adantl
    @58
    @3
    @16
    @17
    @25
    @3
    @16
    wcel
    #
    @12
    @3
    @16
    @23
    elinel1
    adantl
    @25
    @3
    @17
    wcel
    wn
    @12
    @25
    @3
    cA
    @17
    @59
    eldifbd
    adantl
    eldifd
    jca
    ex
    eximdv
    mpd
    @18
    vx
    cA
    df-rex
    sylibr
    @12
    @18
    @10
    vx
    cA
    @12
    @18
    @10
    @12
    @18
    wa
    #
    @4
    cA
    wcel
    #
    @9
    wa
    #
    vy
    wex
    #
    @10
    @61
    @4
    @0
    @3
    @0
    cmin
    co
    #
    cabs
    cfv
    #
    cmin
    co
    #
    @0
    @66
    caddc
    co
    #
    cioo
    co
    #
    @23
    cin
    #
    wcel
    #
    vy
    wex
    #
    @64
    @61
    @70
    c0
    wne
    #
    @72
    @61
    @35
    @0
    @69
    wcel
    #
    @73
    @12
    @35
    @18
    @42
    adantr
    @61
    @3
    cr
    wcel
    #
    @0
    cr
    wcel
    #
    @3
    @0
    wne
    #
    @74
    @18
    @75
    @12
    @18
    @60
    @75
    @3
    @16
    @17
    eldifi
    #
    @3
    @14
    @15
    elioore
    #
    syl
    #
    adantl
    #
    @12
    @76
    @18
    @41
    adantr
    #
    @18
    @77
    @12
    @3
    @16
    @0
    eldifsni
    adantl
    @75
    @76
    @77
    w3a
    #
    @67
    @68
    @0
    @75
    @76
    @67
    cxr
    wcel
    #
    @77
    @75
    @76
    wa
    #
    @67
    @85
    @0
    @66
    @75
    @76
    simpr
    #
    @85
    @65
    @85
    @65
    @3
    @0
    resubcl
    #
    recnd
    #
    abscld
    #
    resubcld
    rexrd
    3adant3
    @75
    @76
    @68
    cxr
    wcel
    #
    @77
    @85
    @68
    @85
    @0
    @66
    @86
    @89
    readdcld
    rexrd
    3adant3
    @75
    @76
    @77
    simp2
    #
    @83
    @0
    @66
    @91
    @83
    @65
    @75
    @76
    @65
    cc
    wcel
    @77
    @88
    3adant3
    @83
    @3
    @0
    @75
    @76
    @3
    cc
    wcel
    #
    @77
    @3
    recn
    #
    3ad2ant1
    @83
    @0
    @91
    recnd
    @75
    @76
    @77
    simp3
    subne0d
    absrpcld
    #
    ltsubrpd
    @83
    @0
    @66
    @91
    @94
    ltaddrpd
    eliood
    syl3anc
    @61
    @84
    @90
    @35
    @74
    @73
    wi
    #
    wi
    @61
    @67
    @61
    @0
    @66
    @82
    @61
    @65
    @61
    @3
    @0
    @18
    @92
    @12
    @18
    @3
    @80
    recnd
    adantl
    @61
    @0
    @82
    recnd
    #
    subcld
    abscld
    #
    resubcld
    rexrd
    @61
    @68
    @61
    @0
    @66
    @82
    @97
    readdcld
    rexrd
    @34
    @95
    @0
    @67
    @29
    cioo
    co
    #
    wcel
    #
    @98
    @23
    cin
    #
    c0
    wne
    #
    wi
    va
    vb
    @67
    @68
    cxr
    cxr
    @28
    @67
    wceq
    #
    @31
    @99
    @33
    @101
    @102
    @30
    @98
    @0
    @28
    @67
    @29
    cioo
    oveq1
    #
    eleq2d
    @102
    @32
    @100
    c0
    @102
    @30
    @98
    @23
    @103
    ineq1d
    neeq1d
    imbi12d
    @29
    @68
    wceq
    #
    @99
    @74
    @101
    @73
    @104
    @98
    @69
    @0
    @29
    @68
    @67
    cioo
    oveq2
    #
    eleq2d
    @104
    @100
    @70
    c0
    @104
    @98
    @69
    @23
    @105
    ineq1d
    neeq1d
    imbi12d
    rspc2v
    syl2anc
    mp2d
    vy
    @70
    n0
    sylib
    @61
    @71
    @63
    vy
    @61
    @71
    @63
    @61
    @71
    wa
    #
    @62
    @5
    @8
    @71
    @62
    @61
    @71
    @4
    cA
    @17
    @4
    @69
    @23
    elinel2
    eldifad
    adantl
    @106
    @76
    @75
    @4
    @69
    wcel
    #
    @5
    @61
    @76
    @71
    @82
    adantr
    @61
    @75
    @71
    @81
    adantr
    #
    @71
    @107
    @61
    @4
    @69
    @23
    elinel1
    #
    adantl
    @76
    @75
    @107
    w3a
    #
    cc0
    @65
    cle
    wbr
    #
    @5
    @110
    @111
    wa
    #
    @76
    @75
    @4
    @0
    @65
    cmin
    co
    #
    @0
    @65
    caddc
    co
    #
    cioo
    co
    #
    wcel
    #
    @5
    @76
    @75
    @107
    @111
    simpl1
    #
    @76
    @75
    @107
    @111
    simpl2
    #
    @112
    @4
    @69
    @115
    @76
    @75
    @107
    @111
    simpl3
    @112
    @67
    @113
    @68
    @114
    cioo
    @112
    @66
    @65
    @0
    cmin
    @112
    @0
    @3
    @117
    @118
    @112
    @111
    @0
    @3
    cle
    wbr
    @110
    @111
    simpr
    @112
    @3
    @0
    @118
    @117
    subge0d
    mpbid
    abssubge0d
    #
    oveq2d
    @112
    @66
    @65
    @0
    caddc
    @119
    oveq2d
    oveq12d
    eleqtrd
    @76
    @75
    @116
    w3a
    #
    @4
    @3
    @116
    @76
    @4
    cr
    wcel
    #
    @75
    @4
    @113
    @114
    elioore
    3ad2ant3
    @120
    @4
    @114
    @3
    clt
    @120
    @113
    cxr
    wcel
    #
    @114
    cxr
    wcel
    #
    @116
    @4
    @114
    clt
    wbr
    @76
    @75
    @122
    @116
    @76
    @75
    wa
    #
    @113
    @124
    @0
    @65
    @76
    @75
    simpl
    #
    @75
    @76
    @65
    cr
    wcel
    #
    @87
    ancoms
    #
    resubcld
    rexrd
    3adant3
    @76
    @75
    @123
    @116
    @124
    @114
    @124
    @0
    @65
    @125
    @127
    readdcld
    rexrd
    3adant3
    @76
    @75
    @116
    simp3
    @113
    @114
    @4
    iooltub
    syl3anc
    @76
    @75
    @114
    @3
    wceq
    @116
    @124
    @0
    @3
    @124
    @0
    @125
    recnd
    #
    @75
    @92
    @76
    @93
    adantl
    #
    pncan3d
    3adant3
    breqtrd
    gtned
    syl3anc
    @110
    @111
    wn
    #
    wa
    #
    @76
    @75
    @4
    @0
    @0
    @3
    cmin
    co
    #
    cmin
    co
    #
    @0
    @132
    caddc
    co
    #
    cioo
    co
    #
    wcel
    #
    @5
    @76
    @75
    @107
    @130
    simpl1
    @76
    @75
    @107
    @130
    simpl2
    @131
    @4
    @69
    @135
    @76
    @75
    @107
    @130
    simpl3
    @76
    @75
    @130
    @69
    @135
    wceq
    @107
    @124
    @130
    wa
    #
    @67
    @133
    @68
    @134
    cioo
    @137
    @66
    @132
    @0
    cmin
    @137
    @66
    @65
    cneg
    @132
    @137
    @65
    @124
    @126
    @130
    @127
    adantr
    #
    @137
    @65
    cc0
    @138
    @137
    0red
    #
    @137
    @65
    cc0
    clt
    wbr
    @130
    @124
    @130
    simpr
    @137
    @65
    cc0
    @138
    @139
    ltnled
    mpbird
    ltled
    absnidd
    @137
    @3
    @0
    @124
    @92
    @130
    @129
    adantr
    @124
    @0
    cc
    wcel
    #
    @130
    @128
    adantr
    negsubdi2d
    eqtrd
    #
    oveq2d
    @137
    @66
    @132
    @0
    caddc
    @141
    oveq2d
    oveq12d
    3adantl3
    eleqtrd
    @76
    @75
    @136
    w3a
    #
    @3
    @4
    @76
    @75
    @136
    simp2
    #
    @142
    @3
    cxr
    wcel
    @134
    cxr
    wcel
    #
    @4
    @3
    @134
    cioo
    co
    #
    wcel
    @3
    @4
    clt
    wbr
    @142
    @3
    @143
    rexrd
    @76
    @75
    @144
    @136
    @124
    @134
    @124
    @0
    @132
    @125
    @0
    @3
    resubcl
    readdcld
    rexrd
    3adant3
    @142
    @4
    @135
    @145
    @76
    @75
    @136
    simp3
    @76
    @75
    @135
    @145
    wceq
    @136
    @124
    @133
    @3
    @134
    cioo
    @124
    @0
    @3
    @128
    @129
    nncand
    oveq1d
    3adant3
    eleqtrd
    @3
    @134
    @4
    ioogtlb
    syl3anc
    ltned
    syl3anc
    pm2.61dan
    syl3anc
    @106
    @7
    @66
    @0
    @4
    cmin
    co
    #
    cabs
    cfv
    #
    caddc
    co
    #
    cE
    wph
    @18
    @71
    @7
    cr
    wcel
    @2
    wph
    @18
    wa
    @71
    wa
    @6
    @18
    @71
    @6
    cc
    wcel
    wph
    @18
    @71
    wa
    #
    @6
    @149
    @3
    @4
    @18
    @75
    @71
    @80
    adantr
    @71
    @121
    @18
    @71
    @107
    @121
    @109
    @4
    @67
    @68
    elioore
    #
    syl
    #
    adantl
    resubcld
    recnd
    adantll
    abscld
    adantllr
    @106
    @66
    @147
    @61
    @66
    cr
    wcel
    #
    @71
    @97
    adantr
    #
    @12
    @71
    @147
    cr
    wcel
    #
    @18
    @12
    @71
    wa
    #
    @146
    @155
    @146
    @155
    @0
    @4
    @12
    @76
    @71
    @41
    adantr
    @71
    @121
    @12
    @151
    adantl
    resubcld
    recnd
    abscld
    adantlr
    #
    readdcld
    wph
    @43
    @2
    @18
    @71
    @44
    ad3antrrr
    @106
    @3
    @4
    @0
    @106
    @3
    @108
    recnd
    @71
    @4
    cc
    wcel
    @61
    @71
    @4
    @151
    recnd
    adantl
    @61
    @140
    @71
    @96
    adantr
    abs3difd
    @106
    @148
    @13
    @13
    caddc
    co
    #
    cE
    clt
    @106
    @66
    @147
    @13
    @13
    @153
    @156
    @12
    @13
    cr
    wcel
    #
    @18
    @71
    @45
    ad2antrr
    #
    @159
    @61
    @66
    @13
    clt
    wbr
    #
    @71
    @61
    wph
    @76
    @60
    @160
    wph
    @2
    @18
    simpll
    #
    @82
    @18
    @60
    @12
    @78
    adantl
    #
    wph
    @76
    @60
    w3a
    #
    @66
    @132
    cabs
    cfv
    #
    @13
    clt
    @76
    @60
    @66
    @164
    wceq
    wph
    @76
    @60
    wa
    #
    @3
    @0
    @60
    @76
    @75
    @92
    @79
    @129
    sylan2
    #
    @60
    @76
    @75
    @140
    @79
    @128
    sylan2
    #
    abssubd
    3adant1
    @163
    @0
    @13
    @3
    wph
    @76
    @60
    simp2
    wph
    @76
    @158
    @60
    wph
    cE
    @44
    rehalfcld
    3ad2ant1
    #
    wph
    @76
    @60
    simp3
    iooabslt
    eqbrtrd
    #
    syl3anc
    adantr
    @61
    @163
    @107
    @147
    @13
    cle
    wbr
    @71
    @61
    wph
    @76
    @60
    @161
    @82
    @162
    3jca
    @109
    @163
    @107
    wa
    #
    @147
    @13
    @76
    wph
    @107
    @154
    @60
    @76
    @107
    wa
    #
    @146
    @171
    @146
    @171
    @0
    @4
    @76
    @107
    simpl
    @107
    @121
    @76
    @150
    adantl
    resubcld
    recnd
    abscld
    3ad2antl2
    #
    @163
    @158
    @107
    @168
    adantr
    #
    @170
    @147
    @66
    @13
    @172
    @163
    @152
    @107
    @76
    @60
    @152
    wph
    @165
    @65
    @165
    @3
    @0
    @166
    @167
    subcld
    abscld
    3adant1
    adantr
    #
    @173
    @170
    @0
    @66
    @4
    wph
    @76
    @60
    @107
    simpl2
    @174
    @163
    @107
    simpr
    iooabslt
    @163
    @160
    @107
    @169
    adantr
    lttrd
    ltled
    syl2an
    ltleaddd
    wph
    @157
    cE
    wceq
    @2
    @18
    @71
    wph
    cE
    wph
    cE
    @44
    recnd
    2halvesd
    ad3antrrr
    breqtrd
    lelttrd
    jca32
    ex
    eximdv
    mpd
    @9
    vy
    cA
    df-rex
    sylibr
    ex
    reximdv
    mpd
    exlimddv
end
