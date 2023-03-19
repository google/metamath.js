include "crp.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cv.mm"
include "cdiv.mm"
include "casin.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "csqrt.mm"
include "cmul.mm"
include "caddc.mm"
include "cneg.mm"
include "cicc.mm"
include "cc.mm"
include "wss.mm"
include "cmpt.mm"
include "ccncf.mm"
include "rpcn.mm"
include "sqcld.mm"
include "cr.mm"
include "rpre.mm"
include "renegcld.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "ssid.mm"
include "a1i.mm"
include "cncfmptc.mm"
include "syl3anc.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "eqid.mm"
include "ctx.mm"
include "ccn.mm"
include "addcn.mm"
include "ci.mm"
include "clog.mm"
include "cmnf.mm"
include "cc0.mm"
include "cioc.mm"
include "cdif.mm"
include "cres.mm"
include "wa.mm"
include "wceq.mm"
include "sselda.mm"
include "adantr.mm"
include "wne.mm"
include "rpne0.mm"
include "divcld.mm"
include "asinval.mm"
include "syl.mm"
include "ax-icn.mm"
include "mulcld.mm"
include "1cnd.mm"
include "subcld.mm"
include "sqrtcld.mm"
include "addcld.mm"
include "cle.mm"
include "wbr.mm"
include "wn.mm"
include "wo.mm"
include "w3a.mm"
include "clt.mm"
include "0lt1.mm"
include "simp3.mm"
include "oveq1d.mm"
include "div0d.mm"
include "3ad2ant1.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "it0e0.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "sq0.mm"
include "oveq2i.mm"
include "1m0e1.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "sqrt1.mm"
include "oveq12d.mm"
include "0p1e1.mm"
include "breq2d.mm"
include "0red.mm"
include "1red.mm"
include "eqeltrd.mm"
include "ltnled.mm"
include "bitr3d.mm"
include "mpbii.mm"
include "3expa.mm"
include "olcd.mm"
include "inelr.mm"
include "wi.mm"
include "pncand.mm"
include "3adant3.mm"
include "mulassd.mm"
include "divcan6d.mm"
include "mulid1d.mm"
include "3eqtrrd.mm"
include "simpr.mm"
include "redivcld.mm"
include "resqcld.mm"
include "resubcld.mm"
include "wb.mm"
include "elicc2.mm"
include "subge0d.mm"
include "recn.mm"
include "adantl.mm"
include "sqdivd.mm"
include "breq1d.mm"
include "resqcl.mm"
include "rpgt0.mm"
include "0le0.mm"
include "rpge0.mm"
include "lt2sqd.mm"
include "bitrd.mm"
include "mpbid.mm"
include "elrpd.mm"
include "ledivmuld.mm"
include "cabs.mm"
include "absresq.mm"
include "eqcomd.mm"
include "breqan12rd.mm"
include "abscld.mm"
include "absge0d.mm"
include "le2sqd.mm"
include "absled.mm"
include "3bitr2d.mm"
include "3bitrrd.mm"
include "biimpd.mm"
include "exp4b.mm"
include "3impd.mm"
include "sylbid.mm"
include "imp.mm"
include "resqrtcld.mm"
include "remulcld.mm"
include "ex.mm"
include "mtoi.mm"
include "orcd.mm"
include "pm2.61dane.mm"
include "ianor.mm"
include "sylibr.mm"
include "cxr.mm"
include "mnfxr.mm"
include "0re.mm"
include "elioc2.mm"
include "mp2an.mm"
include "3simpb.mm"
include "sylbi.mm"
include "nsyl.mm"
include "eldifd.mm"
include "fvres.mm"
include "eqtr4d.mm"
include "mpteq2dva.mm"
include "negicn.mm"
include "crest.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "resttopon.mm"
include "wf.mm"
include "fmptd.mm"
include "difssd.mm"
include "divrec2d.mm"
include "reccld.mm"
include "cncfmptid.mm"
include "mulcncf.mm"
include "divcan3d.mm"
include "sqge0d.mm"
include "sqrtmuld.mm"
include "subdid.mm"
include "sqne0.mm"
include "mpbird.mm"
include "divcan2d.mm"
include "sqrtsqd.mm"
include "3eqtr3rd.mm"
include "3eqtr3d.mm"
include "areacirclem2.mm"
include "cncfmpt2f.mm"
include "cncffvrn.mm"
include "cncfcn.mm"
include "eleqtrd.mm"
include "logcn.mm"
include "difss.mm"
include "eleqtri.mm"
include "cnmpt11f.mm"
include "eleqtrrd.mm"
include "divrecd.mm"
include "3eqtr2d.mm"

theorem areacirclem4
  let vt: setvar t
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let vv: setvar v
  let cS: class S

  disjoint R t
  disjoint x y
  disjoint t x
  disjoint u x
  disjoint v x
  disjoint R x
  disjoint t y
  disjoint u y
  disjoint v y
  disjoint R y
  disjoint t u
  disjoint t v
  disjoint u v
  disjoint R u
  disjoint R v
  disjoint S t
  disjoint S u
  disjoint S v
  assert |- ( R e. RR+ -> ( t e. ( -u R [,] R ) |-> ( ( R ^ 2 ) x. ( ( arcsin ` ( t / R ) ) + ( ( t / R ) x. ( sqrt ` ( 1 - ( ( t / R ) ^ 2 ) ) ) ) ) ) ) e. ( ( -u R [,] R ) -cn-> CC ) )

  proof
    cR
    crp
    wcel
    #
    vt
    cR
    c2
    cexp
    co
    #
    vt
    cv
    #
    cR
    cdiv
    co
    #
    casin
    cfv
    #
    @3
    c1
    @3
    c2
    cexp
    co
    #
    cmin
    co
    #
    csqrt
    cfv
    #
    cmul
    co
    #
    caddc
    co
    cR
    cneg
    #
    cR
    cicc
    co
    #
    @0
    @1
    cc
    wcel
    #
    @10
    cc
    wss
    #
    cc
    cc
    wss
    #
    vt
    @10
    @1
    cmpt
    @10
    cc
    ccncf
    co
    #
    wcel
    @0
    cR
    cR
    rpcn
    #
    sqcld
    #
    @0
    @10
    cr
    cc
    @0
    @9
    cr
    wcel
    #
    cR
    cr
    wcel
    #
    @10
    cr
    wss
    @0
    cR
    cR
    rpre
    #
    renegcld
    #
    @19
    @9
    cR
    iccssre
    syl2anc
    #
    ax-resscn
    syl6ss
    #
    @13
    @0
    cc
    ssid
    #
    a1i
    #
    vt
    @1
    @10
    cc
    cncfmptc
    syl3anc
    @0
    vt
    @4
    @8
    caddc
    ccnfld
    ctopn
    cfv
    #
    @10
    @25
    eqid
    #
    caddc
    @25
    @25
    ctx
    co
    @25
    ccn
    co
    wcel
    @0
    @25
    @26
    addcn
    a1i
    #
    @0
    vt
    @10
    @4
    cmpt
    vt
    @10
    ci
    cneg
    #
    ci
    @3
    cmul
    co
    #
    @7
    caddc
    co
    #
    clog
    cc
    cmnf
    cc0
    cioc
    co
    #
    cdif
    #
    cres
    #
    cfv
    #
    cmul
    co
    #
    cmpt
    @14
    @0
    vt
    @10
    @4
    @35
    @0
    @2
    @10
    wcel
    #
    wa
    #
    @4
    @28
    @30
    clog
    cfv
    #
    cmul
    co
    #
    @35
    @37
    @3
    cc
    wcel
    #
    @4
    @39
    wceq
    @37
    @2
    cR
    @0
    @10
    cc
    @2
    @22
    sselda
    #
    @0
    cR
    cc
    wcel
    #
    @36
    @15
    adantr
    #
    @0
    cR
    cc0
    wne
    #
    @36
    cR
    rpne0
    #
    adantr
    #
    divcld
    #
    @3
    asinval
    syl
    @37
    @34
    @38
    @28
    cmul
    @37
    @30
    @32
    wcel
    @34
    @38
    wceq
    @37
    @30
    cc
    @31
    @37
    @29
    @7
    @37
    ci
    @3
    ci
    cc
    wcel
    #
    @37
    ax-icn
    a1i
    #
    @47
    mulcld
    #
    @37
    @6
    @37
    c1
    @5
    @37
    1cnd
    #
    @37
    @3
    @47
    sqcld
    #
    subcld
    sqrtcld
    #
    addcld
    @37
    @30
    cr
    wcel
    #
    @30
    cc0
    cle
    wbr
    #
    wa
    #
    @30
    @31
    wcel
    #
    @37
    @54
    wn
    #
    @55
    wn
    #
    wo
    #
    @56
    wn
    @37
    @60
    @2
    cc0
    @37
    @2
    cc0
    wceq
    #
    wa
    @59
    @58
    @0
    @36
    @61
    @59
    @0
    @36
    @61
    w3a
    #
    cc0
    c1
    clt
    wbr
    #
    @59
    0lt1
    @62
    cc0
    @30
    clt
    wbr
    @63
    @59
    @62
    @30
    c1
    cc0
    clt
    @62
    @30
    cc0
    c1
    caddc
    co
    c1
    @62
    @29
    cc0
    @7
    c1
    caddc
    @62
    @29
    ci
    cc0
    cmul
    co
    cc0
    @62
    @3
    cc0
    ci
    cmul
    @62
    @3
    cc0
    cR
    cdiv
    co
    #
    cc0
    @62
    @2
    cc0
    cR
    cdiv
    @0
    @36
    @61
    simp3
    oveq1d
    @0
    @36
    @64
    cc0
    wceq
    @61
    @0
    cR
    @15
    @45
    div0d
    3ad2ant1
    eqtrd
    #
    oveq2d
    it0e0
    syl6eq
    @62
    @7
    c1
    cc0
    c2
    cexp
    co
    #
    cmin
    co
    #
    csqrt
    cfv
    #
    c1
    @62
    @6
    @67
    csqrt
    @62
    @5
    @66
    c1
    cmin
    @62
    @3
    cc0
    c2
    cexp
    @65
    oveq1d
    oveq2d
    fveq2d
    @68
    c1
    csqrt
    cfv
    c1
    @67
    c1
    csqrt
    @67
    c1
    cc0
    cmin
    co
    c1
    @66
    cc0
    c1
    cmin
    sq0
    oveq2i
    1m0e1
    eqtri
    fveq2i
    sqrt1
    eqtri
    syl6eq
    oveq12d
    0p1e1
    syl6eq
    #
    breq2d
    @62
    cc0
    @30
    @62
    0red
    @62
    @30
    c1
    cr
    @69
    @62
    1red
    eqeltrd
    ltnled
    bitr3d
    mpbii
    3expa
    olcd
    @37
    @2
    cc0
    wne
    #
    wa
    #
    @58
    @59
    @71
    @54
    ci
    cr
    wcel
    #
    inelr
    @0
    @36
    @70
    @54
    @72
    wi
    @0
    @36
    @70
    w3a
    #
    @54
    @72
    @73
    @54
    wa
    #
    ci
    @30
    @7
    cmin
    co
    #
    cR
    @2
    cdiv
    co
    #
    cmul
    co
    #
    cr
    @73
    ci
    @77
    wceq
    @54
    @73
    @77
    ci
    @3
    @76
    cmul
    co
    #
    cmul
    co
    #
    ci
    c1
    cmul
    co
    ci
    @73
    @77
    @29
    @76
    cmul
    co
    @79
    @73
    @75
    @29
    @76
    cmul
    @0
    @36
    @75
    @29
    wceq
    @70
    @37
    @29
    @7
    @50
    @53
    pncand
    3adant3
    oveq1d
    @73
    ci
    @3
    @76
    @48
    @73
    ax-icn
    a1i
    #
    @0
    @36
    @40
    @70
    @47
    3adant3
    @73
    cR
    @2
    @0
    @36
    @42
    @70
    @15
    3ad2ant1
    #
    @0
    @36
    @2
    cc
    wcel
    #
    @70
    @41
    3adant3
    #
    @0
    @36
    @70
    simp3
    #
    divcld
    mulassd
    eqtrd
    @73
    @78
    c1
    ci
    cmul
    @73
    @2
    cR
    @83
    @81
    @84
    @0
    @36
    @44
    @70
    @45
    3ad2ant1
    divcan6d
    oveq2d
    @73
    ci
    @80
    mulid1d
    3eqtrrd
    adantr
    @74
    @75
    @76
    @74
    @30
    @7
    @73
    @54
    simpr
    @73
    @7
    cr
    wcel
    #
    @54
    @0
    @36
    @85
    @70
    @37
    @6
    @37
    c1
    @5
    @37
    1red
    @37
    @3
    @37
    @2
    cR
    @0
    @10
    cr
    @2
    @21
    sselda
    #
    @0
    @18
    @36
    @19
    adantr
    #
    @46
    redivcld
    resqcld
    resubcld
    #
    @0
    @36
    cc0
    @6
    cle
    wbr
    #
    @0
    @36
    @2
    cr
    wcel
    #
    @9
    @2
    cle
    wbr
    #
    @2
    cR
    cle
    wbr
    #
    w3a
    #
    @89
    @0
    @17
    @18
    @36
    @93
    wb
    @20
    @19
    @9
    cR
    @2
    elicc2
    syl2anc
    @0
    @90
    @91
    @92
    @89
    @0
    @90
    @91
    @92
    @89
    @0
    @90
    wa
    #
    @91
    @92
    wa
    #
    @89
    @94
    @89
    @5
    c1
    cle
    wbr
    @2
    c2
    cexp
    co
    #
    @1
    cdiv
    co
    #
    c1
    cle
    wbr
    #
    @95
    @94
    c1
    @5
    @94
    1red
    #
    @94
    @3
    @94
    @2
    cR
    @0
    @90
    simpr
    #
    @0
    @18
    @90
    @19
    adantr
    #
    @0
    @44
    @90
    @45
    adantr
    #
    redivcld
    resqcld
    subge0d
    @94
    @5
    @97
    c1
    cle
    @94
    @2
    cR
    @90
    @82
    @0
    @2
    recn
    #
    adantl
    @0
    @42
    @90
    @15
    adantr
    @102
    sqdivd
    breq1d
    @94
    @98
    @96
    @1
    c1
    cmul
    co
    #
    cle
    wbr
    #
    @95
    @94
    @96
    c1
    @1
    @90
    @96
    cr
    wcel
    @0
    @2
    resqcl
    adantl
    @99
    @0
    @1
    crp
    wcel
    @90
    @0
    @1
    @0
    cR
    @19
    resqcld
    #
    @0
    cc0
    cR
    clt
    wbr
    #
    cc0
    @1
    clt
    wbr
    #
    cR
    rpgt0
    @0
    @107
    @66
    @1
    clt
    wbr
    @108
    @0
    cc0
    cR
    @0
    0red
    @19
    cc0
    cc0
    cle
    wbr
    @0
    0le0
    a1i
    cR
    rpge0
    #
    lt2sqd
    @0
    @66
    cc0
    @1
    clt
    @66
    cc0
    wceq
    @0
    sq0
    a1i
    breq1d
    bitrd
    mpbid
    elrpd
    adantr
    ledivmuld
    @94
    @105
    @2
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    @1
    cle
    wbr
    @110
    cR
    cle
    wbr
    @95
    @90
    @0
    @96
    @111
    @104
    @1
    cle
    @90
    @111
    @96
    @2
    absresq
    eqcomd
    @0
    @1
    @16
    mulid1d
    breqan12rd
    @94
    @110
    cR
    @90
    @110
    cr
    wcel
    @0
    @90
    @2
    @103
    abscld
    adantl
    @101
    @90
    cc0
    @110
    cle
    wbr
    @0
    @90
    @2
    @103
    absge0d
    adantl
    @0
    cc0
    cR
    cle
    wbr
    #
    @90
    @109
    adantr
    le2sqd
    @94
    @2
    cR
    @100
    @101
    absled
    3bitr2d
    bitrd
    3bitrrd
    biimpd
    exp4b
    3impd
    sylbid
    imp
    #
    resqrtcld
    3adant3
    adantr
    resubcld
    @73
    @76
    cr
    wcel
    @54
    @73
    cR
    @2
    @0
    @36
    @18
    @70
    @19
    3ad2ant1
    @0
    @36
    @90
    @70
    @86
    3adant3
    @84
    redivcld
    adantr
    remulcld
    eqeltrd
    ex
    3expa
    mtoi
    orcd
    pm2.61dane
    @54
    @55
    ianor
    sylibr
    @57
    @54
    cmnf
    @30
    clt
    wbr
    #
    @55
    w3a
    #
    @56
    cmnf
    cxr
    wcel
    cc0
    cr
    wcel
    @57
    @115
    wb
    mnfxr
    0re
    cmnf
    cc0
    @30
    elioc2
    mp2an
    @54
    @114
    @55
    3simpb
    sylbi
    nsyl
    eldifd
    #
    @30
    @32
    clog
    fvres
    syl
    oveq2d
    eqtr4d
    mpteq2dva
    @0
    vt
    @28
    @34
    @10
    @0
    @28
    cc
    wcel
    #
    @12
    @13
    vt
    @10
    @28
    cmpt
    @14
    wcel
    @117
    @0
    negicn
    a1i
    @22
    @24
    vt
    @28
    @10
    cc
    cncfmptc
    syl3anc
    @0
    vt
    @10
    @34
    cmpt
    @25
    @10
    crest
    co
    #
    @25
    cc
    crest
    co
    #
    ccn
    co
    #
    @14
    @0
    vt
    @30
    @33
    @118
    @25
    @32
    crest
    co
    #
    @119
    @10
    @0
    @25
    cc
    ctopon
    cfv
    wcel
    #
    @12
    @118
    @10
    ctopon
    cfv
    wcel
    @122
    @0
    @25
    @26
    cnfldtopon
    a1i
    @22
    @10
    @25
    cc
    resttopon
    syl2anc
    @0
    vt
    @10
    @30
    cmpt
    #
    @10
    @32
    ccncf
    co
    #
    @118
    @121
    ccn
    co
    #
    @0
    @123
    @124
    wcel
    #
    @10
    @32
    @123
    wf
    #
    @0
    vt
    @10
    @30
    @32
    @123
    @116
    @123
    eqid
    fmptd
    @0
    @32
    cc
    wss
    #
    @123
    @14
    wcel
    @126
    @127
    wb
    @0
    cc
    @31
    difssd
    #
    @0
    vt
    @29
    @7
    caddc
    @25
    @10
    @26
    @27
    @0
    vt
    @10
    @29
    cmpt
    vt
    @10
    ci
    c1
    cR
    cdiv
    co
    #
    cmul
    co
    #
    @2
    cmul
    co
    #
    cmpt
    @14
    @0
    vt
    @10
    @29
    @132
    @37
    @29
    ci
    @130
    @2
    cmul
    co
    #
    cmul
    co
    @132
    @37
    @3
    @133
    ci
    cmul
    @37
    @2
    cR
    @41
    @43
    @46
    divrec2d
    oveq2d
    @37
    ci
    @130
    @2
    @49
    @0
    @130
    cc
    wcel
    #
    @36
    @0
    cR
    @15
    @45
    reccld
    #
    adantr
    #
    @41
    mulassd
    eqtr4d
    mpteq2dva
    @0
    vt
    @131
    @2
    @10
    @0
    @131
    cc
    wcel
    @12
    @13
    vt
    @10
    @131
    cmpt
    @14
    wcel
    @0
    ci
    @130
    @48
    @0
    ax-icn
    a1i
    @135
    mulcld
    @22
    @24
    vt
    @131
    @10
    cc
    cncfmptc
    syl3anc
    @0
    @12
    @13
    vt
    @10
    @2
    cmpt
    @14
    wcel
    @22
    @24
    vt
    @10
    cc
    cncfmptid
    syl2anc
    #
    mulcncf
    eqeltrd
    @0
    vt
    @10
    @7
    cmpt
    vt
    @10
    @130
    @1
    @96
    cmin
    co
    #
    csqrt
    cfv
    #
    cmul
    co
    #
    cmpt
    @14
    @0
    vt
    @10
    @7
    @140
    @37
    cR
    @7
    cmul
    co
    #
    cR
    cdiv
    co
    @130
    @141
    cmul
    co
    @7
    @140
    @37
    @141
    cR
    @37
    cR
    @7
    @43
    @53
    mulcld
    @43
    @46
    divrec2d
    @37
    @7
    cR
    @53
    @43
    @46
    divcan3d
    @37
    @141
    @139
    @130
    cmul
    @37
    @1
    @6
    cmul
    co
    #
    csqrt
    cfv
    @1
    csqrt
    cfv
    #
    @7
    cmul
    co
    @139
    @141
    @37
    @1
    @6
    @0
    @1
    cr
    wcel
    @36
    @106
    adantr
    @0
    cc0
    @1
    cle
    wbr
    @36
    @0
    cR
    @19
    sqge0d
    adantr
    @88
    @113
    sqrtmuld
    @37
    @142
    @138
    csqrt
    @37
    @142
    @104
    @1
    @5
    cmul
    co
    #
    cmin
    co
    @138
    @37
    @1
    c1
    @5
    @0
    @11
    @36
    @16
    adantr
    #
    @51
    @52
    subdid
    @37
    @104
    @1
    @144
    @96
    cmin
    @37
    @1
    @145
    mulid1d
    @37
    @144
    @1
    @97
    cmul
    co
    @96
    @37
    @5
    @97
    @1
    cmul
    @37
    @2
    cR
    @41
    @43
    @46
    sqdivd
    oveq2d
    @37
    @96
    @1
    @37
    @2
    @41
    sqcld
    #
    @145
    @0
    @1
    cc0
    wne
    #
    @36
    @0
    @147
    @44
    @45
    @0
    @42
    @147
    @44
    wb
    @15
    cR
    sqne0
    syl
    mpbird
    adantr
    divcan2d
    eqtrd
    oveq12d
    eqtrd
    fveq2d
    @37
    @143
    cR
    @7
    cmul
    @37
    cR
    @87
    @0
    @112
    @36
    @109
    adantr
    sqrtsqd
    oveq1d
    3eqtr3rd
    oveq2d
    3eqtr3d
    #
    mpteq2dva
    @0
    vt
    @130
    @139
    @10
    @0
    @134
    @12
    @13
    vt
    @10
    @130
    cmpt
    @14
    wcel
    @135
    @22
    @24
    vt
    @130
    @10
    cc
    cncfmptc
    syl3anc
    @0
    @18
    @112
    vt
    @10
    @139
    cmpt
    @14
    wcel
    @19
    @109
    vt
    cR
    areacirclem2
    syl2anc
    #
    mulcncf
    eqeltrd
    cncfmpt2f
    @10
    cc
    @32
    @123
    cncffvrn
    syl2anc
    mpbird
    @0
    @12
    @128
    @124
    @125
    wceq
    @22
    @129
    @10
    @32
    @25
    @118
    @121
    @26
    @118
    eqid
    #
    @121
    eqid
    #
    cncfcn
    syl2anc
    eleqtrd
    @33
    @121
    @119
    ccn
    co
    #
    wcel
    @0
    @33
    @32
    cc
    ccncf
    co
    #
    @152
    @32
    @32
    eqid
    logcn
    @128
    @13
    @153
    @152
    wceq
    cc
    @31
    difss
    @23
    @32
    cc
    @25
    @121
    @119
    @26
    @151
    @119
    eqid
    #
    cncfcn
    mp2an
    eleqtri
    a1i
    cnmpt11f
    @0
    @12
    @13
    @14
    @120
    wceq
    @22
    @24
    @10
    cc
    @25
    @118
    @119
    @26
    @150
    @154
    cncfcn
    syl2anc
    eleqtrrd
    mulcncf
    eqeltrd
    @0
    vt
    @10
    @8
    cmpt
    vt
    @10
    @2
    @130
    @130
    cmul
    co
    #
    cmul
    co
    #
    @139
    cmul
    co
    #
    cmpt
    @14
    @0
    vt
    @10
    @8
    @157
    @37
    @8
    @3
    @140
    cmul
    co
    @3
    @130
    cmul
    co
    #
    @139
    cmul
    co
    @157
    @37
    @7
    @140
    @3
    cmul
    @148
    oveq2d
    @37
    @3
    @130
    @139
    @47
    @136
    @37
    @138
    @37
    @1
    @96
    @145
    @146
    subcld
    sqrtcld
    mulassd
    @37
    @158
    @156
    @139
    cmul
    @37
    @158
    @2
    @130
    cmul
    co
    #
    @130
    cmul
    co
    @156
    @37
    @3
    @159
    @130
    cmul
    @37
    @2
    cR
    @41
    @43
    @46
    divrecd
    oveq1d
    @37
    @2
    @130
    @130
    @41
    @136
    @136
    mulassd
    eqtrd
    oveq1d
    3eqtr2d
    mpteq2dva
    @0
    vt
    @156
    @139
    @10
    @0
    vt
    @2
    @155
    @10
    @137
    @0
    @155
    cc
    wcel
    @12
    @13
    vt
    @10
    @155
    cmpt
    @14
    wcel
    @0
    @130
    @130
    @135
    @135
    mulcld
    @22
    @24
    vt
    @155
    @10
    cc
    cncfmptc
    syl3anc
    mulcncf
    @149
    mulcncf
    eqeltrd
    cncfmpt2f
    mulcncf
end
