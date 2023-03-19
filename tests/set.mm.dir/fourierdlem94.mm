include "cmnf.mm"
include "cioo.mm"
include "co.mm"
include "cres.mm"
include "climc.mm"
include "c0.mm"
include "wne.mm"
include "cpnf.mm"
include "cpi.mm"
include "cneg.mm"
include "cr.mm"
include "cv.mm"
include "cmin.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cmul.mm"
include "cmpt.mm"
include "caddc.mm"
include "c1.mm"
include "wcel.mm"
include "cio.mm"
include "pire.mm"
include "renegcli.mm"
include "a1i.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "negpilt0.mm"
include "pipos.mm"
include "0re.mm"
include "lttri.mm"
include "mp2an.mm"
include "c2.mm"
include "picn.mm"
include "2timesi.mm"
include "subnegi.mm"
include "3eqtr4i.mm"
include "wss.mm"
include "ssid.mm"
include "cz.mm"
include "w3a.mm"
include "simp2.mm"
include "zre.mm"
include "3ad2ant3.mm"
include "2re.mm"
include "remulcli.mm"
include "syl5eqel.mm"
include "adantr.mm"
include "3adant2.mm"
include "remulcld.mm"
include "readdcld.mm"
include "wceq.mm"
include "simp1.mm"
include "simp3.mm"
include "wa.mm"
include "cc.mm"
include "wf.mm"
include "ax-resscn.mm"
include "fssd.mm"
include "simplr.mm"
include "simpr.mm"
include "wi.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "chvarv.mm"
include "ad4ant14.mm"
include "fperiodmul.mm"
include "syl21anc.mm"
include "cfzo.mm"
include "cdv.mm"
include "cdm.mm"
include "ccncf.mm"
include "ioossre.mm"
include "fssresd.mm"
include "crn.mm"
include "ctg.mm"
include "cnt.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "eqid.mm"
include "tgioo2.mm"
include "dvres.mm"
include "syl22anc.mm"
include "dmeqd.mm"
include "ioontr.mm"
include "reseq2i.mm"
include "dmeqi.mm"
include "cncff.mm"
include "fdm.mm"
include "3syl.mm"
include "3eqtrd.mm"
include "dvcn.mm"
include "syl31anc.mm"
include "syl6ss.mm"
include "cfz.mm"
include "cmap.mm"
include "wral.mm"
include "cn.mm"
include "wb.mm"
include "fourierdlem2.mm"
include "syl.mm"
include "mpbid.mm"
include "simpld.mm"
include "elmapi.mm"
include "elfzofz.mm"
include "adantl.mm"
include "ffvelrnd.mm"
include "rexrd.mm"
include "fzofzp1.mm"
include "simprrd.mm"
include "r19.21bi.mm"
include "lptioo2cn.mm"
include "cabs.mm"
include "cle.mm"
include "wrex.mm"
include "dvbss.mm"
include "dvfre.mm"
include "syl2anc.mm"
include "simprd.mm"
include "simplld.mm"
include "simplrd.mm"
include "lptioo1cn.mm"
include "ellimciota.mm"
include "fperdvper.mm"
include "an32s.mm"
include "oveq12d.mm"
include "cbvmptv.mm"
include "fourierdlem71.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "syl6eq.mm"
include "fveq1d.mm"
include "fvres.mm"
include "sylan9eq.mm"
include "adantlr.mm"
include "ssdmres.mm"
include "sylibr.mm"
include "ad2antrr.mm"
include "sseldd.mm"
include "rspa.mm"
include "eqbrtrd.mm"
include "ex.mm"
include "ralrimi.mm"
include "reximdv.mm"
include "mpd.mm"
include "ioodvbdlimc2.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "id.mm"
include "fourierdlem49.mm"
include "cico.mm"
include "ioodvbdlimc1.mm"
include "biid.mm"
include "fourierdlem48.mm"
include "jca.mm"

theorem fourierdlem94
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cQ: class Q
  let cT: class T
  let vi: setvar i
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cX: class X
  let vp: setvar p
  let vj: setvar j
  let vk: setvar k
  let vw: setvar w
  let vy: setvar y
  let vt: setvar t
  let vz: setvar z
  assume fourierdlem94.f: |- ( ph -> F : RR --> RR )
  assume fourierdlem94.t: |- T = ( 2 x. _pi )
  assume fourierdlem94.per: |- ( ( ph /\ x e. RR ) -> ( F ` ( x + T ) ) = ( F ` x ) )
  assume fourierdlem94.x: |- ( ph -> X e. RR )
  assume fourierdlem94.p: |- P = ( n e. NN |-> { p e. ( RR ^m ( 0 ... n ) ) | ( ( ( p ` 0 ) = -u _pi /\ ( p ` n ) = _pi ) /\ A. i e. ( 0 ..^ n ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem94.m: |- ( ph -> M e. NN )
  assume fourierdlem94.q: |- ( ph -> Q e. ( P ` M ) )
  assume fourierdlem94.dvcn: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> ( ( RR _D F ) |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) e. ( ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) -cn-> CC ) )
  assume fourierdlem94.dvlb: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> ( ( ( RR _D F ) |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) limCC ( Q ` i ) ) =/= (/) )
  assume fourierdlem94.dvub: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> ( ( ( RR _D F ) |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) limCC ( Q ` ( i + 1 ) ) ) =/= (/) )

  disjoint F i
  disjoint F n
  disjoint F x
  disjoint i n
  disjoint i x
  disjoint n x
  disjoint M i
  disjoint M x
  disjoint M n
  disjoint M p
  disjoint i p
  disjoint n p
  disjoint Q i
  disjoint Q x
  disjoint Q n
  disjoint Q p
  disjoint T i
  disjoint T x
  disjoint T n
  disjoint T p
  disjoint X i
  disjoint X x
  disjoint X n
  disjoint X p
  disjoint i ph
  disjoint ph x
  disjoint n ph
  disjoint F j
  disjoint F k
  disjoint F w
  disjoint F y
  disjoint i j
  disjoint i k
  disjoint i w
  disjoint i y
  disjoint j k
  disjoint j n
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint k n
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint n w
  disjoint n y
  disjoint w x
  disjoint w y
  disjoint x y
  disjoint F t
  disjoint F z
  disjoint i t
  disjoint i z
  disjoint j t
  disjoint j z
  disjoint k t
  disjoint k z
  disjoint t w
  disjoint t y
  disjoint t z
  disjoint w z
  disjoint y z
  disjoint M j
  disjoint M k
  disjoint M t
  disjoint M w
  disjoint M y
  disjoint M z
  disjoint t x
  disjoint x z
  disjoint j p
  disjoint k p
  disjoint p w
  disjoint p y
  disjoint Q j
  disjoint Q k
  disjoint Q t
  disjoint Q w
  disjoint Q y
  disjoint Q z
  disjoint T j
  disjoint T k
  disjoint T t
  disjoint T w
  disjoint T y
  disjoint T z
  disjoint X j
  disjoint X k
  disjoint X t
  disjoint X w
  disjoint X y
  disjoint X z
  disjoint j ph
  disjoint k ph
  disjoint ph t
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint k x
  assert |- ( ph -> ( ( ( F |` ( -oo (,) X ) ) limCC X ) =/= (/) /\ ( ( F |` ( X (,) +oo ) ) limCC X ) =/= (/) ) )

  proof
    wph
    cF
    cmnf
    cX
    cioo
    co
    cres
    cX
    climc
    co
    c0
    wne
    cF
    cX
    cpnf
    cioo
    co
    cres
    cX
    climc
    co
    c0
    wne
    wph
    vx
    cpi
    cneg
    #
    cpi
    cr
    cP
    cQ
    cT
    vi
    vk
    vn
    vz
    cr
    vz
    cv
    #
    @1
    vy
    cr
    cpi
    vy
    cv
    #
    cmin
    co
    #
    cT
    cdiv
    co
    #
    cfl
    cfv
    #
    cT
    cmul
    co
    #
    cmpt
    #
    cfv
    #
    caddc
    co
    #
    cmpt
    #
    cF
    @2
    cF
    vi
    cv
    #
    cQ
    cfv
    #
    @11
    c1
    caddc
    co
    #
    cQ
    cfv
    #
    cioo
    co
    #
    cres
    #
    @14
    climc
    co
    wcel
    vy
    cio
    cM
    cX
    @7
    vp
    @0
    cr
    wcel
    wph
    cpi
    pire
    renegcli
    #
    a1i
    #
    cpi
    cr
    wcel
    wph
    pire
    a1i
    #
    @0
    cpi
    clt
    wbr
    #
    wph
    @0
    cc0
    clt
    wbr
    cc0
    cpi
    clt
    wbr
    @20
    negpilt0
    pipos
    @0
    cc0
    cpi
    @17
    0re
    pire
    lttri
    mp2an
    a1i
    #
    fourierdlem94.p
    c2
    cpi
    cmul
    co
    #
    cpi
    cpi
    caddc
    co
    cT
    cpi
    @0
    cmin
    co
    cpi
    picn
    2timesi
    fourierdlem94.t
    cpi
    cpi
    picn
    picn
    subnegi
    3eqtr4i
    #
    fourierdlem94.m
    fourierdlem94.q
    cr
    cr
    wss
    #
    wph
    cr
    ssid
    #
    a1i
    #
    fourierdlem94.f
    wph
    vx
    cv
    #
    cr
    wcel
    #
    vk
    cv
    #
    cz
    wcel
    #
    w3a
    #
    @27
    @29
    cT
    cmul
    co
    #
    wph
    @28
    @30
    simp2
    #
    @31
    @29
    cT
    @30
    wph
    @29
    cr
    wcel
    #
    @28
    @29
    zre
    #
    3ad2ant3
    wph
    @30
    cT
    cr
    wcel
    #
    @28
    wph
    @36
    @30
    wph
    cT
    @22
    cr
    fourierdlem94.t
    @22
    cr
    wcel
    wph
    c2
    cpi
    2re
    pire
    remulcli
    a1i
    syl5eqel
    adantr
    #
    3adant2
    remulcld
    readdcld
    #
    @31
    wph
    @30
    @28
    @27
    @32
    caddc
    co
    cF
    cfv
    @27
    cF
    cfv
    #
    wceq
    wph
    @28
    @30
    simp1
    wph
    @28
    @30
    simp3
    @33
    wph
    @30
    wa
    #
    @28
    wa
    vy
    cT
    cF
    @29
    @27
    @40
    cr
    cc
    cF
    wf
    #
    @28
    wph
    @41
    @30
    wph
    cr
    cr
    cc
    cF
    fourierdlem94.f
    cr
    cc
    wss
    #
    wph
    ax-resscn
    a1i
    #
    fssd
    #
    adantr
    #
    adantr
    @40
    @36
    @28
    @37
    adantr
    wph
    @30
    @28
    simplr
    @40
    @28
    simpr
    wph
    @2
    cr
    wcel
    #
    @2
    cT
    caddc
    co
    #
    cF
    cfv
    #
    @2
    cF
    cfv
    #
    wceq
    #
    @30
    @28
    wph
    @28
    wa
    #
    @27
    cT
    caddc
    co
    #
    cF
    cfv
    #
    @39
    wceq
    #
    wi
    wph
    @46
    wa
    #
    @50
    wi
    vx
    vy
    @27
    @2
    wceq
    #
    @51
    @55
    @54
    @50
    @56
    @28
    @46
    wph
    @27
    @2
    cr
    eleq1
    anbi2d
    @56
    @53
    @48
    @39
    @49
    @56
    @52
    @47
    cF
    @27
    @2
    cT
    caddc
    oveq1
    fveq2d
    @27
    @2
    cF
    fveq2
    eqeq12d
    imbi12d
    fourierdlem94.per
    chvarv
    ad4ant14
    fperiodmul
    syl21anc
    #
    wph
    @11
    cc0
    cM
    cfzo
    co
    #
    wcel
    #
    wa
    #
    @42
    @15
    cc
    @16
    wf
    #
    @15
    cr
    wss
    #
    cr
    @16
    cdv
    co
    #
    cdm
    #
    @15
    wceq
    @16
    @15
    cc
    ccncf
    co
    #
    wcel
    @42
    @60
    ax-resscn
    a1i
    #
    wph
    @61
    @59
    wph
    @15
    cr
    cc
    @16
    wph
    cr
    cr
    @15
    cF
    fourierdlem94.f
    @62
    wph
    @12
    @14
    ioossre
    #
    a1i
    fssresd
    #
    @43
    fssd
    adantr
    #
    @62
    @60
    @67
    a1i
    #
    @60
    @64
    cr
    cF
    cdv
    co
    #
    @15
    cioo
    crn
    ctg
    cfv
    #
    cnt
    cfv
    cfv
    #
    cres
    #
    cdm
    #
    @71
    @15
    cres
    #
    cdm
    #
    @15
    @60
    @63
    @74
    @60
    @42
    @41
    @24
    @62
    @63
    @74
    wceq
    @66
    wph
    @41
    @59
    @44
    adantr
    @24
    @60
    @25
    a1i
    @70
    cr
    @15
    cr
    @72
    cF
    ccnfld
    ctopn
    cfv
    #
    @78
    eqid
    #
    @78
    @79
    tgioo2
    dvres
    syl22anc
    #
    dmeqd
    @75
    @77
    wceq
    @60
    @74
    @76
    @73
    @15
    @71
    @12
    @14
    ioontr
    reseq2i
    #
    dmeqi
    a1i
    @60
    @76
    @65
    wcel
    #
    @15
    cc
    @76
    wf
    #
    @77
    @15
    wceq
    #
    fourierdlem94.dvcn
    @15
    cc
    @76
    cncff
    #
    @15
    cc
    @76
    fdm
    3syl
    #
    3eqtrd
    #
    @15
    cr
    @16
    dvcn
    syl31anc
    #
    @60
    vy
    @15
    @14
    @16
    @78
    @69
    @60
    @15
    cr
    cc
    @70
    ax-resscn
    syl6ss
    #
    @60
    @12
    @14
    @78
    @79
    @60
    @12
    @60
    cc0
    cM
    cfz
    co
    #
    cr
    @11
    cQ
    wph
    @90
    cr
    cQ
    wf
    #
    @59
    wph
    cQ
    cr
    @90
    cmap
    co
    wcel
    #
    @91
    wph
    @92
    cc0
    cQ
    cfv
    @0
    wceq
    #
    cM
    cQ
    cfv
    cpi
    wceq
    #
    wa
    #
    @12
    @14
    clt
    wbr
    #
    vi
    @58
    wral
    #
    wa
    #
    wph
    cQ
    cM
    cP
    cfv
    wcel
    #
    @92
    @98
    wa
    #
    fourierdlem94.q
    wph
    cM
    cn
    wcel
    @99
    @100
    wb
    fourierdlem94.m
    @0
    cpi
    cP
    cQ
    vi
    vn
    cM
    vp
    fourierdlem94.p
    fourierdlem2
    syl
    mpbid
    #
    simpld
    cQ
    cr
    @90
    elmapi
    syl
    #
    adantr
    #
    @59
    @11
    @90
    wcel
    wph
    @11
    cc0
    cM
    elfzofz
    adantl
    ffvelrnd
    #
    rexrd
    @60
    @90
    cr
    @13
    cQ
    @103
    @59
    @13
    @90
    wcel
    wph
    cc0
    cM
    @11
    fzofzp1
    adantl
    ffvelrnd
    #
    wph
    @96
    vi
    @58
    wph
    @92
    @95
    @97
    @101
    simprrd
    r19.21bi
    #
    lptioo2cn
    #
    @60
    vt
    vz
    @12
    @14
    @16
    @104
    @105
    wph
    @15
    cr
    @16
    wf
    @59
    @68
    adantr
    #
    @87
    @60
    vt
    cv
    #
    @71
    cfv
    #
    cabs
    cfv
    #
    @1
    cle
    wbr
    #
    vt
    @71
    cdm
    #
    wral
    #
    vz
    cr
    wrex
    #
    @109
    @63
    cfv
    #
    cabs
    cfv
    #
    @1
    cle
    wbr
    #
    vt
    @15
    wral
    #
    vz
    cr
    wrex
    wph
    @115
    @59
    wph
    vt
    vz
    @0
    cpi
    cQ
    @27
    @76
    @12
    climc
    co
    wcel
    vx
    cio
    cT
    vi
    vk
    vt
    cr
    @109
    cpi
    @109
    cmin
    co
    cT
    cdiv
    co
    cfl
    cfv
    cT
    cmul
    co
    caddc
    co
    cmpt
    #
    @71
    vj
    @58
    vj
    cv
    #
    cQ
    cfv
    #
    @121
    c1
    caddc
    co
    #
    cQ
    cfv
    #
    cioo
    co
    #
    cmpt
    @27
    @76
    @14
    climc
    co
    wcel
    vx
    cio
    cM
    wph
    cr
    cr
    cF
    @43
    @44
    @26
    dvbss
    wph
    cr
    cr
    cF
    wf
    @24
    @113
    cr
    @71
    wf
    fourierdlem94.f
    @26
    cr
    cF
    dvfre
    syl2anc
    @18
    @19
    @21
    @23
    fourierdlem94.m
    @102
    wph
    @93
    @94
    @97
    wph
    @92
    @98
    @101
    simprd
    #
    simplld
    wph
    @93
    @94
    @97
    @126
    simplrd
    fourierdlem94.dvcn
    @60
    vx
    @15
    @12
    @76
    @78
    @60
    @82
    @83
    fourierdlem94.dvcn
    @85
    syl
    #
    @89
    @60
    @12
    @14
    @78
    @79
    @60
    @14
    @105
    rexrd
    @104
    @106
    lptioo1cn
    #
    fourierdlem94.dvlb
    @79
    ellimciota
    @60
    vx
    @15
    @14
    @76
    @78
    @127
    @89
    @107
    fourierdlem94.dvub
    @79
    ellimciota
    wph
    @109
    @113
    wcel
    #
    wa
    @30
    wa
    #
    @109
    @32
    caddc
    co
    #
    @113
    wcel
    #
    @131
    @71
    cfv
    @110
    wceq
    #
    wph
    @30
    @129
    @132
    @133
    wa
    @40
    vt
    @32
    cF
    @71
    @45
    @40
    @29
    cT
    @30
    @34
    wph
    @35
    adantl
    @37
    remulcld
    @40
    @109
    cr
    wcel
    #
    wa
    vx
    cT
    cF
    @29
    @109
    @40
    @41
    @134
    @45
    adantr
    @40
    @36
    @134
    @37
    adantr
    wph
    @30
    @134
    simplr
    @40
    @134
    simpr
    wph
    @28
    @54
    @30
    @134
    fourierdlem94.per
    ad4ant14
    fperiodmul
    @71
    eqid
    fperdvper
    an32s
    #
    simpld
    @130
    @132
    @133
    @135
    simprd
    vj
    vi
    @58
    @125
    @15
    @121
    @11
    wceq
    #
    @122
    @12
    @124
    @14
    cioo
    @121
    @11
    cQ
    fveq2
    @136
    @123
    @13
    cQ
    @121
    @11
    c1
    caddc
    oveq1
    fveq2d
    oveq12d
    cbvmptv
    @120
    eqid
    fourierdlem71
    adantr
    @60
    @114
    @119
    vz
    cr
    @60
    @114
    @119
    @60
    @114
    wa
    #
    @118
    vt
    @15
    @60
    @114
    vt
    @60
    vt
    nfv
    @112
    vt
    @113
    nfra1
    nfan
    @137
    @109
    @15
    wcel
    #
    @118
    @137
    @138
    wa
    #
    @117
    @111
    @1
    cle
    @60
    @138
    @117
    @111
    wceq
    @114
    @60
    @138
    wa
    @116
    @110
    cabs
    @60
    @138
    @116
    @109
    @76
    cfv
    @110
    @60
    @109
    @63
    @76
    @60
    @63
    @74
    @76
    @80
    @81
    syl6eq
    fveq1d
    @109
    @15
    @71
    fvres
    sylan9eq
    fveq2d
    adantlr
    @139
    @114
    @129
    @112
    @60
    @114
    @138
    simplr
    @139
    @15
    @113
    @109
    @60
    @15
    @113
    wss
    #
    @114
    @138
    @60
    @84
    @140
    @86
    @15
    @71
    ssdmres
    sylibr
    ad2antrr
    @137
    @138
    simpr
    sseldd
    @112
    vt
    @113
    rspa
    syl2anc
    eqbrtrd
    ex
    ralrimi
    ex
    reximdv
    mpd
    #
    ioodvbdlimc2
    @79
    ellimciota
    fourierdlem94.x
    vy
    vx
    cr
    @6
    cpi
    @27
    cmin
    co
    #
    cT
    cdiv
    co
    #
    cfl
    cfv
    #
    cT
    cmul
    co
    @2
    @27
    wceq
    #
    @5
    @144
    cT
    cmul
    @145
    @4
    @143
    cfl
    @145
    @3
    @142
    cT
    cdiv
    @2
    @27
    cpi
    cmin
    oveq2
    oveq1d
    fveq2d
    oveq1d
    cbvmptv
    #
    vz
    vx
    cr
    @9
    @27
    @27
    @7
    cfv
    #
    caddc
    co
    @1
    @27
    wceq
    #
    @1
    @27
    @8
    @147
    caddc
    @148
    id
    @1
    @27
    @7
    fveq2
    oveq12d
    cbvmptv
    #
    fourierdlem49
    wph
    @60
    vw
    cv
    #
    @12
    @14
    cico
    co
    wcel
    wa
    @30
    wa
    @150
    cX
    @32
    caddc
    co
    wceq
    wa
    #
    vx
    vw
    @0
    cpi
    cr
    cP
    cQ
    @2
    @16
    @12
    climc
    co
    wcel
    vy
    cio
    cT
    vi
    vk
    vn
    @10
    cF
    cM
    cX
    @7
    vp
    @18
    @19
    @21
    fourierdlem94.p
    @23
    fourierdlem94.m
    fourierdlem94.q
    fourierdlem94.f
    @38
    @57
    @88
    @60
    vy
    @15
    @12
    @16
    @78
    @69
    @89
    @128
    @60
    vt
    vz
    @12
    @14
    @16
    @104
    @105
    @108
    @87
    @141
    ioodvbdlimc1
    @79
    ellimciota
    fourierdlem94.x
    @146
    @149
    @151
    biid
    fourierdlem48
    jca
end
