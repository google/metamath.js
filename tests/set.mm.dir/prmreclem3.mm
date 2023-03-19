include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "csqrt.mm"
include "cfl.mm"
include "cmul.mm"
include "cr.mm"
include "wcel.mm"
include "cfn.mm"
include "cn0.mm"
include "c1.mm"
include "cfz.mm"
include "wss.mm"
include "fzfi.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "cprime.mm"
include "cdif.mm"
include "wral.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "ssfi.mm"
include "mp2an.mm"
include "hashcl.mm"
include "ax-mp.mm"
include "nn0rei.mm"
include "a1i.mm"
include "cn.mm"
include "2nn.mm"
include "nnnn0d.mm"
include "nnexpcl.mm"
include "sylancr.mm"
include "cc0.mm"
include "cle.mm"
include "wa.mm"
include "nnrpd.mm"
include "rpsqrtcld.mm"
include "rprege0d.mm"
include "flge0nn0.mm"
include "syl.mm"
include "nn0mulcld.mm"
include "nn0red.mm"
include "nnred.mm"
include "rpred.mm"
include "remulcld.mm"
include "wceq.mm"
include "remulcl.mm"
include "cxp.mm"
include "cdom.mm"
include "xpfi.mm"
include "cdiv.mm"
include "cop.mm"
include "cz.mm"
include "clt.mm"
include "simpr.mm"
include "sseldi.mm"
include "elfznn.mm"
include "cuz.mm"
include "wi.mm"
include "prmreclem1.mm"
include "simp2d.mm"
include "wne.mm"
include "wb.mm"
include "simp1d.mm"
include "nnsqcld.mm"
include "nnzd.mm"
include "nnne0d.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "nnre.mm"
include "nngt0.mm"
include "jca.mm"
include "divgt0.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "adantr.mm"
include "dvdsmul1.mm"
include "nncnd.mm"
include "divcan1d.mm"
include "breqtrd.mm"
include "dvdsle.mm"
include "mpd.mm"
include "elfzle2.mm"
include "letrd.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "elfz5.mm"
include "mpbird.mm"
include "weq.mm"
include "breq2.mm"
include "notbid.mm"
include "ralbidv.mm"
include "elrab2.mm"
include "sylib.mm"
include "simprd.mm"
include "eldifi.mm"
include "prmz.mm"
include "adantl.mm"
include "dvdstr.mm"
include "mpan2d.mm"
include "con3d.mm"
include "ralimdva.mm"
include "wo.mm"
include "elnn1uz2.mm"
include "ord.mm"
include "simp3d.mm"
include "sylsyld.mm"
include "mt4d.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "recnd.mm"
include "sqsqrtd.mm"
include "breqtrrd.mm"
include "crp.mm"
include "rprege0.mm"
include "le2sq.mm"
include "flge.mm"
include "nn0zd.mm"
include "opelxpi.mm"
include "ex.mm"
include "ovex.mm"
include "fvex.mm"
include "opth.mm"
include "oveq1.mm"
include "oveq12.mm"
include "sylan2.mm"
include "sylbi.mm"
include "adantrr.mm"
include "ssriv.mm"
include "sstri.mm"
include "simprr.mm"
include "eqeq12d.mm"
include "syl5ib.mm"
include "id.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "opeq12d.mm"
include "impbid1.mm"
include "dom2d.mm"
include "mpi.mm"
include "hashdom.mm"
include "sylibr.mm"
include "hashxp.mm"
include "hashfz1.mm"
include "oveq2d.mm"
include "syl5eq.mm"
include "nn0ge0d.mm"
include "prmreclem2.mm"
include "lemul1ad.mm"
include "caddc.mm"
include "fllelt.mm"
include "simpld.mm"
include "lemul2a.mm"
include "syl31anc.mm"

theorem prmreclem3
  let wph: wff ph
  let cQ: class Q
  let vn: setvar n
  let cF: class F
  let cK: class K
  let cM: class M
  let cN: class N
  let vr: setvar r
  let vp: setvar p
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vq: setvar q
  let cA: class A
  let cW: class W
  assume prmrec.1: |- F = ( n e. NN |-> if ( n e. Prime , ( 1 / n ) , 0 ) )
  assume prmrec.2: |- ( ph -> K e. NN )
  assume prmrec.3: |- ( ph -> N e. NN )
  assume prmrec.4: |- M = { n e. ( 1 ... N ) | A. p e. ( Prime \ ( 1 ... K ) ) -. p || n }
  assume prmreclem2.5: |- Q = ( n e. NN |-> sup ( { r e. NN | ( r ^ 2 ) || n } , RR , < ) )

  disjoint n p
  disjoint n r
  disjoint F n
  disjoint p r
  disjoint F p
  disjoint F r
  disjoint K n
  disjoint K p
  disjoint M n
  disjoint M p
  disjoint n ph
  disjoint p ph
  disjoint Q n
  disjoint Q p
  disjoint Q r
  disjoint N n
  disjoint N p
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j p
  disjoint j r
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint F j
  disjoint k m
  disjoint k n
  disjoint k p
  disjoint k r
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint m n
  disjoint m p
  disjoint m r
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint j q
  disjoint K j
  disjoint k q
  disjoint K k
  disjoint n q
  disjoint p q
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint K q
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint M k
  disjoint M q
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint A r
  disjoint j ph
  disjoint k ph
  disjoint ph q
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint Q x
  disjoint Q y
  disjoint Q z
  disjoint W j
  disjoint W k
  disjoint W q
  disjoint W x
  disjoint N j
  disjoint N k
  disjoint N q
  disjoint N x
  disjoint N y
  disjoint N z
  assert |- ( ph -> ( # ` M ) <_ ( ( 2 ^ K ) x. ( sqrt ` N ) ) )

  proof
    wph
    cM
    chash
    cfv
    #
    c2
    cK
    cexp
    co
    #
    cN
    csqrt
    cfv
    #
    cfl
    cfv
    #
    cmul
    co
    #
    @1
    @2
    cmul
    co
    #
    @0
    cr
    wcel
    wph
    @0
    cM
    cfn
    wcel
    #
    @0
    cn0
    wcel
    c1
    cN
    cfz
    co
    #
    cfn
    wcel
    cM
    @7
    wss
    @6
    c1
    cN
    fzfi
    cM
    vp
    cv
    #
    vn
    cv
    #
    cdvds
    wbr
    #
    wn
    #
    vp
    cprime
    c1
    cK
    cfz
    co
    #
    cdif
    #
    wral
    #
    vn
    @7
    crab
    @7
    prmrec.4
    @14
    vn
    @7
    ssrab2
    eqsstri
    #
    @7
    cM
    ssfi
    mp2an
    #
    cM
    hashcl
    ax-mp
    nn0rei
    a1i
    #
    wph
    @4
    wph
    @1
    @3
    wph
    @1
    wph
    c2
    cn
    wcel
    cK
    cn0
    wcel
    @1
    cn
    wcel
    2nn
    wph
    cK
    prmrec.2
    nnnn0d
    c2
    cK
    nnexpcl
    sylancr
    #
    nnnn0d
    wph
    @2
    cr
    wcel
    #
    cc0
    @2
    cle
    wbr
    wa
    #
    @3
    cn0
    wcel
    #
    wph
    @2
    wph
    cN
    wph
    cN
    prmrec.3
    nnrpd
    rpsqrtcld
    #
    rprege0d
    @2
    flge0nn0
    syl
    #
    nn0mulcld
    nn0red
    #
    wph
    @1
    @2
    wph
    @1
    @18
    nnred
    #
    wph
    @2
    @22
    rpred
    #
    remulcld
    wph
    @0
    vx
    cv
    #
    cQ
    cfv
    #
    c1
    wceq
    #
    vx
    cM
    crab
    #
    chash
    cfv
    #
    @3
    cmul
    co
    #
    @4
    @17
    wph
    @31
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    @32
    cr
    wcel
    @31
    @30
    cfn
    wcel
    #
    @31
    cn0
    wcel
    @6
    @30
    cM
    wss
    @35
    @16
    @29
    vx
    cM
    ssrab2
    cM
    @30
    ssfi
    mp2an
    #
    @30
    hashcl
    ax-mp
    nn0rei
    #
    wph
    @3
    @23
    nn0red
    #
    @31
    @3
    remulcl
    sylancr
    @24
    wph
    @0
    @30
    c1
    @3
    cfz
    co
    #
    cxp
    #
    chash
    cfv
    #
    @32
    cle
    wph
    cM
    @40
    cdom
    wbr
    #
    @0
    @41
    cle
    wbr
    #
    wph
    @40
    cfn
    wcel
    #
    @42
    @35
    @39
    cfn
    wcel
    #
    @44
    @36
    c1
    @3
    fzfi
    #
    @30
    @39
    xpfi
    mp2an
    #
    wph
    vy
    vz
    cM
    @40
    vy
    cv
    #
    @48
    cQ
    cfv
    #
    c2
    cexp
    co
    #
    cdiv
    co
    #
    @49
    cop
    #
    vz
    cv
    #
    @53
    cQ
    cfv
    #
    c2
    cexp
    co
    #
    cdiv
    co
    #
    @54
    cop
    #
    cfn
    wph
    @48
    cM
    wcel
    #
    @52
    @40
    wcel
    #
    wph
    @58
    wa
    #
    @51
    @30
    wcel
    #
    @49
    @39
    wcel
    #
    @59
    @60
    @51
    cM
    wcel
    #
    @51
    cQ
    cfv
    #
    c1
    wceq
    #
    @61
    @60
    @51
    @7
    wcel
    #
    @8
    @51
    cdvds
    wbr
    #
    wn
    #
    vp
    @13
    wral
    #
    @63
    @60
    @66
    @51
    cN
    cle
    wbr
    #
    @60
    @51
    @48
    cN
    @60
    @51
    @60
    @51
    cz
    wcel
    #
    cc0
    @51
    clt
    wbr
    #
    @51
    cn
    wcel
    #
    @60
    @50
    @48
    cdvds
    wbr
    #
    @71
    @60
    @48
    cn
    wcel
    #
    @74
    @60
    @48
    @7
    wcel
    #
    @75
    @60
    cM
    @7
    @48
    @15
    wph
    @58
    simpr
    #
    sseldi
    #
    @48
    cN
    elfznn
    #
    syl
    #
    @75
    @49
    cn
    wcel
    #
    @74
    @9
    c2
    cuz
    cfv
    #
    wcel
    @9
    c2
    cexp
    co
    @51
    cdvds
    wbr
    wn
    wi
    #
    cQ
    vn
    @9
    @48
    vr
    prmreclem2.5
    prmreclem1
    #
    simp2d
    syl
    #
    @60
    @50
    cz
    wcel
    #
    @50
    cc0
    wne
    @48
    cz
    wcel
    #
    @74
    @71
    wb
    @60
    @50
    @60
    @49
    @60
    @75
    @81
    @80
    @75
    @81
    @74
    @83
    @84
    simp1d
    syl
    #
    nnsqcld
    #
    nnzd
    #
    @60
    @50
    @89
    nnne0d
    #
    @60
    @48
    @80
    nnzd
    #
    @50
    @48
    dvdsval2
    syl3anc
    mpbid
    #
    @60
    @75
    @50
    cn
    wcel
    #
    @72
    @80
    @89
    @75
    @48
    cr
    wcel
    #
    cc0
    @48
    clt
    wbr
    #
    wa
    @50
    cr
    wcel
    #
    cc0
    @50
    clt
    wbr
    #
    wa
    @72
    @94
    @75
    @95
    @96
    @48
    nnre
    @48
    nngt0
    jca
    @94
    @97
    @98
    @50
    nnre
    @50
    nngt0
    jca
    @48
    @50
    divgt0
    syl2an
    syl2anc
    @51
    elnnz
    sylanbrc
    #
    nnred
    @60
    @48
    @80
    nnred
    #
    wph
    cN
    cr
    wcel
    @58
    wph
    cN
    prmrec.3
    nnred
    adantr
    #
    @60
    @51
    @48
    cdvds
    wbr
    #
    @51
    @48
    cle
    wbr
    #
    @60
    @51
    @51
    @50
    cmul
    co
    #
    @48
    cdvds
    @60
    @71
    @86
    @51
    @104
    cdvds
    wbr
    @93
    @90
    @51
    @50
    dvdsmul1
    syl2anc
    @60
    @48
    @50
    @60
    @48
    @80
    nncnd
    @60
    @50
    @89
    nncnd
    @91
    divcan1d
    #
    breqtrd
    #
    @60
    @71
    @75
    @102
    @103
    wi
    @93
    @80
    @51
    @48
    dvdsle
    syl2anc
    mpd
    @60
    @76
    @48
    cN
    cle
    wbr
    @78
    @48
    c1
    cN
    elfzle2
    syl
    #
    letrd
    @60
    @51
    c1
    cuz
    cfv
    #
    wcel
    cN
    cz
    wcel
    #
    @66
    @70
    wb
    @60
    @51
    cn
    @108
    @99
    nnuz
    syl6eleq
    wph
    @109
    @58
    wph
    cN
    prmrec.3
    nnzd
    adantr
    @51
    c1
    cN
    elfz5
    syl2anc
    mpbird
    @60
    @8
    @48
    cdvds
    wbr
    #
    wn
    #
    vp
    @13
    wral
    #
    @69
    @60
    @76
    @112
    @60
    @58
    @76
    @112
    wa
    @77
    @14
    @112
    vn
    @48
    @7
    cM
    vn
    vy
    weq
    #
    @11
    @111
    vp
    @13
    @113
    @10
    @110
    @9
    @48
    @8
    cdvds
    breq2
    notbid
    ralbidv
    prmrec.4
    elrab2
    sylib
    simprd
    @60
    @111
    @68
    vp
    @13
    @60
    @8
    @13
    wcel
    #
    wa
    #
    @67
    @110
    @115
    @67
    @102
    @110
    @60
    @102
    @114
    @106
    adantr
    @115
    @8
    cz
    wcel
    #
    @71
    @87
    @67
    @102
    wa
    @110
    wi
    @114
    @116
    @60
    @114
    @8
    cprime
    wcel
    @116
    @8
    cprime
    @12
    eldifi
    @8
    prmz
    syl
    adantl
    @60
    @71
    @114
    @93
    adantr
    @60
    @87
    @114
    @92
    adantr
    @8
    @51
    @48
    dvdstr
    syl3anc
    mpan2d
    con3d
    ralimdva
    mpd
    @14
    @69
    vn
    @51
    @7
    cM
    @9
    @51
    wceq
    #
    @11
    @68
    vp
    @13
    @117
    @10
    @67
    @9
    @51
    @8
    cdvds
    breq2
    notbid
    ralbidv
    prmrec.4
    elrab2
    sylanbrc
    @60
    @64
    c2
    cexp
    co
    #
    @51
    cdvds
    wbr
    #
    @65
    @60
    @73
    @119
    @99
    @73
    @64
    cn
    wcel
    #
    @119
    cA
    @82
    wcel
    cA
    c2
    cexp
    co
    @51
    @118
    cdiv
    co
    cdvds
    wbr
    wn
    wi
    #
    cQ
    vn
    cA
    @51
    vr
    prmreclem2.5
    prmreclem1
    #
    simp2d
    syl
    @60
    @75
    @65
    wn
    @64
    @82
    wcel
    #
    @119
    wn
    #
    @80
    @60
    @65
    @123
    @60
    @120
    @65
    @123
    wo
    @60
    @73
    @120
    @99
    @73
    @120
    @119
    @121
    @122
    simp1d
    syl
    @64
    elnn1uz2
    sylib
    ord
    @75
    @81
    @74
    @123
    @124
    wi
    cQ
    vn
    @64
    @48
    vr
    prmreclem2.5
    prmreclem1
    simp3d
    sylsyld
    mt4d
    @29
    @65
    vx
    @51
    cM
    @27
    @51
    wceq
    @28
    @64
    c1
    @27
    @51
    cQ
    fveq2
    eqeq1d
    elrab
    sylanbrc
    @60
    @62
    @49
    @3
    cle
    wbr
    #
    @60
    @49
    @2
    cle
    wbr
    #
    @125
    @60
    @126
    @50
    @2
    c2
    cexp
    co
    #
    cle
    wbr
    #
    @60
    @50
    cN
    @127
    cle
    @60
    @50
    @48
    cN
    @60
    @50
    @89
    nnred
    @100
    @101
    @60
    @74
    @50
    @48
    cle
    wbr
    #
    @85
    @60
    @86
    @75
    @74
    @129
    wi
    @90
    @80
    @50
    @48
    dvdsle
    syl2anc
    mpd
    @107
    letrd
    @60
    cN
    @60
    cN
    @101
    recnd
    sqsqrtd
    breqtrrd
    @60
    @49
    crp
    wcel
    #
    @2
    crp
    wcel
    #
    @126
    @128
    wb
    #
    @60
    @49
    @88
    nnrpd
    wph
    @131
    @58
    @22
    adantr
    @130
    @49
    cr
    wcel
    cc0
    @49
    cle
    wbr
    wa
    @20
    @132
    @131
    @49
    rprege0
    @2
    rprege0
    @49
    @2
    le2sq
    syl2an
    syl2anc
    mpbird
    @60
    @19
    @49
    cz
    wcel
    @126
    @125
    wb
    wph
    @19
    @58
    @26
    adantr
    @60
    @49
    @88
    nnzd
    @2
    @49
    flge
    syl2anc
    mpbid
    @60
    @49
    @108
    wcel
    @3
    cz
    wcel
    #
    @62
    @125
    wb
    @60
    @49
    cn
    @108
    @88
    nnuz
    syl6eleq
    wph
    @133
    @58
    wph
    @3
    @23
    nn0zd
    adantr
    @49
    c1
    @3
    elfz5
    syl2anc
    mpbird
    @51
    @49
    @30
    @39
    opelxpi
    syl2anc
    ex
    wph
    @58
    @53
    cM
    wcel
    #
    wa
    #
    @52
    @57
    wceq
    #
    vy
    vz
    weq
    #
    wb
    wph
    @135
    wa
    #
    @136
    @137
    @136
    @104
    @56
    @55
    cmul
    co
    #
    wceq
    #
    @138
    @137
    @136
    @51
    @56
    wceq
    #
    @49
    @54
    wceq
    #
    wa
    @140
    @51
    @49
    @56
    @54
    @48
    @50
    cdiv
    ovex
    @48
    cQ
    fvex
    opth
    @142
    @141
    @50
    @55
    wceq
    @140
    @49
    @54
    c2
    cexp
    oveq1
    @51
    @56
    @50
    @55
    cmul
    oveq12
    sylan2
    sylbi
    @138
    @104
    @48
    @139
    @53
    wph
    @58
    @104
    @48
    wceq
    @134
    @105
    adantrr
    @138
    @53
    @55
    @138
    @53
    @138
    cM
    cn
    @53
    cM
    @7
    cn
    @15
    vy
    @7
    cn
    @79
    ssriv
    sstri
    wph
    @58
    @134
    simprr
    sseldi
    #
    nncnd
    @138
    @55
    @138
    @54
    @138
    @53
    cn
    wcel
    #
    @54
    cn
    wcel
    #
    @143
    @144
    @145
    @55
    @53
    cdvds
    wbr
    c2
    @82
    wcel
    c2
    c2
    cexp
    co
    @56
    cdvds
    wbr
    wn
    wi
    cQ
    vn
    c2
    @53
    vr
    prmreclem2.5
    prmreclem1
    simp1d
    syl
    nnsqcld
    #
    nncnd
    @138
    @55
    @146
    nnne0d
    divcan1d
    eqeq12d
    syl5ib
    @137
    @51
    @56
    @49
    @54
    @137
    @48
    @53
    @50
    @55
    cdiv
    @137
    id
    @137
    @49
    @54
    c2
    cexp
    @48
    @53
    cQ
    fveq2
    #
    oveq1d
    oveq12d
    @147
    opeq12d
    impbid1
    ex
    dom2d
    mpi
    @6
    @44
    @43
    @42
    wb
    @16
    @47
    cM
    @40
    cfn
    hashdom
    mp2an
    sylibr
    wph
    @41
    @31
    @39
    chash
    cfv
    #
    cmul
    co
    #
    @32
    @35
    @45
    @41
    @149
    wceq
    @36
    @46
    @30
    @39
    hashxp
    mp2an
    wph
    @148
    @3
    @31
    cmul
    wph
    @21
    @148
    @3
    wceq
    @23
    @3
    hashfz1
    syl
    oveq2d
    syl5eq
    breqtrd
    wph
    @31
    @1
    @3
    @33
    wph
    @37
    a1i
    @25
    @38
    wph
    @3
    @23
    nn0ge0d
    wph
    vx
    cQ
    vn
    cF
    cK
    cM
    cN
    vr
    vp
    prmrec.1
    prmrec.2
    prmrec.3
    prmrec.4
    prmreclem2.5
    prmreclem2
    lemul1ad
    letrd
    wph
    @34
    @19
    @1
    cr
    wcel
    cc0
    @1
    cle
    wbr
    wa
    @3
    @2
    cle
    wbr
    #
    @4
    @5
    cle
    wbr
    @38
    @26
    wph
    @1
    wph
    @1
    @18
    nnrpd
    rprege0d
    wph
    @150
    @2
    @3
    c1
    caddc
    co
    clt
    wbr
    #
    wph
    @19
    @150
    @151
    wa
    @26
    @2
    fllelt
    syl
    simpld
    @3
    @2
    @1
    lemul2a
    syl31anc
    letrd
end
