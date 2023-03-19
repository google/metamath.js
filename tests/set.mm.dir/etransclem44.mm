include "cc0.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cr.mm"
include "cdvn.mm"
include "cmul.mm"
include "cfa.mm"
include "cdiv.mm"
include "cfz.mm"
include "caddc.mm"
include "cxp.mm"
include "cop.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "c1st.mm"
include "c2nd.mm"
include "csu.mm"
include "wceq.mm"
include "a1i.mm"
include "nfv.mm"
include "nfcv.mm"
include "cfn.mm"
include "wcel.mm"
include "fzfi.mm"
include "xpfi.mm"
include "mp2an.mm"
include "wa.mm"
include "cn0.mm"
include "cz.mm"
include "wf.mm"
include "adantr.mm"
include "fzssnn0.mm"
include "xp1st.mm"
include "sseldi.mm"
include "adantl.mm"
include "ffvelrnd.mm"
include "cc.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "reopn.mm"
include "eqid.mm"
include "tgioo2.mm"
include "eleqtri.mm"
include "cn.mm"
include "cprime.mm"
include "prmnn.mm"
include "syl.mm"
include "xp2nd.mm"
include "elfznn0.mm"
include "nn0red.mm"
include "nn0zd.mm"
include "etransclem42.mm"
include "zmulcld.mm"
include "zcnd.mm"
include "cuz.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "eluzfz1.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "0zd.mm"
include "nnzd.mm"
include "nnm1nn0.mm"
include "zaddcld.mm"
include "3jca.mm"
include "nn0ge0d.mm"
include "nnnn0d.mm"
include "nn0mulcld.mm"
include "zred.mm"
include "addge02d.mm"
include "mpbid.mm"
include "jca32.mm"
include "elfz2.mm"
include "sylibr.mm"
include "opelxp.mm"
include "sylanbrc.mm"
include "fveq2.mm"
include "cvv.mm"
include "0re.mm"
include "ovex.mm"
include "op1stg.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "op2ndg.mm"
include "fveq12d.mm"
include "oveq12d.mm"
include "fsumsplit1.mm"
include "oveq1d.mm"
include "wss.mm"
include "difss.mm"
include "ssfi.mm"
include "eldifi.mm"
include "sylan2.mm"
include "fsumzcl.mm"
include "faccld.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divdird.mm"
include "3eqtrd.mm"
include "divassd.mm"
include "cdvds.mm"
include "cmap.mm"
include "crab.mm"
include "cmpt.mm"
include "cif.mm"
include "cexp.mm"
include "etransclem5.mm"
include "etransclem11.mm"
include "etransclem37.mm"
include "wne.mm"
include "wb.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "fsumdivc.mm"
include "wo.mm"
include "wn.mm"
include "cabs.mm"
include "1zzd.mm"
include "zabscl.mm"
include "nn0abscl.mm"
include "absne0d.mm"
include "elnnne0.mm"
include "nnge1d.mm"
include "clt.mm"
include "zltlem1.mm"
include "syl2anc.mm"
include "fzm1ndvds.mm"
include "dvdsabsb.mm"
include "mtbird.mm"
include "etransclem41.mm"
include "jca.mm"
include "pm4.56.mm"
include "sylib.mm"
include "euclemma.mm"
include "breq2d.mm"
include "eldifn.mm"
include "1st2nd2.mm"
include "simpr.mm"
include "simpl.mm"
include "opeq12d.mm"
include "eqtrd.mm"
include "velsn.mm"
include "mtand.mm"
include "etransclem38.mm"
include "dvdsmultr2.mm"
include "sylc.mm"
include "breqtrrd.mm"
include "fsumdvds.mm"
include "etransclem9.mm"
include "eqnetrd.mm"

theorem etransclem44
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cP: class P
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cK: class K
  let cM: class M
  let vc: setvar c
  let vd: setvar d
  let vn: setvar n
  let vm: setvar m
  let vy: setvar y
  assume etransclem44.a: |- ( ph -> A : NN0 --> ZZ )
  assume etransclem44.a0: |- ( ph -> ( A ` 0 ) =/= 0 )
  assume etransclem44.m: |- ( ph -> M e. NN0 )
  assume etransclem44.p: |- ( ph -> P e. Prime )
  assume etransclem44.ap: |- ( ph -> ( abs ` ( A ` 0 ) ) < P )
  assume etransclem44.mp: |- ( ph -> ( ! ` M ) < P )
  assume etransclem44.f: |- F = ( x e. RR |-> ( ( x ^ ( P - 1 ) ) x. prod_ j e. ( 1 ... M ) ( ( x - j ) ^ P ) ) )
  assume etransclem44.k: |- K = ( sum_ k e. ( ( 0 ... M ) X. ( 0 ... ( ( M x. P ) + ( P - 1 ) ) ) ) ( ( A ` ( 1st ` k ) ) x. ( ( ( RR Dn F ) ` ( 2nd ` k ) ) ` ( 1st ` k ) ) ) / ( ! ` ( P - 1 ) ) )

  disjoint A k
  disjoint F k
  disjoint M j
  disjoint M k
  disjoint M x
  disjoint j k
  disjoint j x
  disjoint k x
  disjoint P j
  disjoint P k
  disjoint P x
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint k x
  disjoint M c
  disjoint M d
  disjoint M n
  disjoint c d
  disjoint c j
  disjoint c k
  disjoint c n
  disjoint c x
  disjoint d j
  disjoint d k
  disjoint d n
  disjoint d x
  disjoint j n
  disjoint k n
  disjoint n x
  disjoint M m
  disjoint c m
  disjoint d m
  disjoint j m
  disjoint m n
  disjoint m x
  disjoint P c
  disjoint P n
  disjoint P y
  disjoint c y
  disjoint j y
  disjoint k y
  disjoint n y
  disjoint x y
  disjoint c ph
  disjoint n ph
  assert |- ( ph -> K =/= 0 )

  proof
    wph
    cK
    cc0
    cA
    cfv
    #
    cc0
    cP
    c1
    cmin
    co
    #
    cr
    cF
    cdvn
    co
    #
    cfv
    #
    cfv
    #
    cmul
    co
    #
    @1
    cfa
    cfv
    #
    cdiv
    co
    #
    cc0
    cM
    cfz
    co
    #
    cc0
    cM
    cP
    cmul
    co
    #
    @1
    caddc
    co
    #
    cfz
    co
    #
    cxp
    #
    cc0
    @1
    cop
    #
    csn
    #
    cdif
    #
    vk
    cv
    #
    c1st
    cfv
    #
    cA
    cfv
    #
    @17
    @16
    c2nd
    cfv
    #
    @2
    cfv
    #
    cfv
    #
    cmul
    co
    #
    vk
    csu
    #
    @6
    cdiv
    co
    #
    caddc
    co
    #
    cc0
    wph
    cK
    @12
    @22
    vk
    csu
    #
    @6
    cdiv
    co
    #
    @5
    @23
    caddc
    co
    #
    @6
    cdiv
    co
    @25
    cK
    @27
    wceq
    wph
    etransclem44.k
    a1i
    wph
    @26
    @28
    @6
    cdiv
    wph
    @12
    @22
    @13
    @5
    vk
    wph
    vk
    nfv
    vk
    @5
    nfcv
    @12
    cfn
    wcel
    #
    wph
    @8
    cfn
    wcel
    @11
    cfn
    wcel
    @29
    cc0
    cM
    fzfi
    cc0
    @10
    fzfi
    @8
    @11
    xpfi
    mp2an
    #
    a1i
    wph
    @16
    @12
    wcel
    #
    wa
    #
    @22
    @32
    @18
    @21
    @32
    cn0
    cz
    @17
    cA
    wph
    cn0
    cz
    cA
    wf
    @31
    etransclem44.a
    adantr
    @31
    @17
    cn0
    wcel
    wph
    @31
    @8
    cn0
    @17
    cM
    fzssnn0
    #
    @16
    @8
    @11
    xp1st
    #
    sseldi
    adantl
    #
    ffvelrnd
    #
    @32
    vx
    cP
    cr
    vj
    cF
    @17
    cM
    @19
    cr
    cr
    cr
    cc
    cpr
    wcel
    #
    @32
    reelprrecn
    a1i
    cr
    ccnfld
    ctopn
    cfv
    #
    cr
    crest
    co
    #
    wcel
    #
    @32
    cr
    cioo
    crn
    ctg
    cfv
    @39
    reopn
    @38
    @38
    eqid
    tgioo2
    eleqtri
    #
    a1i
    wph
    cP
    cn
    wcel
    #
    @31
    wph
    cP
    cprime
    wcel
    #
    @42
    etransclem44.p
    cP
    prmnn
    syl
    #
    adantr
    wph
    cM
    cn0
    wcel
    #
    @31
    etransclem44.m
    adantr
    etransclem44.f
    @31
    @19
    cn0
    wcel
    #
    wph
    @31
    @19
    @11
    wcel
    @46
    @16
    @8
    @11
    xp2nd
    @19
    @10
    elfznn0
    syl
    #
    adantl
    @32
    @17
    @35
    nn0red
    #
    @32
    @17
    @35
    nn0zd
    etransclem42
    #
    zmulcld
    #
    zcnd
    #
    wph
    cc0
    @8
    wcel
    #
    @1
    @11
    wcel
    #
    @13
    @12
    wcel
    wph
    cM
    cc0
    cuz
    cfv
    #
    wcel
    @52
    wph
    cM
    cn0
    @54
    etransclem44.m
    nn0uz
    syl6eleq
    cc0
    cM
    eluzfz1
    syl
    #
    wph
    cc0
    cz
    wcel
    #
    @10
    cz
    wcel
    #
    @1
    cz
    wcel
    #
    w3a
    #
    cc0
    @1
    cle
    wbr
    #
    @1
    @10
    cle
    wbr
    #
    wa
    wa
    @53
    wph
    @59
    @60
    @61
    wph
    @56
    @57
    @58
    wph
    0zd
    #
    wph
    @9
    @1
    wph
    cM
    cP
    wph
    cM
    etransclem44.m
    nn0zd
    wph
    cP
    @44
    nnzd
    #
    zmulcld
    #
    wph
    @1
    wph
    @42
    @1
    cn0
    wcel
    @44
    cP
    nnm1nn0
    syl
    #
    nn0zd
    #
    zaddcld
    @66
    3jca
    wph
    @1
    @65
    nn0ge0d
    wph
    cc0
    @9
    cle
    wbr
    @61
    wph
    @9
    wph
    cM
    cP
    etransclem44.m
    wph
    cP
    @44
    nnnn0d
    nn0mulcld
    nn0ge0d
    wph
    @1
    @9
    wph
    @1
    @65
    nn0red
    wph
    @9
    @64
    zred
    addge02d
    mpbid
    jca32
    @1
    cc0
    @10
    elfz2
    sylibr
    cc0
    @1
    @8
    @11
    opelxp
    sylanbrc
    @16
    @13
    wceq
    #
    @18
    @0
    @21
    @4
    cmul
    @67
    @17
    cc0
    cA
    @67
    @17
    @13
    c1st
    cfv
    #
    cc0
    @16
    @13
    c1st
    fveq2
    cc0
    cr
    wcel
    #
    @1
    cvv
    wcel
    #
    @68
    cc0
    wceq
    0re
    cP
    c1
    cmin
    ovex
    #
    cc0
    @1
    cr
    cvv
    op1stg
    mp2an
    syl6eq
    #
    fveq2d
    @67
    @17
    cc0
    @20
    @3
    @67
    @19
    @1
    @2
    @67
    @19
    @13
    c2nd
    cfv
    #
    @1
    @16
    @13
    c2nd
    fveq2
    @69
    @70
    @73
    @1
    wceq
    0re
    @71
    cc0
    @1
    cr
    cvv
    op2ndg
    mp2an
    syl6eq
    fveq2d
    @72
    fveq12d
    oveq12d
    fsumsplit1
    oveq1d
    wph
    @5
    @23
    @6
    wph
    @5
    wph
    @0
    @4
    wph
    cn0
    cz
    cc0
    cA
    etransclem44.a
    wph
    @8
    cn0
    cc0
    @33
    @55
    sseldi
    ffvelrnd
    #
    wph
    vx
    cP
    cr
    vj
    cF
    cc0
    cM
    @1
    cr
    @37
    wph
    reelprrecn
    a1i
    #
    @40
    wph
    @41
    a1i
    #
    @44
    etransclem44.m
    etransclem44.f
    @65
    @69
    wph
    0re
    a1i
    #
    @62
    etransclem42
    #
    zmulcld
    zcnd
    wph
    @23
    wph
    @15
    @22
    vk
    @15
    cfn
    wcel
    #
    wph
    @29
    @15
    @12
    wss
    @79
    @30
    @12
    @14
    difss
    @12
    @15
    ssfi
    mp2an
    a1i
    #
    @16
    @15
    wcel
    #
    wph
    @31
    @22
    cz
    wcel
    @16
    @12
    @14
    eldifi
    #
    @50
    sylan2
    fsumzcl
    zcnd
    wph
    @6
    wph
    @1
    @65
    faccld
    #
    nncnd
    #
    wph
    @6
    @83
    nnne0d
    #
    divdird
    3eqtrd
    wph
    cP
    @7
    @24
    @63
    wph
    cP
    @44
    nnne0d
    wph
    @7
    @0
    @4
    @6
    cdiv
    co
    #
    cmul
    co
    #
    cz
    wph
    @0
    @4
    @6
    wph
    @0
    @74
    zcnd
    #
    wph
    @4
    @78
    zcnd
    @84
    @85
    divassd
    #
    wph
    @0
    @86
    @74
    wph
    @6
    @4
    cdvds
    wbr
    #
    @86
    cz
    wcel
    #
    wph
    vx
    vm
    cn0
    @8
    @16
    vd
    cv
    cfv
    vk
    csu
    vm
    cv
    #
    wceq
    vd
    cc0
    @92
    cfz
    co
    @8
    cmap
    co
    crab
    cmpt
    #
    cP
    cr
    vj
    vn
    cF
    vk
    @8
    vy
    cr
    vy
    cv
    @16
    cmin
    co
    @16
    cc0
    wceq
    @1
    cP
    cif
    cexp
    co
    cmpt
    cmpt
    #
    cc0
    cM
    @1
    cr
    vc
    @75
    @76
    @44
    etransclem44.m
    etransclem44.f
    @65
    vy
    vx
    cP
    vk
    vj
    cM
    cr
    etransclem5
    #
    vk
    vj
    vn
    vm
    cM
    vd
    vc
    etransclem11
    #
    @55
    @77
    etransclem37
    wph
    @6
    cz
    wcel
    #
    @6
    cc0
    wne
    #
    @4
    cz
    wcel
    @90
    @91
    wb
    wph
    @6
    @83
    nnzd
    #
    @85
    @78
    @6
    @4
    dvdsval2
    syl3anc
    mpbid
    #
    zmulcld
    eqeltrd
    wph
    @24
    @15
    @22
    @6
    cdiv
    co
    #
    vk
    csu
    #
    cz
    wph
    @15
    @22
    @6
    vk
    @80
    @84
    @81
    wph
    @31
    @22
    cc
    wcel
    @82
    @51
    sylan2
    @85
    fsumdivc
    #
    wph
    @15
    @101
    vk
    @80
    wph
    @81
    wa
    #
    @101
    @18
    @21
    @6
    cdiv
    co
    #
    cmul
    co
    #
    cz
    @104
    @18
    @21
    @6
    @81
    wph
    @31
    @18
    cc
    wcel
    @82
    @32
    @18
    @36
    zcnd
    sylan2
    @104
    @21
    @81
    wph
    @31
    @21
    cz
    wcel
    #
    @82
    @49
    sylan2
    #
    zcnd
    wph
    @6
    cc
    wcel
    @81
    @84
    adantr
    wph
    @98
    @81
    @85
    adantr
    #
    divassd
    #
    @104
    @18
    @105
    @81
    wph
    @31
    @18
    cz
    wcel
    #
    @82
    @36
    sylan2
    #
    @104
    @6
    @21
    cdvds
    wbr
    #
    @105
    cz
    wcel
    #
    @104
    vx
    @93
    cP
    cr
    vj
    vn
    cF
    @94
    @17
    cM
    @19
    cr
    vc
    @37
    @104
    reelprrecn
    a1i
    @40
    @104
    @41
    a1i
    wph
    @42
    @81
    @44
    adantr
    #
    wph
    @45
    @81
    etransclem44.m
    adantr
    #
    etransclem44.f
    @104
    @31
    @46
    @81
    @31
    wph
    @82
    adantl
    #
    @47
    syl
    #
    @95
    @96
    @104
    @31
    @17
    @8
    wcel
    @117
    @34
    syl
    #
    @81
    wph
    @31
    @17
    cr
    wcel
    @82
    @48
    sylan2
    etransclem37
    @104
    @97
    @98
    @107
    @113
    @114
    wb
    wph
    @97
    @81
    @99
    adantr
    @109
    @108
    @6
    @21
    dvdsval2
    syl3anc
    mpbid
    #
    zmulcld
    eqeltrd
    #
    fsumzcl
    eqeltrd
    wph
    cP
    @7
    cdvds
    wbr
    cP
    @87
    cdvds
    wbr
    #
    wph
    @122
    cP
    @0
    cdvds
    wbr
    #
    cP
    @86
    cdvds
    wbr
    #
    wo
    #
    wph
    @123
    wn
    #
    @124
    wn
    #
    wa
    @125
    wn
    wph
    @126
    @127
    wph
    @123
    cP
    @0
    cabs
    cfv
    #
    cdvds
    wbr
    #
    wph
    @42
    @128
    c1
    @1
    cfz
    co
    wcel
    #
    @129
    wn
    @44
    wph
    c1
    cz
    wcel
    #
    @58
    @128
    cz
    wcel
    #
    w3a
    #
    c1
    @128
    cle
    wbr
    #
    @128
    @1
    cle
    wbr
    #
    wa
    wa
    @130
    wph
    @133
    @134
    @135
    wph
    @131
    @58
    @132
    wph
    1zzd
    @66
    wph
    @0
    cz
    wcel
    #
    @132
    @74
    @0
    zabscl
    syl
    #
    3jca
    wph
    @128
    wph
    @128
    cn0
    wcel
    #
    @128
    cc0
    wne
    @128
    cn
    wcel
    wph
    @136
    @138
    @74
    @0
    nn0abscl
    syl
    wph
    @0
    @88
    etransclem44.a0
    absne0d
    @128
    elnnne0
    sylanbrc
    nnge1d
    wph
    @128
    cP
    clt
    wbr
    #
    @135
    etransclem44.ap
    wph
    @132
    cP
    cz
    wcel
    #
    @139
    @135
    wb
    @137
    @63
    @128
    cP
    zltlem1
    syl2anc
    mpbid
    jca32
    @128
    c1
    @1
    elfz2
    sylibr
    cP
    @128
    fzm1ndvds
    syl2anc
    wph
    @140
    @136
    @123
    @129
    wb
    @63
    @74
    cP
    @0
    dvdsabsb
    syl2anc
    mtbird
    wph
    vx
    cP
    vj
    cF
    cM
    etransclem44.m
    etransclem44.p
    etransclem44.mp
    etransclem44.f
    etransclem41
    jca
    @123
    @124
    pm4.56
    sylib
    wph
    @43
    @136
    @91
    @122
    @125
    wb
    etransclem44.p
    @74
    @100
    cP
    @0
    @86
    euclemma
    syl3anc
    mtbird
    wph
    @7
    @87
    cP
    cdvds
    @89
    breq2d
    mtbird
    wph
    cP
    @102
    @24
    cdvds
    wph
    @15
    @101
    vk
    cP
    @80
    @63
    @121
    @104
    cP
    @106
    @101
    cdvds
    @104
    @140
    @111
    @114
    w3a
    cP
    @105
    cdvds
    wbr
    cP
    @106
    cdvds
    wbr
    @104
    @140
    @111
    @114
    wph
    @140
    @81
    @63
    adantr
    @112
    @120
    3jca
    @104
    vx
    @93
    cP
    vj
    vn
    cF
    @19
    @17
    cM
    vc
    @115
    @116
    etransclem44.f
    @118
    @119
    @81
    @19
    @1
    wceq
    #
    @17
    cc0
    wceq
    #
    wa
    #
    wn
    wph
    @81
    @143
    @16
    @14
    wcel
    #
    @16
    @12
    @14
    eldifn
    @81
    @143
    wa
    #
    @67
    @144
    @145
    @16
    @17
    @19
    cop
    #
    @13
    @145
    @31
    @16
    @146
    wceq
    @81
    @31
    @143
    @82
    adantr
    @16
    @8
    @11
    1st2nd2
    syl
    @143
    @146
    @13
    wceq
    @81
    @143
    @17
    cc0
    @19
    @1
    @141
    @142
    simpr
    @141
    @142
    simpl
    opeq12d
    adantl
    eqtrd
    vk
    @13
    velsn
    sylibr
    mtand
    adantl
    @96
    etransclem38
    cP
    @18
    @105
    dvdsmultr2
    sylc
    @110
    breqtrrd
    fsumdvds
    @103
    breqtrrd
    etransclem9
    eqnetrd
end
