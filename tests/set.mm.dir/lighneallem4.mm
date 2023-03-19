include "cprime.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "cn.mm"
include "w3a.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "wceq.mm"
include "wi.mm"
include "caddc.mm"
include "cc.mm"
include "wb.mm"
include "2cnd.mm"
include "nnnn0.mm"
include "expcld.mm"
include "3ad2ant3.mm"
include "1cnd.mm"
include "eldifi.mm"
include "prmnn.mm"
include "nncn.mm"
include "3syl.mm"
include "3ad2ant1.mm"
include "cn0.mm"
include "3ad2ant2.mm"
include "3jca.mm"
include "adantr.mm"
include "subadd2.mm"
include "syl.mm"
include "cc0.mm"
include "cfz.mm"
include "cneg.mm"
include "cv.mm"
include "cmul.mm"
include "csu.mm"
include "simpl2.mm"
include "simpr.mm"
include "oddpwp1fsum.mm"
include "eqeq1d.mm"
include "cz.mm"
include "peano2nn.mm"
include "nnzd.mm"
include "fzfid.mm"
include "neg1z.mm"
include "a1i.mm"
include "elfznn0.mm"
include "zexpcl.mm"
include "syl2an.mm"
include "nnz.mm"
include "zmulcld.mm"
include "fsumzcl.mm"
include "jca.mm"
include "ad2antrr.mm"
include "dvdsmul2.mm"
include "breq2.mm"
include "adantl.mm"
include "2a1.mm"
include "wrex.mm"
include "cuz.mm"
include "cfv.mm"
include "2prm.mm"
include "prmuz2.mm"
include "wne.mm"
include "df-ne.mm"
include "eluz2b3.mm"
include "simplbi2.mm"
include "syl5bir.mm"
include "com12.mm"
include "impcom.mm"
include "simprr.mm"
include "lighneallem4b.mm"
include "syl3anc.mm"
include "dvdsprmpweqnn.mm"
include "mp3an2i.mm"
include "2z.mm"
include "iddvdsexp.mm"
include "sylan.mm"
include "nn0expcld.mm"
include "nn0zd.mm"
include "ex.mm"
include "impel.mm"
include "wo.mm"
include "cpr.mm"
include "nn0z.mm"
include "m1expcl2.mm"
include "ovex.mm"
include "elpr.mm"
include "n2dvdsm1.mm"
include "mtbiri.mm"
include "n2dvds1.mm"
include "jaoi.mm"
include "a1d.mm"
include "sylbi.mm"
include "mpcom.mm"
include "elnn0.mm"
include "oddn2prm.mm"
include "prmdvdsexp.mm"
include "mp3an2ani.mm"
include "mtbird.mm"
include "expcom.mm"
include "oveq2.mm"
include "exp0d.mm"
include "eqtrd.mm"
include "breq2d.mm"
include "ioran.mm"
include "sylanbrc.mm"
include "mpan.mm"
include "euclemma.mm"
include "chash.mm"
include "nnm1nn0.mm"
include "hashfz0.mm"
include "npcan1.mm"
include "eqtr2d.mm"
include "notbid.mm"
include "biimpd.mm"
include "impr.mm"
include "oddsumodd.mm"
include "pm2.21d.mm"
include "sylbird.mm"
include "mpid.mm"
include "rexlimdva.mm"
include "syld.mm"
include "exp32.mm"
include "impd.mm"
include "pm2.61i.mm"
include "sylbid.mm"
include "mpd.mm"
include "adantld.mm"
include "3imp.mm"

theorem lighneallem4
  let cP: class P
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x


  assert |- ( ( ( P e. ( Prime \ { 2 } ) /\ M e. NN /\ N e. NN ) /\ ( -. 2 || N /\ -. 2 || M ) /\ ( ( 2 ^ N ) - 1 ) = ( P ^ M ) ) -> M = 1 )

  proof
    cP
    cprime
    c2
    csn
    #
    cdif
    wcel
    #
    cM
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    w3a
    #
    c2
    cN
    cdvds
    wbr
    wn
    #
    c2
    cM
    cdvds
    wbr
    #
    wn
    #
    wa
    c2
    cN
    cexp
    co
    #
    c1
    cmin
    co
    cP
    cM
    cexp
    co
    #
    wceq
    #
    cM
    c1
    wceq
    #
    @4
    @7
    @10
    @11
    wi
    #
    @5
    @4
    @7
    @12
    @4
    @7
    wa
    #
    @10
    @9
    c1
    caddc
    co
    #
    @8
    wceq
    #
    @11
    @13
    @8
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @9
    cc
    wcel
    #
    w3a
    #
    @10
    @15
    wb
    @4
    @19
    @7
    @4
    @16
    @17
    @18
    @3
    @1
    @16
    @2
    @3
    c2
    cN
    @3
    2cnd
    cN
    nnnn0
    #
    expcld
    3ad2ant3
    @4
    1cnd
    @4
    cP
    cM
    @1
    @2
    cP
    cc
    wcel
    #
    @3
    @1
    cP
    cprime
    wcel
    #
    cP
    cn
    wcel
    #
    @21
    cP
    cprime
    @0
    eldifi
    #
    cP
    prmnn
    #
    cP
    nncn
    3syl
    #
    3ad2ant1
    #
    @2
    @1
    cM
    cn0
    wcel
    @3
    cM
    nnnn0
    3ad2ant2
    expcld
    3jca
    adantr
    @8
    c1
    @9
    subadd2
    syl
    @13
    @15
    cP
    c1
    caddc
    co
    #
    cc0
    cM
    c1
    cmin
    co
    #
    cfz
    co
    #
    c1
    cneg
    #
    vk
    cv
    #
    cexp
    co
    #
    cP
    @32
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cmul
    co
    #
    @8
    wceq
    #
    @11
    @13
    @14
    @37
    @8
    @13
    cP
    vk
    cM
    @4
    @21
    @7
    @27
    adantr
    @1
    @2
    @3
    @7
    simpl2
    @4
    @7
    simpr
    oddpwp1fsum
    eqeq1d
    @13
    @38
    @11
    @13
    @38
    wa
    #
    @36
    @37
    cdvds
    wbr
    #
    @11
    @39
    @28
    cz
    wcel
    #
    @36
    cz
    wcel
    #
    wa
    #
    @40
    @4
    @43
    @7
    @38
    @4
    @41
    @42
    @1
    @2
    @41
    @3
    @1
    @22
    @23
    @41
    @24
    @25
    @23
    @28
    cP
    peano2nn
    nnzd
    3syl
    3ad2ant1
    @4
    @30
    @35
    vk
    @4
    cc0
    @29
    fzfid
    @4
    @32
    @30
    wcel
    #
    wa
    @33
    @34
    @4
    @31
    cz
    wcel
    #
    @32
    cn0
    wcel
    #
    @33
    cz
    wcel
    #
    @44
    @45
    @4
    neg1z
    a1i
    @32
    @29
    elfznn0
    #
    @31
    @32
    zexpcl
    #
    syl2an
    @4
    cP
    cz
    wcel
    #
    @46
    @34
    cz
    wcel
    #
    @44
    @1
    @2
    @50
    @3
    @1
    @22
    @23
    @50
    @24
    @25
    cP
    nnz
    3syl
    #
    3ad2ant1
    @48
    cP
    @32
    zexpcl
    syl2an
    zmulcld
    fsumzcl
    jca
    ad2antrr
    @28
    @36
    dvdsmul2
    syl
    @39
    @40
    @36
    @8
    cdvds
    wbr
    #
    @11
    @38
    @40
    @53
    wb
    @13
    @37
    @8
    @36
    cdvds
    breq2
    adantl
    @13
    @53
    @11
    wi
    #
    @38
    @11
    @13
    @54
    wi
    @11
    @13
    @53
    2a1
    @11
    wn
    #
    @4
    @7
    @54
    @4
    @55
    @7
    @54
    wi
    @4
    @55
    @7
    @54
    @4
    @55
    @7
    wa
    #
    wa
    #
    @53
    @36
    c2
    vn
    cv
    #
    cexp
    co
    #
    wceq
    #
    vn
    cn
    wrex
    #
    @11
    c2
    cprime
    wcel
    #
    @57
    @36
    c2
    cuz
    cfv
    #
    wcel
    #
    cN
    cn0
    wcel
    #
    @53
    @61
    wi
    2prm
    @57
    cP
    @63
    wcel
    #
    cM
    @63
    wcel
    #
    @7
    @64
    @4
    @66
    @56
    @1
    @2
    @66
    @3
    @1
    @22
    @66
    @24
    cP
    prmuz2
    syl
    3ad2ant1
    adantr
    @56
    @4
    @67
    @55
    @4
    @67
    wi
    @7
    @4
    @55
    @67
    @2
    @1
    @55
    @67
    wi
    @3
    @55
    cM
    c1
    wne
    #
    @2
    @67
    cM
    c1
    df-ne
    @67
    @2
    @68
    cM
    eluz2b3
    simplbi2
    syl5bir
    3ad2ant2
    com12
    adantr
    impcom
    @4
    @55
    @7
    simprr
    cP
    vk
    cM
    lighneallem4b
    syl3anc
    @4
    @65
    @56
    @3
    @1
    @65
    @2
    @20
    3ad2ant3
    adantr
    @36
    c2
    vn
    cN
    dvdsprmpweqnn
    mp3an2i
    @57
    @60
    @11
    vn
    cn
    @57
    @58
    cn
    wcel
    #
    wa
    #
    @60
    c2
    @59
    cdvds
    wbr
    #
    @11
    @57
    c2
    cz
    wcel
    #
    @69
    @71
    @72
    @57
    2z
    a1i
    c2
    @58
    iddvdsexp
    sylan
    @70
    @60
    @71
    @11
    wi
    @70
    @60
    wa
    @71
    c2
    @36
    cdvds
    wbr
    #
    @11
    @60
    @73
    @71
    wb
    @70
    @36
    @59
    c2
    cdvds
    breq2
    adantl
    @70
    @73
    @11
    wi
    @60
    @70
    @73
    @11
    @70
    @30
    @35
    vk
    @70
    cc0
    @29
    fzfid
    @70
    @46
    @35
    cz
    wcel
    #
    @44
    @4
    @46
    @74
    wi
    #
    @56
    @69
    @1
    @2
    @75
    @3
    @1
    @22
    @23
    @75
    @24
    @25
    @23
    @46
    @74
    @23
    @46
    wa
    #
    @33
    @34
    @23
    @45
    @46
    @47
    @45
    @23
    neg1z
    a1i
    @49
    sylan
    @76
    @34
    @76
    cP
    @32
    @23
    cP
    cn0
    wcel
    #
    @46
    cP
    nnnn0
    #
    adantr
    @23
    @46
    simpr
    nn0expcld
    nn0zd
    zmulcld
    ex
    3syl
    3ad2ant1
    ad2antrr
    @48
    impel
    @70
    @46
    c2
    @35
    cdvds
    wbr
    #
    wn
    #
    @44
    @4
    @46
    @80
    wi
    #
    @56
    @69
    @1
    @2
    @81
    @3
    @1
    @46
    @80
    @1
    @46
    wa
    #
    @79
    c2
    @33
    cdvds
    wbr
    #
    c2
    @34
    cdvds
    wbr
    #
    wo
    #
    @82
    @83
    wn
    #
    @84
    wn
    #
    @85
    wn
    @46
    @86
    @1
    @33
    @31
    c1
    cpr
    wcel
    #
    @46
    @86
    @46
    @32
    cz
    wcel
    @88
    @32
    nn0z
    @32
    m1expcl2
    syl
    @88
    @33
    @31
    wceq
    #
    @33
    c1
    wceq
    #
    wo
    #
    @46
    @86
    wi
    @33
    @31
    c1
    @31
    @32
    cexp
    ovex
    elpr
    @91
    @86
    @46
    @89
    @86
    @90
    @89
    @83
    c2
    @31
    cdvds
    wbr
    n2dvdsm1
    @33
    @31
    c2
    cdvds
    breq2
    mtbiri
    @90
    @83
    c2
    c1
    cdvds
    wbr
    #
    n2dvds1
    @33
    c1
    c2
    cdvds
    breq2
    mtbiri
    jaoi
    a1d
    sylbi
    mpcom
    adantl
    @46
    @1
    @87
    @46
    @32
    cn
    wcel
    #
    @32
    cc0
    wceq
    #
    wo
    @1
    @87
    wi
    #
    @32
    elnn0
    @93
    @95
    @94
    @1
    @93
    @87
    @1
    @93
    wa
    @84
    c2
    cP
    cdvds
    wbr
    #
    @1
    @96
    wn
    @93
    cP
    oddn2prm
    adantr
    @62
    @1
    @50
    @93
    @93
    @84
    @96
    wb
    2prm
    @52
    @1
    @93
    simpr
    cP
    c2
    @32
    prmdvdsexp
    mp3an2ani
    mtbird
    expcom
    @94
    @1
    @87
    @94
    @1
    wa
    #
    @84
    @92
    n2dvds1
    @97
    @34
    c1
    c2
    cdvds
    @97
    @34
    cP
    cc0
    cexp
    co
    #
    c1
    @94
    @34
    @98
    wceq
    @1
    @32
    cc0
    cP
    cexp
    oveq2
    adantr
    @97
    cP
    @1
    @21
    @94
    @26
    adantl
    exp0d
    eqtrd
    breq2d
    mtbiri
    ex
    jaoi
    sylbi
    impcom
    @83
    @84
    ioran
    sylanbrc
    @62
    @82
    @47
    @51
    @79
    @85
    wb
    2prm
    @46
    @47
    @1
    @45
    @46
    @47
    neg1z
    @49
    mpan
    adantl
    @82
    @34
    @82
    cP
    @32
    @1
    @77
    @46
    @1
    @22
    @23
    @77
    @24
    @25
    @78
    3syl
    adantr
    @1
    @46
    simpr
    nn0expcld
    nn0zd
    c2
    @33
    @34
    euclemma
    mp3an2i
    mtbird
    ex
    3ad2ant1
    ad2antrr
    @48
    impel
    @57
    c2
    @30
    chash
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    @69
    @4
    @55
    @7
    @101
    @4
    @55
    wa
    #
    @7
    @101
    @102
    @6
    @100
    @102
    cM
    @99
    c2
    cdvds
    @4
    cM
    @99
    wceq
    #
    @55
    @2
    @1
    @103
    @3
    @2
    @99
    @29
    c1
    caddc
    co
    #
    cM
    @2
    @29
    cn0
    wcel
    @99
    @104
    wceq
    cM
    nnm1nn0
    @29
    hashfz0
    syl
    @2
    cM
    cc
    wcel
    @104
    cM
    wceq
    cM
    nncn
    cM
    npcan1
    syl
    eqtr2d
    3ad2ant2
    adantr
    breq2d
    notbid
    biimpd
    impr
    adantr
    oddsumodd
    pm2.21d
    adantr
    sylbird
    ex
    mpid
    rexlimdva
    syld
    exp32
    com12
    impd
    pm2.61i
    adantr
    sylbid
    mpd
    ex
    sylbid
    sylbid
    ex
    adantld
    3imp
end
