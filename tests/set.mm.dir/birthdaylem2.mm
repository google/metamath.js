include "cn.mm"
include "wcel.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "cdiv.mm"
include "cmin.mm"
include "c1.mm"
include "caddc.mm"
include "cv.mm"
include "clog.mm"
include "csu.mm"
include "ce.mm"
include "cmul.mm"
include "cfa.mm"
include "cbc.mm"
include "wf1.mm"
include "cab.mm"
include "fveq2i.mm"
include "cfn.mm"
include "wceq.mm"
include "fzfi.mm"
include "hashf1.mm"
include "mp2an.mm"
include "eqtri.mm"
include "cn0.mm"
include "elfznn0.mm"
include "adantl.mm"
include "hashfz1.mm"
include "syl.mm"
include "fveq2d.mm"
include "nnnn0.mm"
include "adantr.mm"
include "oveq12d.mm"
include "syl5eq.mm"
include "faccl.mm"
include "nncnd.mm"
include "fznn0sub.mm"
include "nnne0d.mm"
include "divcld.mm"
include "divcan2d.mm"
include "bcval2.mm"
include "divdiv1d.mm"
include "eqtr4d.mm"
include "oveq2d.mm"
include "cc.mm"
include "fzfid.mm"
include "elfznn.mm"
include "nnrp.mm"
include "relogcld.mm"
include "recnd.mm"
include "fsumcl.mm"
include "efsub.mm"
include "syl2anc.mm"
include "clt.mm"
include "wbr.mm"
include "cin.mm"
include "c0.mm"
include "nn0red.mm"
include "ltp1d.mm"
include "fzdisj.mm"
include "cun.mm"
include "cle.mm"
include "fznn0sub2.mm"
include "elfzle2.mm"
include "cuz.mm"
include "cz.mm"
include "wb.mm"
include "simpr.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "nnz.mm"
include "ad2antrr.mm"
include "elfz5.mm"
include "mpbird.mm"
include "fzsplit.mm"
include "fz10.mm"
include "syl6eq.mm"
include "uneq1d.mm"
include "uncom.mm"
include "un0.mm"
include "oveq1d.mm"
include "1e0p1.mm"
include "syl6eqr.mm"
include "eqtr2d.mm"
include "wo.mm"
include "elnn0.mm"
include "sylib.mm"
include "mpjaodan.mm"
include "fsumsplit.mm"
include "nn0p1nn.mm"
include "elfzuz.mm"
include "eluznn.mm"
include "syl2an.mm"
include "pncan2d.mm"
include "wne.mm"
include "eflog.mm"
include "logfac.mm"
include "eqtr3d.mm"
include "3eqtr4d.mm"
include "eqtrd.mm"
include "cexp.mm"
include "cmap.mm"
include "wf.mm"
include "mapvalg.mm"
include "eqtr4i.mm"
include "hashmap.mm"
include "nncn.mm"
include "nnne0.mm"
include "elfzelz.mm"
include "explog.mm"
include "syl3anc.mm"
include "nn0cnd.mm"
include "crp.mm"
include "mulcld.mm"
include "relogdiv.mm"
include "syl2anr.mm"
include "syldan.mm"
include "sumeq2dv.mm"
include "nn0zd.mm"
include "peano2zd.mm"
include "rpdivcld.mm"
include "oveq1.mm"
include "fsumrev.mm"
include "subidd.mm"
include "1cnd.mm"
include "subsubd.mm"
include "ax-1cn.mm"
include "subcl.mm"
include "sylancl.mm"
include "nncand.mm"
include "divsubdird.mm"
include "dividd.mm"
include "sumeq12rdv.mm"
include "fsumsub.mm"
include "fsumconst.mm"
include "cen.mm"
include "1zzd.mm"
include "fzen.mm"
include "addcom.mm"
include "sylancr.mm"
include "pncan3d.mm"
include "breqtrd.mm"
include "hasheni.mm"
include "3eqtr3rd.mm"
include "3eqtr2d.mm"

theorem birthdaylem2
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vk: setvar k
  let cK: class K
  let cN: class N
  let vn: setvar n
  assume birthday.s: |- S = { f | f : ( 1 ... K ) --> ( 1 ... N ) }
  assume birthday.t: |- T = { f | f : ( 1 ... K ) -1-1-> ( 1 ... N ) }

  disjoint f k
  disjoint K f
  disjoint K k
  disjoint N f
  disjoint N k
  disjoint f n
  disjoint k n
  disjoint K n
  disjoint N n
  assert |- ( ( N e. NN /\ K e. ( 0 ... N ) ) -> ( ( # ` T ) / ( # ` S ) ) = ( exp ` sum_ k e. ( 0 ... ( K - 1 ) ) ( log ` ( 1 - ( k / N ) ) ) ) )

  proof
    cN
    cn
    wcel
    #
    cK
    cc0
    cN
    cfz
    co
    #
    wcel
    #
    wa
    #
    cT
    chash
    cfv
    #
    cS
    chash
    cfv
    #
    cdiv
    co
    cN
    cK
    cmin
    co
    #
    c1
    caddc
    co
    #
    cN
    cfz
    co
    #
    vn
    cv
    #
    clog
    cfv
    #
    vn
    csu
    #
    ce
    cfv
    #
    cK
    cN
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    cdiv
    co
    #
    @11
    @14
    cmin
    co
    #
    ce
    cfv
    #
    cc0
    cK
    c1
    cmin
    co
    #
    cfz
    co
    #
    c1
    vk
    cv
    #
    cN
    cdiv
    co
    #
    cmin
    co
    #
    clog
    cfv
    #
    vk
    csu
    #
    ce
    cfv
    @3
    @4
    @12
    @5
    @15
    cdiv
    @3
    @4
    cK
    cfa
    cfv
    #
    cN
    cK
    cbc
    co
    #
    cmul
    co
    #
    @12
    @3
    @4
    c1
    cK
    cfz
    co
    #
    chash
    cfv
    #
    cfa
    cfv
    #
    c1
    cN
    cfz
    co
    #
    chash
    cfv
    #
    @30
    cbc
    co
    #
    cmul
    co
    #
    @28
    @4
    @29
    @32
    vf
    cv
    #
    wf1
    vf
    cab
    #
    chash
    cfv
    #
    @35
    cT
    @37
    chash
    birthday.t
    fveq2i
    @29
    cfn
    wcel
    #
    @32
    cfn
    wcel
    #
    @38
    @35
    wceq
    c1
    cK
    fzfi
    #
    c1
    cN
    fzfi
    #
    @29
    @32
    vf
    hashf1
    mp2an
    eqtri
    @3
    @31
    @26
    @34
    @27
    cmul
    @3
    @30
    cK
    cfa
    @3
    cK
    cn0
    wcel
    #
    @30
    cK
    wceq
    @2
    @43
    @0
    cK
    cN
    elfznn0
    adantl
    #
    cK
    hashfz1
    syl
    #
    fveq2d
    @3
    @33
    cN
    @30
    cK
    cbc
    @0
    @33
    cN
    wceq
    #
    @2
    @0
    cN
    cn0
    wcel
    #
    @46
    cN
    nnnn0
    #
    cN
    hashfz1
    syl
    adantr
    #
    @45
    oveq12d
    oveq12d
    syl5eq
    @3
    @26
    cN
    cfa
    cfv
    #
    @6
    cfa
    cfv
    #
    cdiv
    co
    #
    @26
    cdiv
    co
    #
    cmul
    co
    @52
    @28
    @12
    @3
    @52
    @26
    @3
    @50
    @51
    @3
    @50
    @3
    @47
    @50
    cn
    wcel
    @0
    @47
    @2
    @48
    adantr
    #
    cN
    faccl
    syl
    #
    nncnd
    #
    @3
    @51
    @3
    @6
    cn0
    wcel
    #
    @51
    cn
    wcel
    @2
    @57
    @0
    cK
    cc0
    cN
    fznn0sub
    adantl
    #
    @6
    faccl
    syl
    #
    nncnd
    #
    @3
    @51
    @59
    nnne0d
    #
    divcld
    @3
    @26
    @3
    @43
    @26
    cn
    wcel
    @44
    cK
    faccl
    syl
    #
    nncnd
    #
    @3
    @26
    @62
    nnne0d
    #
    divcan2d
    @3
    @27
    @53
    @26
    cmul
    @3
    @27
    @50
    @51
    @26
    cmul
    co
    cdiv
    co
    #
    @53
    @2
    @27
    @65
    wceq
    @0
    cK
    cN
    bcval2
    adantl
    @3
    @50
    @51
    @26
    @56
    @60
    @63
    @61
    @64
    divdiv1d
    eqtr4d
    oveq2d
    @3
    @32
    @10
    vn
    csu
    #
    c1
    @6
    cfz
    co
    #
    @10
    vn
    csu
    #
    cmin
    co
    #
    ce
    cfv
    #
    @66
    ce
    cfv
    #
    @68
    ce
    cfv
    #
    cdiv
    co
    #
    @12
    @52
    @3
    @66
    cc
    wcel
    @68
    cc
    wcel
    @70
    @73
    wceq
    @3
    @32
    @10
    vn
    @3
    c1
    cN
    fzfid
    #
    @3
    @9
    @32
    wcel
    #
    wa
    @9
    cn
    wcel
    #
    @10
    cc
    wcel
    #
    @75
    @76
    @3
    @9
    cN
    elfznn
    adantl
    @76
    @10
    @76
    @9
    @9
    nnrp
    #
    relogcld
    recnd
    #
    syl
    #
    fsumcl
    @3
    @67
    @10
    vn
    @3
    c1
    @6
    fzfid
    @3
    @9
    @67
    wcel
    #
    wa
    @76
    @77
    @81
    @76
    @3
    @9
    @6
    elfznn
    adantl
    @79
    syl
    fsumcl
    #
    @66
    @68
    efsub
    syl2anc
    @3
    @11
    @69
    ce
    @3
    @69
    @68
    @11
    caddc
    co
    #
    @68
    cmin
    co
    @11
    @3
    @66
    @83
    @68
    cmin
    @3
    @67
    @8
    @10
    @32
    vn
    @3
    @6
    @7
    clt
    wbr
    @67
    @8
    cin
    c0
    wceq
    @3
    @6
    @3
    @6
    @58
    nn0red
    ltp1d
    c1
    @6
    @7
    cN
    fzdisj
    syl
    @3
    @6
    cn
    wcel
    #
    @32
    @67
    @8
    cun
    #
    wceq
    #
    @6
    cc0
    wceq
    #
    @3
    @84
    wa
    #
    @6
    @32
    wcel
    #
    @86
    @88
    @89
    @6
    cN
    cle
    wbr
    #
    @3
    @90
    @84
    @3
    @6
    @1
    wcel
    #
    @90
    @2
    @91
    @0
    cK
    cN
    fznn0sub2
    adantl
    @6
    cc0
    cN
    elfzle2
    syl
    adantr
    @88
    @6
    c1
    cuz
    cfv
    #
    wcel
    cN
    cz
    wcel
    #
    @89
    @90
    wb
    @88
    @6
    cn
    @92
    @3
    @84
    simpr
    nnuz
    syl6eleq
    @0
    @93
    @2
    @84
    cN
    nnz
    #
    ad2antrr
    @6
    c1
    cN
    elfz5
    syl2anc
    mpbird
    @6
    c1
    cN
    fzsplit
    syl
    @3
    @87
    wa
    #
    @85
    c0
    @8
    cun
    #
    @32
    @95
    @67
    c0
    @8
    @95
    @67
    c1
    cc0
    cfz
    co
    c0
    @95
    @6
    cc0
    c1
    cfz
    @3
    @87
    simpr
    #
    oveq2d
    fz10
    syl6eq
    uneq1d
    @95
    @96
    @8
    @32
    @96
    @8
    c0
    cun
    @8
    c0
    @8
    uncom
    @8
    un0
    eqtri
    @95
    @7
    c1
    cN
    cfz
    @95
    @7
    cc0
    c1
    caddc
    co
    c1
    @95
    @6
    cc0
    c1
    caddc
    @97
    oveq1d
    1e0p1
    syl6eqr
    oveq1d
    syl5eq
    eqtr2d
    @3
    @57
    @84
    @87
    wo
    @58
    @6
    elnn0
    sylib
    mpjaodan
    @74
    @80
    fsumsplit
    oveq1d
    @3
    @68
    @11
    @82
    @3
    @8
    @10
    vn
    @3
    @7
    cN
    fzfid
    #
    @3
    @9
    @8
    wcel
    #
    wa
    #
    @76
    @77
    @3
    @7
    cn
    wcel
    #
    @9
    @7
    cuz
    cfv
    wcel
    @76
    @99
    @3
    @57
    @101
    @58
    @6
    nn0p1nn
    syl
    @9
    @7
    cN
    elfzuz
    @9
    @7
    eluznn
    syl2an
    #
    @79
    syl
    #
    fsumcl
    #
    pncan2d
    eqtr2d
    fveq2d
    @3
    @50
    @71
    @51
    @72
    cdiv
    @3
    @50
    clog
    cfv
    #
    ce
    cfv
    #
    @50
    @71
    @3
    @50
    cc
    wcel
    @50
    cc0
    wne
    @106
    @50
    wceq
    @56
    @3
    @50
    @55
    nnne0d
    @50
    eflog
    syl2anc
    @3
    @105
    @66
    ce
    @3
    @47
    @105
    @66
    wceq
    @54
    vn
    cN
    logfac
    syl
    fveq2d
    eqtr3d
    @3
    @51
    clog
    cfv
    #
    ce
    cfv
    #
    @51
    @72
    @3
    @51
    cc
    wcel
    @51
    cc0
    wne
    @108
    @51
    wceq
    @60
    @61
    @51
    eflog
    syl2anc
    @3
    @107
    @68
    ce
    @3
    @57
    @107
    @68
    wceq
    @58
    vn
    @6
    logfac
    syl
    fveq2d
    eqtr3d
    oveq12d
    3eqtr4d
    3eqtr4d
    eqtrd
    @3
    @5
    cN
    cK
    cexp
    co
    #
    @15
    @3
    @5
    @33
    @30
    cexp
    co
    #
    @109
    @5
    @32
    @29
    cmap
    co
    #
    chash
    cfv
    #
    @110
    cS
    @111
    chash
    cS
    @29
    @32
    @36
    wf
    vf
    cab
    #
    @111
    birthday.s
    @40
    @39
    @111
    @113
    wceq
    @42
    @41
    @32
    @29
    cfn
    cfn
    vf
    mapvalg
    mp2an
    eqtr4i
    fveq2i
    @40
    @39
    @112
    @110
    wceq
    @42
    @41
    @32
    @29
    hashmap
    mp2an
    eqtri
    @3
    @33
    cN
    @30
    cK
    cexp
    @49
    @45
    oveq12d
    syl5eq
    @3
    cN
    cc
    wcel
    #
    cN
    cc0
    wne
    #
    cK
    cz
    wcel
    #
    @109
    @15
    wceq
    @0
    @114
    @2
    cN
    nncn
    adantr
    #
    @0
    @115
    @2
    cN
    nnne0
    adantr
    #
    @2
    @116
    @0
    cK
    cc0
    cN
    elfzelz
    adantl
    #
    cN
    cK
    explog
    syl3anc
    eqtrd
    oveq12d
    @3
    @11
    cc
    wcel
    @14
    cc
    wcel
    @18
    @16
    wceq
    @104
    @3
    cK
    @13
    @3
    cK
    @44
    nn0cnd
    #
    @3
    @13
    @3
    cN
    @0
    cN
    crp
    wcel
    #
    @2
    cN
    nnrp
    adantr
    #
    relogcld
    recnd
    #
    mulcld
    @11
    @14
    efsub
    syl2anc
    @3
    @17
    @25
    ce
    @3
    @8
    @9
    cN
    cdiv
    co
    #
    clog
    cfv
    #
    vn
    csu
    #
    @8
    @10
    @13
    cmin
    co
    #
    vn
    csu
    #
    @25
    @17
    @3
    @8
    @125
    @127
    vn
    @3
    @99
    @76
    @125
    @127
    wceq
    #
    @102
    @76
    @9
    crp
    wcel
    #
    @121
    @129
    @3
    @78
    @122
    @9
    cN
    relogdiv
    syl2anr
    syldan
    sumeq2dv
    @3
    @126
    cN
    cN
    cmin
    co
    #
    cN
    @7
    cmin
    co
    #
    cfz
    co
    #
    cN
    @21
    cmin
    co
    #
    cN
    cdiv
    co
    #
    clog
    cfv
    #
    vk
    csu
    @25
    @3
    @125
    @136
    vn
    vk
    cN
    @7
    cN
    @0
    @93
    @2
    @94
    adantr
    #
    @3
    @6
    @3
    @6
    @58
    nn0zd
    #
    peano2zd
    @137
    @100
    @125
    @100
    @124
    @100
    @9
    cN
    @100
    @76
    @130
    @102
    @78
    syl
    @3
    @121
    @99
    @122
    adantr
    rpdivcld
    relogcld
    recnd
    @9
    @134
    wceq
    @124
    @135
    clog
    @9
    @134
    cN
    cdiv
    oveq1
    fveq2d
    fsumrev
    @3
    @133
    @20
    @136
    @24
    vk
    @3
    @131
    cc0
    @132
    @19
    cfz
    @3
    cN
    @117
    subidd
    @3
    cN
    cN
    @19
    cmin
    co
    #
    cmin
    co
    @132
    @19
    @3
    @139
    @7
    cN
    cmin
    @3
    cN
    cK
    c1
    @117
    @120
    @3
    1cnd
    subsubd
    oveq2d
    @3
    cN
    @19
    @117
    @3
    cK
    cc
    wcel
    c1
    cc
    wcel
    #
    @19
    cc
    wcel
    @120
    ax-1cn
    cK
    c1
    subcl
    sylancl
    nncand
    eqtr3d
    oveq12d
    @3
    @21
    @20
    wcel
    #
    wa
    #
    @135
    @23
    clog
    @142
    @135
    cN
    cN
    cdiv
    co
    #
    @22
    cmin
    co
    @23
    @142
    cN
    @21
    cN
    @3
    @114
    @141
    @117
    adantr
    #
    @142
    @21
    @141
    @21
    cn0
    wcel
    @3
    @21
    @19
    elfznn0
    adantl
    nn0cnd
    @144
    @3
    @115
    @141
    @118
    adantr
    #
    divsubdird
    @142
    @143
    c1
    @22
    cmin
    @142
    cN
    @144
    @145
    dividd
    oveq1d
    eqtrd
    fveq2d
    sumeq12rdv
    eqtrd
    @3
    @128
    @11
    @8
    @13
    vn
    csu
    #
    cmin
    co
    @17
    @3
    @8
    @10
    @13
    vn
    @98
    @103
    @3
    @13
    cc
    wcel
    #
    @99
    @123
    adantr
    fsumsub
    @3
    @146
    @14
    @11
    cmin
    @3
    @146
    @8
    chash
    cfv
    #
    @13
    cmul
    co
    #
    @14
    @3
    @8
    cfn
    wcel
    @147
    @146
    @149
    wceq
    @98
    @123
    @8
    @13
    vn
    fsumconst
    syl2anc
    @3
    @148
    cK
    @13
    cmul
    @3
    @30
    @148
    cK
    @3
    @29
    @8
    cen
    wbr
    @30
    @148
    wceq
    @3
    @29
    c1
    @6
    caddc
    co
    #
    cK
    @6
    caddc
    co
    #
    cfz
    co
    #
    @8
    cen
    @3
    c1
    cz
    wcel
    @116
    @6
    cz
    wcel
    @29
    @152
    cen
    wbr
    @3
    1zzd
    @119
    @138
    @6
    c1
    cK
    fzen
    syl3anc
    @3
    @150
    @7
    @151
    cN
    cfz
    @3
    @140
    @6
    cc
    wcel
    @150
    @7
    wceq
    ax-1cn
    @3
    @6
    @58
    nn0cnd
    c1
    @6
    addcom
    sylancr
    @3
    cK
    cN
    @120
    @117
    pncan3d
    oveq12d
    breqtrd
    @29
    @8
    hasheni
    syl
    @45
    eqtr3d
    oveq1d
    eqtrd
    oveq2d
    eqtrd
    3eqtr3rd
    fveq2d
    3eqtr2d
end
