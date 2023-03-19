include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "c3.mm"
include "cexp.mm"
include "csu.mm"
include "c1.mm"
include "caddc.mm"
include "cbp.mm"
include "cmin.mm"
include "cdiv.mm"
include "c2.mm"
include "cmul.mm"
include "c4.mm"
include "wceq.mm"
include "3nn0.mm"
include "fsumkthpow.mm"
include "mpan.mm"
include "df-4.mm"
include "oveq1i.mm"
include "oveq12i.mm"
include "cdc.mm"
include "cneg.mm"
include "cc.mm"
include "nn0cn.mm"
include "peano2cn.mm"
include "syl.mm"
include "bpoly4.mm"
include "cn.mm"
include "4nn.mm"
include "0exp.mm"
include "ax-mp.mm"
include "3nn.mm"
include "oveq2i.mm"
include "2t0e0.mm"
include "eqtri.mm"
include "0m0e0.mm"
include "sq0.mm"
include "00id.mm"
include "0cn.mm"
include "df-neg.mm"
include "3eqtr4i.mm"
include "a1i.mm"
include "oveq12d.mm"
include "4nn0.mm"
include "expcl.mm"
include "mpan2.mm"
include "2cn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "subcld.mm"
include "sqcl.mm"
include "addcld.mm"
include "0nn0.mm"
include "deccl.mm"
include "nn0cni.mm"
include "nn0rei.mm"
include "10pos.mm"
include "declti.mm"
include "gt0ne0ii.mm"
include "reccli.mm"
include "subcl.mm"
include "sylancl.mm"
include "subneg.mm"
include "npcan.mm"
include "2p2e4.mm"
include "eqcomi.mm"
include "df-3.mm"
include "2nn0.mm"
include "expadd.mm"
include "mp3an23.mm"
include "1nn0.mm"
include "oveq2d.mm"
include "sqcld.mm"
include "mulid1d.mm"
include "eqcomd.mm"
include "exp1d.mm"
include "eqeltrd.mm"
include "mul12.mm"
include "mp3an2i.mm"
include "subdid.mm"
include "3eqtr4d.mm"
include "oveq1d.mm"
include "ax-1cn.mm"
include "adddi.mm"
include "mp3an3.mm"
include "syl2anc.mm"
include "eqtr4d.mm"
include "mp3an13.mm"
include "2t1e2.mm"
include "syl6eq.mm"
include "addsubass.mm"
include "2m1e1.mm"
include "eqtrd.mm"
include "subsub.mm"
include "binom21.mm"
include "addass.mm"
include "mvrraddd.mm"
include "3eqtr3d.mm"
include "mulcomd.mm"
include "3eqtrd.mm"
include "syl5eq.mm"
include "syl5eqr.mm"

theorem fsumcube
  let cT: class T
  let vk: setvar k

  disjoint T k
  assert |- ( T e. NN0 -> sum_ k e. ( 0 ... T ) ( k ^ 3 ) = ( ( ( T ^ 2 ) x. ( ( T + 1 ) ^ 2 ) ) / 4 ) )

  proof
    cT
    cn0
    wcel
    #
    cc0
    cT
    cfz
    co
    vk
    cv
    c3
    cexp
    co
    vk
    csu
    #
    c3
    c1
    caddc
    co
    #
    cT
    c1
    caddc
    co
    #
    cbp
    co
    #
    @2
    cc0
    cbp
    co
    #
    cmin
    co
    #
    @2
    cdiv
    co
    #
    cT
    c2
    cexp
    co
    #
    @3
    c2
    cexp
    co
    #
    cmul
    co
    #
    c4
    cdiv
    co
    #
    c3
    cn0
    wcel
    #
    @0
    @1
    @7
    wceq
    3nn0
    vk
    c3
    cT
    fsumkthpow
    mpan
    @0
    @7
    c4
    @3
    cbp
    co
    #
    c4
    cc0
    cbp
    co
    #
    cmin
    co
    #
    c4
    cdiv
    co
    @11
    @15
    @6
    c4
    @2
    cdiv
    @13
    @4
    @14
    @5
    cmin
    c4
    @2
    @3
    cbp
    df-4
    oveq1i
    c4
    @2
    cc0
    cbp
    df-4
    oveq1i
    oveq12i
    df-4
    oveq12i
    @0
    @15
    @10
    c4
    cdiv
    @0
    @15
    @3
    c4
    cexp
    co
    #
    c2
    @3
    c3
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    @9
    caddc
    co
    #
    c1
    c3
    cc0
    cdc
    #
    cdiv
    co
    #
    cmin
    co
    #
    @22
    cneg
    #
    cmin
    co
    #
    @23
    @22
    caddc
    co
    #
    @10
    @0
    @13
    @23
    @14
    @24
    cmin
    @0
    @3
    cc
    wcel
    #
    @13
    @23
    wceq
    @0
    cT
    cc
    wcel
    #
    @27
    cT
    nn0cn
    #
    cT
    peano2cn
    #
    syl
    @3
    bpoly4
    syl
    @14
    @24
    wceq
    @0
    cc0
    c4
    cexp
    co
    #
    c2
    cc0
    c3
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    cc0
    c2
    cexp
    co
    #
    caddc
    co
    #
    @22
    cmin
    co
    #
    cc0
    @22
    cmin
    co
    @14
    @24
    @36
    cc0
    @22
    cmin
    @36
    cc0
    cc0
    caddc
    co
    cc0
    @34
    cc0
    @35
    cc0
    caddc
    @34
    cc0
    cc0
    cmin
    co
    cc0
    @31
    cc0
    @33
    cc0
    cmin
    c4
    cn
    wcel
    @31
    cc0
    wceq
    4nn
    c4
    0exp
    ax-mp
    @33
    c2
    cc0
    cmul
    co
    cc0
    @32
    cc0
    c2
    cmul
    c3
    cn
    wcel
    @32
    cc0
    wceq
    3nn
    c3
    0exp
    ax-mp
    oveq2i
    2t0e0
    eqtri
    oveq12i
    0m0e0
    eqtri
    sq0
    oveq12i
    00id
    eqtri
    oveq1i
    cc0
    cc
    wcel
    @14
    @37
    wceq
    0cn
    cc0
    bpoly4
    ax-mp
    @22
    df-neg
    3eqtr4i
    a1i
    oveq12d
    @0
    @23
    cc
    wcel
    #
    @22
    cc
    wcel
    #
    @25
    @26
    wceq
    @0
    @20
    cc
    wcel
    #
    @39
    @38
    @0
    @28
    @40
    @29
    @28
    @27
    @40
    @30
    @27
    @19
    @9
    @27
    @16
    @18
    @27
    c4
    cn0
    wcel
    @16
    cc
    wcel
    4nn0
    @3
    c4
    expcl
    mpan2
    @27
    c2
    cc
    wcel
    #
    @17
    cc
    wcel
    #
    @18
    cc
    wcel
    2cn
    @27
    @12
    @42
    3nn0
    @3
    c3
    expcl
    mpan2
    c2
    @17
    mulcl
    sylancr
    subcld
    @3
    sqcl
    addcld
    syl
    #
    syl
    @21
    @21
    c3
    cc0
    3nn0
    0nn0
    deccl
    #
    nn0cni
    @21
    @21
    @44
    nn0rei
    c3
    cc0
    cc0
    3nn
    0nn0
    0nn0
    10pos
    declti
    gt0ne0ii
    reccli
    #
    @20
    @22
    subcl
    sylancl
    @45
    @23
    @22
    subneg
    sylancl
    @0
    @26
    @20
    @10
    @0
    @28
    @26
    @20
    wceq
    #
    @29
    @28
    @40
    @39
    @46
    @43
    @45
    @20
    @22
    npcan
    sylancl
    syl
    @0
    @20
    @3
    c2
    c2
    caddc
    co
    #
    cexp
    co
    #
    c2
    @3
    c2
    c1
    caddc
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    @9
    caddc
    co
    #
    @10
    @19
    @52
    @9
    caddc
    @16
    @48
    @18
    @51
    cmin
    c4
    @47
    @3
    cexp
    @47
    c4
    2p2e4
    eqcomi
    oveq2i
    @17
    @50
    c2
    cmul
    c3
    @49
    @3
    cexp
    df-3
    oveq2i
    oveq2i
    oveq12i
    oveq1i
    @0
    @28
    @53
    @10
    wceq
    @29
    @28
    @53
    @9
    @9
    cmul
    co
    #
    c2
    @9
    @3
    c1
    cexp
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    @9
    c1
    cmul
    co
    #
    caddc
    co
    #
    @10
    @28
    @52
    @58
    @9
    @59
    caddc
    @28
    @27
    @52
    @58
    wceq
    @30
    @27
    @48
    @54
    @51
    @57
    cmin
    @27
    c2
    cn0
    wcel
    #
    @61
    @48
    @54
    wceq
    2nn0
    2nn0
    @3
    c2
    c2
    expadd
    mp3an23
    @27
    @50
    @56
    c2
    cmul
    @27
    @61
    c1
    cn0
    wcel
    @50
    @56
    wceq
    2nn0
    1nn0
    @3
    c2
    c1
    expadd
    mp3an23
    oveq2d
    oveq12d
    syl
    @28
    @59
    @9
    @28
    @9
    @28
    @3
    @30
    sqcld
    #
    mulid1d
    eqcomd
    oveq12d
    @28
    @60
    @9
    @9
    c2
    @3
    cmul
    co
    #
    cmin
    co
    #
    c1
    caddc
    co
    #
    cmul
    co
    #
    @9
    @8
    cmul
    co
    @10
    @28
    @60
    @9
    @64
    cmul
    co
    #
    @59
    caddc
    co
    #
    @66
    @28
    @58
    @67
    @59
    caddc
    @28
    @54
    @9
    c2
    @55
    cmul
    co
    #
    cmul
    co
    #
    cmin
    co
    @54
    @9
    @63
    cmul
    co
    #
    cmin
    co
    @58
    @67
    @28
    @70
    @71
    @54
    cmin
    @28
    @69
    @63
    @9
    cmul
    @28
    @55
    @3
    c2
    cmul
    @28
    @3
    @30
    exp1d
    #
    oveq2d
    oveq2d
    oveq2d
    @28
    @57
    @70
    @54
    cmin
    @41
    @28
    @9
    cc
    wcel
    #
    @55
    cc
    wcel
    @57
    @70
    wceq
    2cn
    @62
    @28
    @55
    @3
    cc
    @72
    @30
    eqeltrd
    c2
    @9
    @55
    mul12
    mp3an2i
    oveq2d
    @28
    @9
    @9
    @63
    @62
    @62
    @28
    @41
    @27
    @63
    cc
    wcel
    #
    2cn
    @30
    c2
    @3
    mulcl
    sylancr
    #
    subdid
    3eqtr4d
    oveq1d
    @28
    @73
    @64
    cc
    wcel
    #
    @66
    @68
    wceq
    #
    @62
    @28
    @9
    @63
    @62
    @75
    subcld
    @73
    @76
    c1
    cc
    wcel
    #
    @77
    ax-1cn
    @9
    @64
    c1
    adddi
    mp3an3
    syl2anc
    eqtr4d
    @28
    @65
    @8
    @9
    cmul
    @28
    @9
    @63
    c1
    cmin
    co
    #
    cmin
    co
    #
    @9
    c2
    cT
    cmul
    co
    #
    c1
    caddc
    co
    #
    cmin
    co
    @65
    @8
    @28
    @79
    @82
    @9
    cmin
    @28
    @79
    @81
    c2
    caddc
    co
    #
    c1
    cmin
    co
    #
    @82
    @28
    @63
    @83
    c1
    cmin
    @28
    @63
    @81
    c2
    c1
    cmul
    co
    #
    caddc
    co
    #
    @83
    @41
    @28
    @78
    @63
    @86
    wceq
    2cn
    ax-1cn
    c2
    cT
    c1
    adddi
    mp3an13
    @85
    c2
    @81
    caddc
    2t1e2
    oveq2i
    syl6eq
    oveq1d
    @28
    @84
    @81
    c2
    c1
    cmin
    co
    #
    caddc
    co
    #
    @82
    @28
    @81
    cc
    wcel
    #
    @84
    @88
    wceq
    #
    @41
    @28
    @89
    2cn
    c2
    cT
    mulcl
    mpan
    #
    @89
    @41
    @78
    @90
    2cn
    ax-1cn
    @81
    c2
    c1
    addsubass
    mp3an23
    syl
    @87
    c1
    @81
    caddc
    2m1e1
    oveq2i
    syl6eq
    eqtrd
    oveq2d
    @28
    @73
    @74
    @80
    @65
    wceq
    #
    @62
    @75
    @73
    @74
    @78
    @92
    ax-1cn
    @9
    @63
    c1
    subsub
    mp3an3
    syl2anc
    @28
    @9
    @8
    @82
    cT
    sqcl
    #
    @28
    @89
    @82
    cc
    wcel
    @91
    @81
    peano2cn
    syl
    @28
    @9
    @8
    @81
    caddc
    co
    c1
    caddc
    co
    #
    @8
    @82
    caddc
    co
    #
    cT
    binom21
    @28
    @8
    cc
    wcel
    #
    @89
    @94
    @95
    wceq
    #
    @93
    @91
    @96
    @89
    @78
    @97
    ax-1cn
    @8
    @81
    c1
    addass
    mp3an3
    syl2anc
    eqtrd
    mvrraddd
    3eqtr3d
    oveq2d
    @28
    @9
    @8
    @62
    @93
    mulcomd
    3eqtrd
    eqtrd
    syl
    syl5eq
    eqtrd
    3eqtrd
    oveq1d
    syl5eqr
    eqtrd
end
