include "crp.mm"
include "c1.mm"
include "cv.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cmu.mm"
include "cdiv.mm"
include "csu.mm"
include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "wtru.mm"
include "cmin.mm"
include "cmul.mm"
include "caddc.mm"
include "cvv.mm"
include "1red.mm"
include "cof.mm"
include "cc.mm"
include "cr.mm"
include "reex.mm"
include "rpssre.mm"
include "ssexi.mm"
include "a1i.mm"
include "fzfid.mm"
include "wa.mm"
include "cn.mm"
include "rpre.mm"
include "elfznn.mm"
include "nndivre.mm"
include "syl2an.mm"
include "recnd.mm"
include "reflcl.mm"
include "syl.mm"
include "subcld.mm"
include "cz.mm"
include "adantl.mm"
include "mucl.mm"
include "zcnd.mm"
include "mulcld.mm"
include "fsumcl.mm"
include "rpcn.mm"
include "rpne0.mm"
include "divcld.mm"
include "ovexd.mm"
include "eqidd.mm"
include "offval2.mm"
include "wss.mm"
include "cle.mm"
include "wbr.mm"
include "cabs.mm"
include "adantr.mm"
include "cc0.mm"
include "wne.mm"
include "absdivd.mm"
include "wceq.mm"
include "rprege0.mm"
include "absid.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "abscld.mm"
include "adantlr.mm"
include "fsumrecl.mm"
include "fsumabs.mm"
include "ssriv.mm"
include "sselda.mm"
include "absmuld.mm"
include "absge0d.mm"
include "simpl.mm"
include "nnrpd.mm"
include "rpdivcl.mm"
include "sseldi.mm"
include "flle.mm"
include "abssubge0d.mm"
include "fracle1.mm"
include "eqbrtrd.mm"
include "mule1.mm"
include "lemul12ad.mm"
include "1t1e1.mm"
include "syl6breq.mm"
include "fsumle.mm"
include "chash.mm"
include "cfn.mm"
include "1cnd.mm"
include "fsumconst.mm"
include "syl2anc.mm"
include "cn0.mm"
include "flge1nn.mm"
include "sylan.mm"
include "nnnn0d.mm"
include "hashfz1.mm"
include "oveq1d.mm"
include "mulid1d.mm"
include "3eqtrd.mm"
include "breqtrd.mm"
include "letrd.mm"
include "breqtrrd.mm"
include "ledivmuld.mm"
include "mpbird.mm"
include "elo1d.mm"
include "crli.mm"
include "ax-1cn.mm"
include "divrcnv.mm"
include "ax-mp.mm"
include "rlimo1.mm"
include "mp1i.mm"
include "o1add.mm"
include "eqeltrrd.mm"
include "zred.mm"
include "nndivred.mm"
include "fsummulc2.mm"
include "fsumadd.mm"
include "npcand.mm"
include "adddird.mm"
include "rpcnne0.mm"
include "w3a.mm"
include "div23.mm"
include "divass.mm"
include "eqtr3d.mm"
include "syl3anc.mm"
include "3eqtr3d.mm"
include "sumeq2dv.mm"
include "cdvds.mm"
include "crab.mm"
include "ssrab2.mm"
include "simprr.mm"
include "dvdsflsumcom.mm"
include "3impb.mm"
include "2sumeq2dv.mm"
include "cuz.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "eluzfz1.mm"
include "musumsum.mm"
include "flge0nn0.mm"
include "4syl.mm"
include "3eqtr3rd.mm"
include "divcan3d.mm"
include "divdir.mm"
include "fveq2d.mm"
include "eqle.mm"
include "o1le.mm"
include "trud.mm"

theorem mudivsum
  let vx: setvar x
  let vn: setvar n
  let vk: setvar k
  let vm: setvar m
  let vy: setvar y

  disjoint n x
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint n y
  disjoint x y
  assert |- ( x e. RR+ |-> sum_ n e. ( 1 ... ( |_ ` x ) ) ( ( mmu ` n ) / n ) ) e. O(1)

  proof
    vx
    crp
    c1
    vx
    cv
    #
    cfl
    cfv
    #
    cfz
    co
    #
    vn
    cv
    #
    cmu
    cfv
    #
    @3
    cdiv
    co
    #
    vn
    csu
    #
    cmpt
    co1
    wcel
    wtru
    vx
    crp
    @2
    @0
    @3
    cdiv
    co
    #
    @7
    cfl
    cfv
    #
    cmin
    co
    #
    @4
    cmul
    co
    #
    vn
    csu
    #
    @0
    cdiv
    co
    #
    c1
    @0
    cdiv
    co
    #
    caddc
    co
    #
    @6
    c1
    cvv
    wtru
    1red
    #
    wtru
    vx
    crp
    @12
    cmpt
    #
    vx
    crp
    @13
    cmpt
    #
    caddc
    cof
    co
    #
    vx
    crp
    @14
    cmpt
    co1
    wtru
    vx
    crp
    @12
    @13
    caddc
    @16
    @17
    cvv
    cc
    cvv
    crp
    cvv
    wcel
    wtru
    crp
    cr
    reex
    rpssre
    ssexi
    a1i
    @0
    crp
    wcel
    #
    @12
    cc
    wcel
    wtru
    @19
    @11
    @0
    @19
    @2
    @10
    vn
    @19
    c1
    @1
    fzfid
    #
    @19
    @3
    @2
    wcel
    #
    wa
    #
    @9
    @4
    @22
    @7
    @8
    @22
    @7
    @19
    @0
    cr
    wcel
    #
    @3
    cn
    wcel
    #
    @7
    cr
    wcel
    #
    @21
    @0
    rpre
    #
    @3
    @1
    elfznn
    #
    @0
    @3
    nndivre
    syl2an
    #
    recnd
    #
    @22
    @8
    @22
    @25
    @8
    cr
    wcel
    #
    @28
    @7
    reflcl
    #
    syl
    recnd
    #
    subcld
    #
    @22
    @4
    @22
    @24
    @4
    cz
    wcel
    #
    @21
    @24
    @19
    @27
    adantl
    #
    @3
    mucl
    #
    syl
    #
    zcnd
    #
    mulcld
    #
    fsumcl
    #
    @0
    rpcn
    #
    @0
    rpne0
    #
    divcld
    adantl
    #
    wtru
    @19
    wa
    #
    c1
    @0
    cdiv
    ovexd
    wtru
    @16
    eqidd
    wtru
    @17
    eqidd
    offval2
    wtru
    @16
    co1
    wcel
    @17
    co1
    wcel
    #
    @18
    co1
    wcel
    wtru
    vx
    crp
    @12
    c1
    c1
    crp
    cr
    wss
    wtru
    rpssre
    a1i
    @43
    @15
    @15
    @19
    c1
    @0
    cle
    wbr
    #
    wa
    #
    @12
    cabs
    cfv
    #
    c1
    cle
    wbr
    wtru
    @47
    @48
    @11
    cabs
    cfv
    #
    @0
    cdiv
    co
    #
    c1
    cle
    @47
    @48
    @49
    @0
    cabs
    cfv
    #
    cdiv
    co
    @50
    @47
    @11
    @0
    @19
    @11
    cc
    wcel
    #
    @46
    @40
    adantr
    #
    @19
    @0
    cc
    wcel
    #
    @46
    @41
    adantr
    #
    @19
    @0
    cc0
    wne
    #
    @46
    @42
    adantr
    #
    absdivd
    @47
    @51
    @0
    @49
    cdiv
    @19
    @51
    @0
    wceq
    #
    @46
    @19
    @23
    cc0
    @0
    cle
    wbr
    wa
    @58
    @0
    rprege0
    @0
    absid
    syl
    adantr
    oveq2d
    eqtrd
    @47
    @50
    c1
    cle
    wbr
    @49
    @0
    c1
    cmul
    co
    #
    cle
    wbr
    @47
    @49
    @0
    @59
    cle
    @47
    @49
    @2
    @10
    cabs
    cfv
    #
    vn
    csu
    #
    @0
    @47
    @11
    @53
    abscld
    #
    @47
    @2
    @60
    vn
    @47
    c1
    @1
    fzfid
    #
    @47
    @21
    wa
    #
    @10
    @19
    @21
    @10
    cc
    wcel
    @46
    @39
    adantlr
    #
    abscld
    #
    fsumrecl
    #
    @19
    @23
    @46
    @26
    adantr
    #
    @47
    @2
    @10
    vn
    @63
    @65
    fsumabs
    @47
    @61
    @1
    @0
    @67
    @47
    @23
    @1
    cr
    wcel
    @68
    @0
    reflcl
    syl
    #
    @68
    @47
    @61
    @2
    c1
    vn
    csu
    #
    @1
    cle
    @47
    @2
    @60
    c1
    vn
    @63
    @66
    @64
    1red
    #
    @64
    @60
    @9
    cabs
    cfv
    #
    @4
    cabs
    cfv
    #
    cmul
    co
    #
    c1
    cle
    @64
    @9
    @4
    @19
    @21
    @9
    cc
    wcel
    @46
    @33
    adantlr
    #
    @64
    @4
    @64
    @24
    @34
    @47
    @2
    cn
    @3
    @2
    cn
    wss
    @47
    vk
    @2
    cn
    vk
    cv
    #
    @1
    elfznn
    ssriv
    a1i
    #
    sselda
    #
    @36
    syl
    zcnd
    #
    absmuld
    @64
    @74
    c1
    c1
    cmul
    co
    c1
    cle
    @64
    @72
    c1
    @73
    c1
    @64
    @9
    @75
    abscld
    @71
    @64
    @4
    @79
    abscld
    @71
    @64
    @9
    @75
    absge0d
    @64
    @4
    @79
    absge0d
    @64
    @72
    @9
    c1
    cle
    @64
    @8
    @7
    @64
    @25
    @30
    @64
    crp
    cr
    @7
    rpssre
    @47
    @19
    @3
    crp
    wcel
    #
    @7
    crp
    wcel
    #
    @21
    @19
    @46
    simpl
    #
    @21
    @3
    @27
    nnrpd
    @0
    @3
    rpdivcl
    syl2an
    #
    sseldi
    #
    @31
    syl
    @84
    @64
    @25
    @8
    @7
    cle
    wbr
    @84
    @7
    flle
    syl
    abssubge0d
    @64
    @25
    @9
    c1
    cle
    wbr
    @84
    @7
    fracle1
    syl
    eqbrtrd
    @64
    @24
    @73
    c1
    cle
    wbr
    @78
    @3
    mule1
    syl
    lemul12ad
    1t1e1
    syl6breq
    eqbrtrd
    fsumle
    @47
    @70
    @2
    chash
    cfv
    #
    c1
    cmul
    co
    #
    @1
    c1
    cmul
    co
    @1
    @47
    @2
    cfn
    wcel
    c1
    cc
    wcel
    #
    @70
    @86
    wceq
    @63
    @47
    1cnd
    #
    @2
    c1
    vn
    fsumconst
    syl2anc
    @47
    @85
    @1
    c1
    cmul
    @47
    @1
    cn0
    wcel
    @85
    @1
    wceq
    @47
    @1
    @19
    @23
    @46
    @1
    cn
    wcel
    @26
    @0
    flge1nn
    sylan
    #
    nnnn0d
    @1
    hashfz1
    syl
    oveq1d
    @47
    @1
    @47
    @1
    @69
    recnd
    mulid1d
    3eqtrd
    breqtrd
    @47
    @23
    @1
    @0
    cle
    wbr
    @68
    @0
    flle
    syl
    letrd
    letrd
    @47
    @0
    @55
    mulid1d
    breqtrrd
    @47
    @49
    c1
    @0
    @62
    @47
    1red
    @82
    ledivmuld
    mpbird
    eqbrtrd
    adantl
    elo1d
    @17
    cc0
    crli
    wbr
    #
    @45
    wtru
    @87
    @90
    ax-1cn
    c1
    vx
    divrcnv
    ax-mp
    cc0
    @17
    rlimo1
    mp1i
    @16
    @17
    o1add
    syl2anc
    eqeltrrd
    @44
    @12
    @13
    caddc
    ovexd
    @19
    @6
    cc
    wcel
    #
    wtru
    @19
    @2
    @5
    vn
    @20
    @22
    @5
    @22
    @4
    @3
    @22
    @4
    @37
    zred
    @35
    nndivred
    recnd
    #
    fsumcl
    #
    adantl
    @47
    @6
    cabs
    cfv
    #
    @14
    cabs
    cfv
    #
    cle
    wbr
    #
    wtru
    @47
    @94
    cr
    wcel
    @94
    @95
    wceq
    @96
    @47
    @6
    @19
    @91
    @46
    @93
    adantr
    #
    abscld
    @47
    @6
    @14
    cabs
    @47
    @0
    @6
    cmul
    co
    #
    @0
    cdiv
    co
    @11
    c1
    caddc
    co
    #
    @0
    cdiv
    co
    #
    @6
    @14
    @47
    @98
    @99
    @0
    cdiv
    @47
    @98
    @2
    @0
    @5
    cmul
    co
    #
    vn
    csu
    #
    @99
    @47
    @2
    @5
    @0
    vn
    @63
    @55
    @19
    @21
    @5
    cc
    wcel
    @46
    @92
    adantlr
    fsummulc2
    @47
    @2
    @10
    @8
    @4
    cmul
    co
    #
    caddc
    co
    #
    vn
    csu
    @11
    @2
    @103
    vn
    csu
    #
    caddc
    co
    @102
    @99
    @47
    @2
    @10
    @103
    vn
    @63
    @65
    @19
    @21
    @103
    cc
    wcel
    @46
    @22
    @8
    @4
    @32
    @38
    mulcld
    adantlr
    fsumadd
    @47
    @2
    @104
    @101
    vn
    @64
    @9
    @8
    caddc
    co
    #
    @4
    cmul
    co
    @7
    @4
    cmul
    co
    #
    @104
    @101
    @64
    @106
    @7
    @4
    cmul
    @64
    @7
    @8
    @19
    @21
    @7
    cc
    wcel
    @46
    @29
    adantlr
    @19
    @21
    @8
    cc
    wcel
    @46
    @32
    adantlr
    #
    npcand
    oveq1d
    @64
    @9
    @8
    @4
    @75
    @108
    @79
    adddird
    @64
    @54
    @4
    cc
    wcel
    #
    @3
    cc
    wcel
    @3
    cc0
    wne
    wa
    #
    @107
    @101
    wceq
    @47
    @54
    @21
    @55
    adantr
    @79
    @64
    @80
    @110
    @64
    @3
    @78
    nnrpd
    @3
    rpcnne0
    syl
    @54
    @109
    @110
    w3a
    @0
    @4
    cmul
    co
    @3
    cdiv
    co
    @107
    @101
    @0
    @4
    @3
    div23
    @0
    @4
    @3
    divass
    eqtr3d
    syl3anc
    3eqtr3d
    sumeq2dv
    @47
    @105
    c1
    @11
    caddc
    @47
    @2
    vy
    cv
    @76
    cdvds
    wbr
    #
    vy
    cn
    crab
    #
    @4
    vn
    csu
    vk
    csu
    #
    @2
    c1
    @8
    cfz
    co
    #
    @4
    vm
    csu
    #
    vn
    csu
    c1
    @105
    @47
    vy
    @0
    @4
    @4
    vm
    vk
    vn
    @76
    @3
    vm
    cv
    cmul
    co
    wceq
    @4
    eqidd
    @68
    @47
    @76
    @2
    wcel
    #
    @3
    @112
    wcel
    #
    wa
    wa
    #
    @4
    @118
    @24
    @34
    @118
    @112
    cn
    @3
    @111
    vy
    cn
    ssrab2
    @47
    @116
    @117
    simprr
    sseldi
    @36
    syl
    zcnd
    #
    dvdsflsumcom
    @47
    @2
    @112
    @4
    c1
    cmul
    co
    #
    vn
    csu
    vk
    csu
    @113
    c1
    @47
    @2
    @112
    @120
    @4
    vk
    vn
    @47
    @116
    @117
    w3a
    @4
    @47
    @116
    @117
    @109
    @119
    3impb
    mulid1d
    2sumeq2dv
    @47
    @2
    c1
    c1
    vn
    vk
    vy
    @76
    c1
    wceq
    c1
    eqidd
    @63
    @77
    @47
    @1
    c1
    cuz
    cfv
    #
    wcel
    c1
    @2
    wcel
    @47
    @1
    cn
    @121
    @89
    nnuz
    syl6eleq
    c1
    @1
    eluzfz1
    syl
    @47
    @116
    wa
    1cnd
    musumsum
    eqtr3d
    @47
    @2
    @115
    @103
    vn
    @64
    @115
    @114
    chash
    cfv
    #
    @4
    cmul
    co
    #
    @103
    @64
    @114
    cfn
    wcel
    @109
    @115
    @123
    wceq
    @64
    c1
    @8
    fzfid
    @79
    @114
    @4
    vm
    fsumconst
    syl2anc
    @64
    @122
    @8
    @4
    cmul
    @64
    @81
    @25
    cc0
    @7
    cle
    wbr
    wa
    @8
    cn0
    wcel
    @122
    @8
    wceq
    @83
    @7
    rprege0
    @7
    flge0nn0
    @8
    hashfz1
    4syl
    oveq1d
    eqtrd
    sumeq2dv
    3eqtr3rd
    oveq2d
    3eqtr3d
    eqtrd
    oveq1d
    @47
    @6
    @0
    @97
    @55
    @57
    divcan3d
    @47
    @52
    @87
    @54
    @56
    wa
    #
    @100
    @14
    wceq
    @53
    @88
    @19
    @124
    @46
    @0
    rpcnne0
    adantr
    @11
    c1
    @0
    divdir
    syl3anc
    3eqtr3d
    fveq2d
    @94
    @95
    eqle
    syl2anc
    adantl
    o1le
    trud
end
