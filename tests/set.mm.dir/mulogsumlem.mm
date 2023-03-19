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
include "clog.mm"
include "cmin.mm"
include "cmul.mm"
include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "wtru.mm"
include "cem.mm"
include "cc.mm"
include "fzfid.mm"
include "wa.mm"
include "cn.mm"
include "cz.mm"
include "elfznn.mm"
include "adantl.mm"
include "mucl.mm"
include "syl.mm"
include "zred.mm"
include "nndivred.mm"
include "recnd.mm"
include "fsumcl.mm"
include "emre.mm"
include "recni.mm"
include "a1i.mm"
include "mudivsum.mm"
include "cr.mm"
include "wss.mm"
include "rpssre.mm"
include "o1const.mm"
include "mp2an.mm"
include "o1mul2.mm"
include "nnrecred.mm"
include "fsumrecl.mm"
include "nnrpd.mm"
include "rpdivcl.mm"
include "sylan2.mm"
include "relogcld.mm"
include "resubcld.mm"
include "remulcld.mm"
include "mulcl.mm"
include "sylancl.mm"
include "caddc.mm"
include "nnrecre.mm"
include "subcld.mm"
include "mulcld.mm"
include "fsumsub.mm"
include "subsub4d.mm"
include "oveq2d.mm"
include "subdid.mm"
include "eqtr3d.mm"
include "sumeq2dv.mm"
include "fsummulc1.mm"
include "3eqtr4d.mm"
include "mpteq2ia.mm"
include "addcld.mm"
include "1red.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "abscld.mm"
include "fsumabs.mm"
include "cc0.mm"
include "cn0.mm"
include "rprege0.mm"
include "flge0nn0.mm"
include "nn0red.mm"
include "rerpdivcl.mm"
include "mpancom.mm"
include "rpreccl.mm"
include "adantr.mm"
include "rpred.mm"
include "id.mm"
include "syl2anr.mm"
include "absge0d.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "absdivd.mm"
include "wceq.mm"
include "absid.mm"
include "eqtrd.mm"
include "mule1.mm"
include "lediv1dd.mm"
include "eqbrtrd.mm"
include "harmonicbnd4.mm"
include "wne.mm"
include "rpcnne0.mm"
include "recdiv.mm"
include "syl2anc.mm"
include "breqtrd.mm"
include "lemul12ad.mm"
include "absmuld.mm"
include "1cnd.mm"
include "dmdcan.mm"
include "syl3anc.mm"
include "rpcnd.mm"
include "mulcomd.mm"
include "3brtr4d.mm"
include "fsumle.mm"
include "chash.mm"
include "hashfz1.mm"
include "oveq1d.mm"
include "cfn.mm"
include "fsumconst.mm"
include "nn0cnd.mm"
include "rpcn.mm"
include "rpne0.mm"
include "divrecd.mm"
include "rpre.mm"
include "flle.mm"
include "mulid1d.mm"
include "breqtrrd.mm"
include "clt.mm"
include "wb.mm"
include "reflcl.mm"
include "rpregt0.mm"
include "ledivmul.mm"
include "mpbird.mm"
include "letrd.mm"
include "ad2antrl.mm"
include "elo1d.mm"
include "syl5eqelr.mm"
include "o1dif.mm"
include "trud.mm"

theorem mulogsumlem
  let vx: setvar x
  let vm: setvar m
  let vn: setvar n
  let vk: setvar k
  let vy: setvar y

  disjoint m n
  disjoint m x
  disjoint n x
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint m y
  disjoint n y
  disjoint x y
  assert |- ( x e. RR+ |-> sum_ n e. ( 1 ... ( |_ ` x ) ) ( ( ( mmu ` n ) / n ) x. ( sum_ m e. ( 1 ... ( |_ ` ( x / n ) ) ) ( 1 / m ) - ( log ` ( x / n ) ) ) ) ) e. O(1)

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
    c1
    @0
    @3
    cdiv
    co
    #
    cfl
    cfv
    #
    cfz
    co
    #
    c1
    vm
    cv
    #
    cdiv
    co
    #
    vm
    csu
    #
    @6
    clog
    cfv
    #
    cmin
    co
    #
    cmul
    co
    #
    vn
    csu
    #
    cmpt
    co1
    wcel
    #
    wtru
    @16
    vx
    crp
    @2
    @5
    vn
    csu
    #
    cem
    cmul
    co
    #
    cmpt
    co1
    wcel
    wtru
    vx
    crp
    @17
    cem
    cc
    @0
    crp
    wcel
    #
    @17
    cc
    wcel
    #
    wtru
    @19
    @2
    @5
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
    @5
    @23
    @4
    @3
    @23
    @4
    @23
    @3
    cn
    wcel
    #
    @4
    cz
    wcel
    @22
    @24
    @19
    @3
    @1
    elfznn
    #
    adantl
    #
    @3
    mucl
    syl
    zred
    #
    @26
    nndivred
    #
    recnd
    #
    fsumcl
    #
    adantl
    cem
    cc
    wcel
    #
    wtru
    @19
    wa
    cem
    emre
    recni
    #
    a1i
    vx
    crp
    @17
    cmpt
    co1
    wcel
    wtru
    vx
    vn
    mudivsum
    a1i
    vx
    crp
    cem
    cmpt
    co1
    wcel
    #
    wtru
    crp
    cr
    wss
    #
    @31
    @33
    rpssre
    @32
    vx
    crp
    cem
    o1const
    mp2an
    a1i
    o1mul2
    wtru
    vx
    crp
    @15
    @18
    @19
    @15
    cc
    wcel
    wtru
    @19
    @15
    @19
    @2
    @14
    vn
    @21
    @23
    @5
    @13
    @28
    @23
    @11
    @12
    @23
    @8
    @10
    vm
    @23
    c1
    @7
    fzfid
    #
    @23
    @9
    @8
    wcel
    #
    wa
    #
    @9
    @36
    @9
    cn
    wcel
    #
    @23
    @9
    @7
    elfznn
    adantl
    #
    nnrecred
    fsumrecl
    @23
    @6
    @22
    @19
    @3
    crp
    wcel
    #
    @6
    crp
    wcel
    #
    @22
    @3
    @25
    nnrpd
    #
    @0
    @3
    rpdivcl
    sylan2
    #
    relogcld
    #
    resubcld
    remulcld
    fsumrecl
    recnd
    adantl
    @19
    @18
    cc
    wcel
    #
    wtru
    @19
    @20
    @31
    @45
    @30
    @32
    @17
    cem
    mulcl
    sylancl
    adantl
    wtru
    vx
    crp
    @15
    @18
    cmin
    co
    #
    cmpt
    vx
    crp
    @2
    @5
    @11
    @12
    cem
    caddc
    co
    #
    cmin
    co
    #
    cmul
    co
    #
    vn
    csu
    #
    cmpt
    co1
    vx
    crp
    @50
    @46
    @19
    @2
    @14
    @5
    cem
    cmul
    co
    #
    cmin
    co
    #
    vn
    csu
    @15
    @2
    @51
    vn
    csu
    #
    cmin
    co
    @50
    @46
    @19
    @2
    @14
    @51
    vn
    @21
    @23
    @5
    @13
    @29
    @23
    @11
    @12
    @23
    @8
    @10
    vm
    @35
    @37
    @38
    @10
    cc
    wcel
    @39
    @38
    @10
    @9
    nnrecre
    recnd
    syl
    fsumcl
    #
    @23
    @12
    @44
    recnd
    #
    subcld
    #
    mulcld
    @23
    @5
    cc
    wcel
    @31
    @51
    cc
    wcel
    @29
    @32
    @5
    cem
    mulcl
    sylancl
    fsumsub
    @19
    @2
    @49
    @52
    vn
    @23
    @5
    @13
    cem
    cmin
    co
    #
    cmul
    co
    @49
    @52
    @23
    @57
    @48
    @5
    cmul
    @23
    @11
    @12
    cem
    @54
    @55
    @31
    @23
    @32
    a1i
    #
    subsub4d
    oveq2d
    @23
    @5
    @13
    cem
    @29
    @56
    @58
    subdid
    eqtr3d
    sumeq2dv
    @19
    @18
    @53
    @15
    cmin
    @19
    @2
    @5
    cem
    vn
    @21
    @31
    @19
    @32
    a1i
    @29
    fsummulc1
    oveq2d
    3eqtr4d
    mpteq2ia
    wtru
    vx
    crp
    @50
    c1
    c1
    @34
    wtru
    rpssre
    a1i
    @19
    @50
    cc
    wcel
    wtru
    @19
    @2
    @49
    vn
    @21
    @23
    @5
    @48
    @29
    @23
    @11
    @47
    @54
    @23
    @12
    cem
    @55
    @58
    addcld
    subcld
    #
    mulcld
    #
    fsumcl
    #
    adantl
    wtru
    1red
    #
    @62
    @19
    @50
    cabs
    cfv
    #
    c1
    cle
    wbr
    wtru
    c1
    @0
    cle
    wbr
    @19
    @63
    @2
    @49
    cabs
    cfv
    #
    vn
    csu
    #
    c1
    @19
    @50
    @61
    abscld
    @19
    @2
    @64
    vn
    @21
    @23
    @49
    @60
    abscld
    #
    fsumrecl
    #
    @19
    1red
    #
    @19
    @2
    @49
    vn
    @21
    @60
    fsumabs
    @19
    @65
    @1
    @0
    cdiv
    co
    #
    c1
    @67
    @1
    cr
    wcel
    #
    @19
    @69
    cr
    wcel
    @19
    @1
    @19
    @0
    cr
    wcel
    #
    cc0
    @0
    cle
    wbr
    wa
    @1
    cn0
    wcel
    #
    @0
    rprege0
    @0
    flge0nn0
    syl
    #
    nn0red
    @1
    @0
    rerpdivcl
    mpancom
    @68
    @19
    @65
    @2
    c1
    @0
    cdiv
    co
    #
    vn
    csu
    #
    @69
    cle
    @19
    @2
    @64
    @74
    vn
    @21
    @66
    @23
    @74
    @19
    @74
    crp
    wcel
    @22
    @0
    rpreccl
    #
    adantr
    rpred
    @23
    @5
    cabs
    cfv
    #
    @48
    cabs
    cfv
    #
    cmul
    co
    c1
    @3
    cdiv
    co
    #
    @3
    @0
    cdiv
    co
    #
    cmul
    co
    #
    @64
    @74
    cle
    @23
    @77
    @79
    @78
    @80
    @23
    @5
    @29
    abscld
    @23
    @3
    @26
    nnrecred
    #
    @23
    @48
    @59
    abscld
    @23
    @80
    @22
    @40
    @19
    @80
    crp
    wcel
    @19
    @42
    @19
    id
    @3
    @0
    rpdivcl
    syl2anr
    #
    rpred
    @23
    @5
    @29
    absge0d
    @23
    @48
    @59
    absge0d
    @23
    @77
    @4
    cabs
    cfv
    #
    @3
    cdiv
    co
    #
    @79
    cle
    @23
    @77
    @84
    @3
    cabs
    cfv
    #
    cdiv
    co
    @85
    @23
    @4
    @3
    @23
    @4
    @27
    recnd
    #
    @23
    @3
    @26
    nncnd
    @23
    @3
    @26
    nnne0d
    absdivd
    @23
    @86
    @3
    @84
    cdiv
    @23
    @3
    cr
    wcel
    cc0
    @3
    cle
    wbr
    wa
    #
    @86
    @3
    wceq
    @23
    @40
    @88
    @23
    @3
    @26
    nnrpd
    #
    @3
    rprege0
    syl
    @3
    absid
    syl
    oveq2d
    eqtrd
    @23
    @84
    c1
    @3
    @23
    @4
    @87
    abscld
    @23
    1red
    @89
    @23
    @24
    @84
    c1
    cle
    wbr
    @26
    @3
    mule1
    syl
    lediv1dd
    eqbrtrd
    @23
    @78
    c1
    @6
    cdiv
    co
    #
    @80
    cle
    @23
    @41
    @78
    @90
    cle
    wbr
    @43
    @6
    vm
    harmonicbnd4
    syl
    @23
    @0
    cc
    wcel
    @0
    cc0
    wne
    wa
    #
    @3
    cc
    wcel
    @3
    cc0
    wne
    wa
    #
    @90
    @80
    wceq
    @19
    @91
    @22
    @0
    rpcnne0
    adantr
    #
    @23
    @40
    @92
    @89
    @3
    rpcnne0
    syl
    #
    @0
    @3
    recdiv
    syl2anc
    breqtrd
    lemul12ad
    @23
    @5
    @48
    @29
    @59
    absmuld
    @23
    @80
    @79
    cmul
    co
    #
    @74
    @81
    @23
    @92
    @91
    c1
    cc
    wcel
    @95
    @74
    wceq
    @94
    @93
    @23
    1cnd
    @3
    @0
    c1
    dmdcan
    syl3anc
    @23
    @80
    @79
    @23
    @80
    @83
    rpcnd
    @23
    @79
    @82
    recnd
    mulcomd
    eqtr3d
    3brtr4d
    fsumle
    @19
    @2
    chash
    cfv
    #
    @74
    cmul
    co
    #
    @1
    @74
    cmul
    co
    @75
    @69
    @19
    @96
    @1
    @74
    cmul
    @19
    @72
    @96
    @1
    wceq
    @73
    @1
    hashfz1
    syl
    oveq1d
    @19
    @2
    cfn
    wcel
    @74
    cc
    wcel
    @75
    @97
    wceq
    @21
    @19
    @74
    @76
    rpcnd
    @2
    @74
    vn
    fsumconst
    syl2anc
    @19
    @1
    @0
    @19
    @1
    @73
    nn0cnd
    @0
    rpcn
    #
    @0
    rpne0
    divrecd
    3eqtr4d
    breqtrd
    @19
    @69
    c1
    cle
    wbr
    #
    @1
    @0
    c1
    cmul
    co
    #
    cle
    wbr
    #
    @19
    @1
    @0
    @100
    cle
    @19
    @71
    @1
    @0
    cle
    wbr
    @0
    rpre
    #
    @0
    flle
    syl
    @19
    @0
    @98
    mulid1d
    breqtrrd
    @19
    @70
    c1
    cr
    wcel
    @71
    cc0
    @0
    clt
    wbr
    wa
    @99
    @101
    wb
    @19
    @71
    @70
    @102
    @0
    reflcl
    syl
    @68
    @0
    rpregt0
    @1
    c1
    @0
    ledivmul
    syl3anc
    mpbird
    letrd
    letrd
    ad2antrl
    elo1d
    syl5eqelr
    o1dif
    mpbird
    trud
end
