include "c1.mm"
include "c2.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "cfz.mm"
include "cpi.mm"
include "ccos.mm"
include "cfv.mm"
include "csu.mm"
include "cc0.mm"
include "wceq.mm"
include "caddc.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "sumeq1d.mm"
include "eqeq1d.mm"
include "ax-1cn.mm"
include "2timesi.mm"
include "oveq2i.mm"
include "sumeq1i.mm"
include "cneg.mm"
include "wtru.mm"
include "cuz.mm"
include "wcel.mm"
include "cz.mm"
include "1z.mm"
include "uzid.mm"
include "ax-mp.mm"
include "a1i.mm"
include "wa.mm"
include "cc.mm"
include "elfzelz.mm"
include "zcnd.mm"
include "adantl.mm"
include "picn.mm"
include "mulcld.mm"
include "coscld.mm"
include "id.mm"
include "1p1e2.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "fsump1.mm"
include "trud.mm"
include "coscl.mm"
include "oveq1.mm"
include "mulid2i.mm"
include "fsum1.mm"
include "mp2an.mm"
include "cospi.mm"
include "eqtri.mm"
include "cos2pi.mm"
include "oveq12i.mm"
include "neg1cn.mm"
include "1pneg1e0.mm"
include "addcomli.mm"
include "3eqtri.mm"
include "cn.mm"
include "2cnd.mm"
include "nncn.mm"
include "adddid.mm"
include "addassd.mm"
include "3eqtr4a.mm"
include "adantr.mm"
include "cle.mm"
include "wbr.mm"
include "1red.mm"
include "cr.mm"
include "2re.mm"
include "nnre.mm"
include "remulcld.mm"
include "readdcld.mm"
include "crp.mm"
include "2rp.mm"
include "nnrp.mm"
include "rpmulcld.mm"
include "ltaddrp2d.mm"
include "ltled.mm"
include "wb.mm"
include "2z.mm"
include "nnz.mm"
include "zmulcld.mm"
include "peano2zd.mm"
include "eluz.mm"
include "sylancr.mm"
include "mpbird.mm"
include "clt.mm"
include "1lt2.mm"
include "2t1e2.mm"
include "nnge1.mm"
include "lemul2d.mm"
include "mpbid.mm"
include "syl5eqbrr.mm"
include "ltletrd.mm"
include "eqtr4i.mm"
include "3eqtr4d.mm"
include "cdiv.mm"
include "addcld.mm"
include "mulassd.mm"
include "wne.mm"
include "0re.mm"
include "pipos.mm"
include "gtneii.mm"
include "rpne0d.mm"
include "divcan5d.mm"
include "divcan4d.mm"
include "3eqtrd.mm"
include "eqeltrd.mm"
include "peano2cn.mm"
include "syl.mm"
include "coseq1.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "simpr.mm"
include "adddird.mm"
include "syl5eqel.mm"
include "addcomd.mm"
include "mulcomd.mm"
include "cosper.mm"
include "addid2i.mm"
include "oveq1i.mm"
include "ex.mm"
include "nnind.mm"

theorem dirkertrigeqlem1
  let vn: setvar n
  let cK: class K
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k

  disjoint K n
  disjoint K x
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint k x
  assert |- ( K e. NN -> sum_ n e. ( 1 ... ( 2 x. K ) ) ( cos ` ( n x. _pi ) ) = 0 )

  proof
    c1
    c2
    vx
    cv
    #
    cmul
    co
    #
    cfz
    co
    #
    vn
    cv
    #
    cpi
    cmul
    co
    #
    ccos
    cfv
    #
    vn
    csu
    #
    cc0
    wceq
    c1
    c2
    c1
    cmul
    co
    #
    cfz
    co
    #
    @5
    vn
    csu
    #
    cc0
    wceq
    c1
    c2
    vy
    cv
    #
    cmul
    co
    #
    cfz
    co
    #
    @5
    vn
    csu
    #
    cc0
    wceq
    #
    c1
    c2
    @10
    c1
    caddc
    co
    #
    cmul
    co
    #
    cfz
    co
    #
    @5
    vn
    csu
    #
    cc0
    wceq
    #
    c1
    c2
    cK
    cmul
    co
    #
    cfz
    co
    #
    @5
    vn
    csu
    #
    cc0
    wceq
    vx
    vy
    cK
    @0
    c1
    wceq
    #
    @6
    @9
    cc0
    @23
    @2
    @8
    @5
    vn
    @23
    @1
    @7
    c1
    cfz
    @0
    c1
    c2
    cmul
    oveq2
    oveq2d
    sumeq1d
    eqeq1d
    @0
    @10
    wceq
    #
    @6
    @13
    cc0
    @24
    @2
    @12
    @5
    vn
    @24
    @1
    @11
    c1
    cfz
    @0
    @10
    c2
    cmul
    oveq2
    oveq2d
    sumeq1d
    eqeq1d
    @0
    @15
    wceq
    #
    @6
    @18
    cc0
    @25
    @2
    @17
    @5
    vn
    @25
    @1
    @16
    c1
    cfz
    @0
    @15
    c2
    cmul
    oveq2
    oveq2d
    sumeq1d
    eqeq1d
    @0
    cK
    wceq
    #
    @6
    @22
    cc0
    @26
    @2
    @21
    @5
    vn
    @26
    @1
    @20
    c1
    cfz
    @0
    cK
    c2
    cmul
    oveq2
    oveq2d
    sumeq1d
    eqeq1d
    @9
    c1
    c1
    c1
    caddc
    co
    #
    cfz
    co
    #
    @5
    vn
    csu
    #
    cc0
    @8
    @28
    @5
    vn
    @7
    @27
    c1
    cfz
    c1
    ax-1cn
    2timesi
    #
    oveq2i
    sumeq1i
    @29
    c1
    c1
    cfz
    co
    @5
    vn
    csu
    #
    c2
    cpi
    cmul
    co
    #
    ccos
    cfv
    #
    caddc
    co
    #
    c1
    cneg
    #
    c1
    caddc
    co
    #
    cc0
    @29
    @34
    wceq
    wtru
    @5
    @33
    vn
    c1
    c1
    c1
    c1
    cuz
    cfv
    #
    wcel
    #
    wtru
    c1
    cz
    wcel
    #
    @38
    1z
    c1
    uzid
    ax-mp
    a1i
    wtru
    @3
    @28
    wcel
    #
    wa
    #
    @4
    @41
    @3
    cpi
    @40
    @3
    cc
    wcel
    wtru
    @40
    @3
    @3
    c1
    @27
    elfzelz
    zcnd
    adantl
    cpi
    cc
    wcel
    #
    @41
    picn
    a1i
    mulcld
    coscld
    @3
    @27
    wceq
    #
    @4
    @32
    ccos
    @43
    @3
    c2
    cpi
    cmul
    @43
    @3
    @27
    c2
    @43
    id
    1p1e2
    syl6eq
    oveq1d
    fveq2d
    fsump1
    trud
    @31
    @35
    @33
    c1
    caddc
    @31
    cpi
    ccos
    cfv
    #
    @35
    @39
    @44
    cc
    wcel
    #
    @31
    @44
    wceq
    1z
    @42
    @45
    picn
    cpi
    coscl
    ax-mp
    @5
    @44
    vn
    c1
    @3
    c1
    wceq
    #
    @4
    cpi
    ccos
    @46
    @4
    c1
    cpi
    cmul
    co
    #
    cpi
    @3
    c1
    cpi
    cmul
    oveq1
    cpi
    picn
    mulid2i
    #
    syl6eq
    fveq2d
    fsum1
    mp2an
    cospi
    eqtri
    cos2pi
    oveq12i
    c1
    @35
    cc0
    ax-1cn
    neg1cn
    1pneg1e0
    addcomli
    #
    3eqtri
    eqtri
    @10
    cn
    wcel
    #
    @14
    @19
    @50
    @14
    wa
    #
    @18
    c1
    @11
    c1
    caddc
    co
    #
    c1
    caddc
    co
    #
    cfz
    co
    #
    @5
    vn
    csu
    #
    c1
    @52
    cfz
    co
    #
    @5
    vn
    csu
    #
    @53
    cpi
    cmul
    co
    #
    ccos
    cfv
    #
    caddc
    co
    #
    cc0
    @50
    @18
    @55
    wceq
    @14
    @50
    @17
    @54
    @5
    vn
    @50
    @16
    @53
    c1
    cfz
    @50
    @11
    @7
    caddc
    co
    #
    @11
    @27
    caddc
    co
    #
    @16
    @53
    @7
    @27
    @11
    caddc
    @30
    oveq2i
    @50
    c2
    @10
    c1
    @50
    2cnd
    #
    @10
    nncn
    #
    c1
    cc
    wcel
    @50
    ax-1cn
    a1i
    #
    adddid
    #
    @50
    @11
    c1
    c1
    @50
    c2
    @10
    @63
    @64
    mulcld
    #
    @65
    @65
    addassd
    #
    3eqtr4a
    oveq2d
    sumeq1d
    adantr
    @50
    @55
    @60
    wceq
    @14
    @50
    @5
    @59
    vn
    c1
    @52
    @50
    @52
    @37
    wcel
    #
    c1
    @52
    cle
    wbr
    #
    @50
    c1
    @52
    @50
    1red
    #
    @50
    @11
    c1
    @50
    c2
    @10
    c2
    cr
    wcel
    @50
    2re
    a1i
    #
    @10
    nnre
    #
    remulcld
    #
    @71
    readdcld
    @50
    c1
    @11
    @71
    @50
    c2
    @10
    c2
    crp
    wcel
    @50
    2rp
    a1i
    #
    @10
    nnrp
    rpmulcld
    ltaddrp2d
    ltled
    @50
    @39
    @52
    cz
    wcel
    @69
    @70
    wb
    1z
    @50
    @11
    @50
    c2
    @10
    c2
    cz
    wcel
    @50
    2z
    a1i
    @10
    nnz
    #
    zmulcld
    #
    peano2zd
    c1
    @52
    eluz
    sylancr
    mpbird
    @3
    @54
    wcel
    #
    @5
    cc
    wcel
    #
    @50
    @78
    @4
    @78
    @3
    cpi
    @78
    @3
    @3
    c1
    @53
    elfzelz
    zcnd
    @42
    @78
    picn
    a1i
    mulcld
    coscld
    adantl
    @3
    @53
    wceq
    @4
    @58
    ccos
    @3
    @53
    cpi
    cmul
    oveq1
    fveq2d
    fsump1
    adantr
    @51
    @60
    @13
    @52
    cpi
    cmul
    co
    #
    ccos
    cfv
    #
    caddc
    co
    #
    c1
    caddc
    co
    #
    cc0
    @50
    @60
    @83
    wceq
    @14
    @50
    @57
    @82
    @59
    c1
    caddc
    @50
    @5
    @81
    vn
    c1
    @11
    @50
    @11
    @37
    wcel
    #
    c1
    @11
    cle
    wbr
    #
    @50
    c1
    @11
    @71
    @74
    @50
    c1
    c2
    @11
    @71
    @72
    @74
    c1
    c2
    clt
    wbr
    @50
    1lt2
    a1i
    @50
    c2
    @7
    @11
    cle
    2t1e2
    @50
    c1
    @10
    cle
    wbr
    @7
    @11
    cle
    wbr
    @10
    nnge1
    @50
    c1
    @10
    c2
    @71
    @73
    @75
    lemul2d
    mpbid
    syl5eqbrr
    ltletrd
    ltled
    @50
    @39
    @11
    cz
    wcel
    @84
    @85
    wb
    1z
    @77
    c1
    @11
    eluz
    sylancr
    mpbird
    @3
    @56
    wcel
    #
    @79
    @50
    @86
    @4
    @86
    @3
    cpi
    @86
    @3
    @3
    c1
    @52
    elfzelz
    zcnd
    @42
    @86
    picn
    a1i
    mulcld
    coscld
    adantl
    @3
    @52
    wceq
    @4
    @80
    ccos
    @3
    @52
    cpi
    cmul
    oveq1
    fveq2d
    fsump1
    @50
    @59
    @16
    cpi
    cmul
    co
    #
    ccos
    cfv
    #
    c1
    @50
    @58
    @87
    ccos
    @50
    @53
    @16
    cpi
    cmul
    @50
    @62
    @61
    @53
    @16
    @50
    @27
    @7
    @11
    caddc
    @27
    @7
    wceq
    @50
    @27
    c2
    @7
    1p1e2
    2t1e2
    eqtr4i
    a1i
    oveq2d
    @68
    @66
    3eqtr4d
    oveq1d
    fveq2d
    @50
    @88
    c1
    wceq
    #
    @87
    @32
    cdiv
    co
    #
    cz
    wcel
    #
    @50
    @90
    @15
    cz
    @50
    @90
    c2
    @15
    cpi
    cmul
    co
    #
    cmul
    co
    #
    @32
    cdiv
    co
    @92
    cpi
    cdiv
    co
    @15
    @50
    @87
    @93
    @32
    cdiv
    @50
    c2
    @15
    cpi
    @63
    @50
    @10
    c1
    @64
    @65
    addcld
    #
    @42
    @50
    picn
    a1i
    #
    mulassd
    oveq1d
    @50
    @92
    cpi
    c2
    @50
    @15
    cpi
    @94
    @95
    mulcld
    @95
    @63
    cpi
    cc0
    wne
    @50
    cc0
    cpi
    0re
    pipos
    gtneii
    a1i
    #
    @50
    c2
    @75
    rpne0d
    divcan5d
    @50
    @15
    cpi
    @94
    @95
    @96
    divcan4d
    3eqtrd
    @50
    @10
    @76
    peano2zd
    eqeltrd
    @50
    @87
    cc
    wcel
    @89
    @91
    wb
    @50
    @16
    cpi
    @50
    c2
    @15
    @63
    @50
    @10
    cc
    wcel
    @15
    cc
    wcel
    @64
    @10
    peano2cn
    syl
    mulcld
    @95
    mulcld
    @87
    coseq1
    syl
    mpbird
    eqtrd
    oveq12d
    adantr
    @51
    @83
    cc0
    @35
    caddc
    co
    #
    c1
    caddc
    co
    #
    cc0
    @51
    @82
    @97
    c1
    caddc
    @51
    @13
    cc0
    @81
    @35
    caddc
    @50
    @14
    simpr
    @50
    @81
    @35
    wceq
    @14
    @50
    @81
    cpi
    @10
    @32
    cmul
    co
    #
    caddc
    co
    #
    ccos
    cfv
    #
    @44
    @35
    @50
    @80
    @100
    ccos
    @50
    @80
    @11
    cpi
    cmul
    co
    #
    @47
    caddc
    co
    @47
    @102
    caddc
    co
    @100
    @50
    @11
    c1
    cpi
    @67
    @65
    @95
    adddird
    @50
    @102
    @47
    @50
    @11
    cpi
    @67
    @95
    mulcld
    @50
    @47
    cpi
    cc
    @48
    @95
    syl5eqel
    addcomd
    @50
    @47
    cpi
    @102
    @99
    caddc
    @47
    cpi
    wceq
    @50
    @48
    a1i
    @50
    @102
    @10
    c2
    cmul
    co
    #
    cpi
    cmul
    co
    @99
    @50
    @11
    @103
    cpi
    cmul
    @50
    c2
    @10
    @63
    @64
    mulcomd
    oveq1d
    @50
    @10
    c2
    cpi
    @64
    @63
    @95
    mulassd
    eqtrd
    oveq12d
    3eqtrd
    fveq2d
    @50
    @42
    @10
    cz
    wcel
    @101
    @44
    wceq
    picn
    @76
    cpi
    @10
    cosper
    sylancr
    @44
    @35
    wceq
    @50
    cospi
    a1i
    3eqtrd
    adantr
    oveq12d
    oveq1d
    @98
    @36
    cc0
    @97
    @35
    c1
    caddc
    @35
    neg1cn
    addid2i
    oveq1i
    @49
    eqtri
    syl6eq
    eqtrd
    3eqtrd
    ex
    nnind
end
