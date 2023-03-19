include "crp.mm"
include "c1.mm"
include "cv.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cvma.mm"
include "clog.mm"
include "cdiv.mm"
include "cchp.mm"
include "caddc.mm"
include "cmul.mm"
include "csu.mm"
include "c2.mm"
include "cmin.mm"
include "cmpt.mm"
include "cmu.mm"
include "cexp.mm"
include "co1.mm"
include "wcel.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn.mm"
include "crab.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "cbvsumv.mm"
include "wa.mm"
include "fzfid.mm"
include "cr.mm"
include "elfznn.mm"
include "adantl.mm"
include "vmacl.mm"
include "syl.mm"
include "recnd.mm"
include "fsummulc2.mm"
include "nnrpd.mm"
include "rpdivcl.mm"
include "sylan2.mm"
include "rpred.mm"
include "chpval.mm"
include "oveq2d.mm"
include "nncnd.mm"
include "ad2antlr.mm"
include "nnne0d.mm"
include "divcan3d.mm"
include "sumeq2dv.mm"
include "3eqtr4d.mm"
include "syl5eq.mm"
include "oveq1.mm"
include "rpre.mm"
include "cc.mm"
include "ssrab2.mm"
include "simprr.mm"
include "sseldi.mm"
include "anassrs.mm"
include "dvdsdivcl.mm"
include "sylan.mm"
include "remulcld.mm"
include "anasss.mm"
include "dvdsflsumcom.mm"
include "eqtr4d.mm"
include "oveq1d.mm"
include "chpcl.mm"
include "mulcld.mm"
include "relogcl.mm"
include "fsumadd.mm"
include "cfn.mm"
include "wss.mm"
include "dvdsssfz1.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "fsumrecl.mm"
include "addcomd.mm"
include "adddid.mm"
include "eqtrd.mm"
include "logsqvma2.mm"
include "cz.mm"
include "mucl.mm"
include "zcnd.mm"
include "ad2antrl.mm"
include "rpdivcld.mm"
include "sqcld.mm"
include "3eqtrd.mm"
include "mpteq2ia.mm"
include "eqid.mm"
include "selberglem2.mm"
include "eqeltri.mm"

theorem selberg
  let vx: setvar x
  let vn: setvar n
  let vc: setvar c
  let vd: setvar d
  let vm: setvar m
  let vy: setvar y

  disjoint n x
  disjoint c d
  disjoint c m
  disjoint c n
  disjoint c x
  disjoint c y
  disjoint d m
  disjoint d n
  disjoint d x
  disjoint d y
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint n y
  disjoint x y
  assert |- ( x e. RR+ |-> ( ( sum_ n e. ( 1 ... ( |_ ` x ) ) ( ( Lam ` n ) x. ( ( log ` n ) + ( psi ` ( x / n ) ) ) ) / x ) - ( 2 x. ( log ` x ) ) ) ) e. O(1)

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
    cvma
    cfv
    #
    @3
    clog
    cfv
    #
    @0
    @3
    cdiv
    co
    #
    cchp
    cfv
    #
    caddc
    co
    #
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
    c2
    @0
    clog
    cfv
    cmul
    co
    #
    cmin
    co
    #
    cmpt
    vx
    crp
    @2
    c1
    @0
    vd
    cv
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    cfz
    co
    #
    @14
    cmu
    cfv
    #
    vm
    cv
    #
    clog
    cfv
    #
    c2
    cexp
    co
    #
    cmul
    co
    #
    vm
    csu
    #
    vd
    csu
    #
    @0
    cdiv
    co
    #
    @12
    cmin
    co
    #
    cmpt
    co1
    vx
    crp
    @13
    @26
    @0
    crp
    wcel
    #
    @11
    @25
    @12
    cmin
    @27
    @10
    @24
    @0
    cdiv
    @27
    @10
    @2
    vy
    cv
    @3
    cdvds
    wbr
    #
    vy
    cn
    crab
    #
    @18
    @3
    @14
    cdiv
    co
    #
    clog
    cfv
    #
    c2
    cexp
    co
    #
    cmul
    co
    #
    vd
    csu
    #
    vn
    csu
    #
    @2
    @17
    @18
    @14
    @19
    cmul
    co
    #
    @14
    cdiv
    co
    #
    clog
    cfv
    #
    c2
    cexp
    co
    #
    cmul
    co
    #
    vm
    csu
    #
    vd
    csu
    @24
    @27
    @2
    @4
    @7
    cmul
    co
    #
    @4
    @5
    cmul
    co
    #
    caddc
    co
    #
    vn
    csu
    #
    @2
    @29
    @14
    cvma
    cfv
    #
    @30
    cvma
    cfv
    #
    cmul
    co
    #
    vd
    csu
    #
    @43
    caddc
    co
    #
    vn
    csu
    #
    @10
    @35
    @27
    @2
    @42
    vn
    csu
    #
    @2
    @43
    vn
    csu
    #
    caddc
    co
    @2
    @49
    vn
    csu
    #
    @53
    caddc
    co
    @45
    @51
    @27
    @52
    @54
    @53
    caddc
    @27
    @52
    @2
    @17
    @46
    @37
    cvma
    cfv
    #
    cmul
    co
    #
    vm
    csu
    #
    vd
    csu
    #
    @54
    @27
    @52
    @2
    @46
    @15
    cchp
    cfv
    #
    cmul
    co
    #
    vd
    csu
    @58
    @2
    @42
    @60
    vn
    vd
    @3
    @14
    wceq
    #
    @4
    @46
    @7
    @59
    cmul
    @3
    @14
    cvma
    fveq2
    @61
    @6
    @15
    cchp
    @3
    @14
    @0
    cdiv
    oveq2
    fveq2d
    oveq12d
    cbvsumv
    @27
    @2
    @60
    @57
    vd
    @27
    @14
    @2
    wcel
    #
    wa
    #
    @46
    @17
    @19
    cvma
    cfv
    #
    vm
    csu
    #
    cmul
    co
    @17
    @46
    @64
    cmul
    co
    #
    vm
    csu
    @60
    @57
    @63
    @17
    @64
    @46
    vm
    @63
    c1
    @16
    fzfid
    @63
    @46
    @63
    @14
    cn
    wcel
    #
    @46
    cr
    wcel
    #
    @62
    @67
    @27
    @14
    @1
    elfznn
    #
    adantl
    @14
    vmacl
    #
    syl
    recnd
    @63
    @19
    @17
    wcel
    #
    wa
    #
    @64
    @72
    @19
    cn
    wcel
    #
    @64
    cr
    wcel
    @71
    @73
    @63
    @19
    @16
    elfznn
    adantl
    #
    @19
    vmacl
    syl
    recnd
    fsummulc2
    @63
    @59
    @65
    @46
    cmul
    @63
    @15
    cr
    wcel
    @59
    @65
    wceq
    @63
    @15
    @62
    @27
    @14
    crp
    wcel
    @15
    crp
    wcel
    @62
    @14
    @69
    nnrpd
    @0
    @14
    rpdivcl
    sylan2
    rpred
    @15
    vm
    chpval
    syl
    oveq2d
    @63
    @17
    @56
    @66
    vm
    @72
    @55
    @64
    @46
    cmul
    @72
    @37
    @19
    cvma
    @72
    @19
    @14
    @72
    @19
    @74
    nncnd
    @72
    @14
    @62
    @67
    @27
    @71
    @69
    ad2antlr
    #
    nncnd
    @72
    @14
    @75
    nnne0d
    divcan3d
    #
    fveq2d
    oveq2d
    sumeq2dv
    3eqtr4d
    sumeq2dv
    syl5eq
    @27
    vy
    @0
    @48
    @56
    vm
    vn
    vd
    @3
    @36
    wceq
    #
    @47
    @55
    @46
    cmul
    @77
    @30
    @37
    cvma
    @3
    @36
    @14
    cdiv
    oveq1
    #
    fveq2d
    oveq2d
    @0
    rpre
    #
    @27
    @3
    @2
    wcel
    #
    @14
    @29
    wcel
    #
    @48
    cc
    wcel
    @27
    @80
    wa
    #
    @81
    wa
    #
    @48
    @83
    @46
    @47
    @83
    @67
    @68
    @27
    @80
    @81
    @67
    @27
    @80
    @81
    wa
    wa
    #
    @29
    cn
    @14
    @28
    vy
    cn
    ssrab2
    #
    @27
    @80
    @81
    simprr
    sseldi
    #
    anassrs
    @70
    syl
    @83
    @30
    cn
    wcel
    @47
    cr
    wcel
    @83
    @29
    cn
    @30
    @85
    @82
    @3
    cn
    wcel
    #
    @81
    @30
    @29
    wcel
    @80
    @87
    @27
    @3
    @1
    elfznn
    #
    adantl
    #
    vy
    @14
    @3
    dvdsdivcl
    sylan
    sseldi
    @30
    vmacl
    syl
    remulcld
    #
    recnd
    anasss
    dvdsflsumcom
    eqtr4d
    oveq1d
    @27
    @2
    @42
    @43
    vn
    @27
    c1
    @1
    fzfid
    #
    @82
    @4
    @7
    @82
    @4
    @82
    @87
    @4
    cr
    wcel
    @89
    @3
    vmacl
    syl
    recnd
    #
    @82
    @7
    @82
    @6
    cr
    wcel
    @7
    cr
    wcel
    @82
    @6
    @80
    @27
    @3
    crp
    wcel
    #
    @6
    crp
    wcel
    @80
    @3
    @88
    nnrpd
    #
    @0
    @3
    rpdivcl
    sylan2
    rpred
    @6
    chpcl
    syl
    recnd
    #
    mulcld
    @82
    @4
    @5
    @92
    @82
    @5
    @82
    @93
    @5
    cr
    wcel
    @82
    @3
    @89
    nnrpd
    @3
    relogcl
    syl
    recnd
    #
    mulcld
    #
    fsumadd
    @27
    @2
    @49
    @43
    vn
    @91
    @82
    @49
    @82
    @29
    @48
    vd
    @82
    c1
    @3
    cfz
    co
    #
    cfn
    wcel
    @29
    @98
    wss
    #
    @29
    cfn
    wcel
    @82
    c1
    @3
    fzfid
    @82
    @87
    @99
    @89
    @3
    vy
    dvdsssfz1
    syl
    @98
    @29
    ssfi
    syl2anc
    @90
    fsumrecl
    recnd
    @97
    fsumadd
    3eqtr4d
    @27
    @2
    @9
    @44
    vn
    @82
    @9
    @4
    @7
    @5
    caddc
    co
    #
    cmul
    co
    @44
    @82
    @8
    @100
    @4
    cmul
    @82
    @5
    @7
    @96
    @95
    addcomd
    oveq2d
    @82
    @4
    @7
    @5
    @92
    @95
    @96
    adddid
    eqtrd
    sumeq2dv
    @27
    @2
    @34
    @50
    vn
    @82
    @87
    @34
    @50
    wceq
    @89
    vy
    @3
    vd
    logsqvma2
    syl
    sumeq2dv
    3eqtr4d
    @27
    vy
    @0
    @33
    @40
    vm
    vn
    vd
    @77
    @32
    @39
    @18
    cmul
    @77
    @31
    @38
    c2
    cexp
    @77
    @30
    @37
    clog
    @78
    fveq2d
    oveq1d
    oveq2d
    @79
    @84
    @18
    @32
    @84
    @18
    @84
    @67
    @18
    cz
    wcel
    @86
    @14
    mucl
    syl
    zcnd
    @84
    @31
    @84
    @30
    crp
    wcel
    #
    @31
    cc
    wcel
    @84
    @3
    @14
    @80
    @93
    @27
    @81
    @94
    ad2antrl
    @84
    @14
    @86
    nnrpd
    rpdivcld
    @101
    @31
    @30
    relogcl
    recnd
    syl
    sqcld
    mulcld
    dvdsflsumcom
    @27
    @2
    @41
    @23
    vd
    @63
    @17
    @40
    @22
    vm
    @72
    @39
    @21
    @18
    cmul
    @72
    @38
    @20
    c2
    cexp
    @72
    @37
    @19
    clog
    @76
    fveq2d
    oveq1d
    oveq2d
    sumeq2dv
    sumeq2dv
    3eqtrd
    oveq1d
    oveq1d
    mpteq2ia
    vx
    @15
    clog
    cfv
    #
    c2
    cexp
    co
    c2
    c2
    @102
    cmul
    co
    cmin
    co
    caddc
    co
    @14
    cdiv
    co
    #
    vm
    vd
    @103
    eqid
    selberglem2
    eqeltri
end
