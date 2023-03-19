include "c1.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "clog.mm"
include "cmul.mm"
include "c2.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfz.mm"
include "cvma.mm"
include "csu.mm"
include "caddc.mm"
include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "wtru.mm"
include "cchp.mm"
include "cmin.mm"
include "wa.mm"
include "cr.mm"
include "elioore.mm"
include "adantl.mm"
include "crp.mm"
include "1rp.mm"
include "a1i.mm"
include "1red.mm"
include "clt.mm"
include "wbr.mm"
include "eliooord.mm"
include "simpld.mm"
include "ltled.mm"
include "rpgecld.mm"
include "relogcld.mm"
include "recnd.mm"
include "2timesd.mm"
include "oveq2d.mm"
include "chpcl.mm"
include "syl.mm"
include "remulcld.mm"
include "2re.mm"
include "rplogcld.mm"
include "rerpdivcld.mm"
include "fzfid.mm"
include "cn.mm"
include "elfznn.mm"
include "vmacl.mm"
include "adantr.mm"
include "nndivred.mm"
include "nnrpd.mm"
include "fsumrecl.mm"
include "readdcld.mm"
include "subsub4d.mm"
include "eqtr4d.mm"
include "oveq1d.mm"
include "subcld.mm"
include "cc.mm"
include "2cn.mm"
include "rpne0d.mm"
include "divcld.mm"
include "mulcld.mm"
include "nnncan2d.mm"
include "pntrf.mm"
include "ffvelrni.mm"
include "addcld.mm"
include "divsubdird.mm"
include "addsubassd.mm"
include "subdid.mm"
include "fsummulc2.mm"
include "fsumsub.mm"
include "mul32d.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "div23d.mm"
include "div12d.mm"
include "eqtr3d.mm"
include "oveq12d.mm"
include "wceq.mm"
include "rpdivcld.mm"
include "pntrval.mm"
include "eqtrd.mm"
include "sumeq2dv.mm"
include "mul12d.mm"
include "3eqtr3rd.mm"
include "subdird.mm"
include "addsubd.mm"
include "divcan3d.mm"
include "3eqtrrd.mm"
include "mpteq2dva.mm"
include "resubcld.mm"
include "selberg3.mm"
include "rehalfcld.mm"
include "div32d.mm"
include "eqcomd.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "divcan2d.mm"
include "wss.mm"
include "ioossre.mm"
include "o1const.mm"
include "mp2an.mm"
include "vmalogdivsum.mm"
include "o1mul2.mm"
include "eqeltrrd.mm"
include "o1sub2.mm"
include "eqeltrd.mm"
include "trud.mm"

theorem selberg3r
  let vx: setvar x
  let cR: class R
  let vn: setvar n
  let va: setvar a
  let vd: setvar d
  let vk: setvar k
  let vm: setvar m
  let cA: class A
  let vb: setvar b
  let vc: setvar c
  let vy: setvar y
  assume pntrval.r: |- R = ( a e. RR+ |-> ( ( psi ` a ) - a ) )

  disjoint a n
  disjoint a x
  disjoint n x
  disjoint R n
  disjoint R x
  disjoint a d
  disjoint a k
  disjoint a m
  disjoint A a
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint d x
  disjoint A d
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint m n
  disjoint m x
  disjoint A m
  disjoint A n
  disjoint A x
  disjoint b c
  disjoint b d
  disjoint b k
  disjoint b m
  disjoint b n
  disjoint b x
  disjoint b y
  disjoint R b
  disjoint c d
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c x
  disjoint c y
  disjoint R c
  disjoint d y
  disjoint R d
  disjoint k y
  disjoint R k
  disjoint m y
  disjoint R m
  disjoint n y
  disjoint x y
  disjoint R y
  assert |- ( x e. ( 1 (,) +oo ) |-> ( ( ( ( R ` x ) x. ( log ` x ) ) + ( ( 2 / ( log ` x ) ) x. sum_ n e. ( 1 ... ( |_ ` x ) ) ( ( ( Lam ` n ) x. ( R ` ( x / n ) ) ) x. ( log ` n ) ) ) ) / x ) ) e. O(1)

  proof
    vx
    c1
    cpnf
    cioo
    co
    #
    vx
    cv
    #
    cR
    cfv
    #
    @1
    clog
    cfv
    #
    cmul
    co
    #
    c2
    @3
    cdiv
    co
    #
    c1
    @1
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
    @1
    @8
    cdiv
    co
    #
    cR
    cfv
    #
    cmul
    co
    @8
    clog
    cfv
    #
    cmul
    co
    #
    vn
    csu
    #
    cmul
    co
    #
    caddc
    co
    #
    @1
    cdiv
    co
    #
    cmpt
    #
    co1
    wcel
    wtru
    @18
    vx
    @0
    @1
    cchp
    cfv
    #
    @3
    cmul
    co
    #
    @5
    @7
    @9
    @10
    cchp
    cfv
    #
    cmul
    co
    #
    @12
    cmul
    co
    #
    vn
    csu
    #
    cmul
    co
    #
    caddc
    co
    #
    @1
    cdiv
    co
    #
    c2
    @3
    cmul
    co
    #
    cmin
    co
    #
    @5
    @7
    @9
    @8
    cdiv
    co
    #
    @12
    cmul
    co
    #
    vn
    csu
    #
    cmul
    co
    #
    @3
    cmin
    co
    #
    cmin
    co
    #
    cmpt
    co1
    wtru
    vx
    @0
    @17
    @35
    wtru
    @1
    @0
    wcel
    #
    wa
    #
    @35
    @27
    @3
    cmin
    co
    #
    @3
    cmin
    co
    #
    @34
    cmin
    co
    @38
    @33
    cmin
    co
    #
    @17
    @37
    @29
    @39
    @34
    cmin
    @37
    @29
    @27
    @3
    @3
    caddc
    co
    #
    cmin
    co
    @39
    @37
    @28
    @41
    @27
    cmin
    @37
    @3
    @37
    @3
    @37
    @1
    @37
    @1
    c1
    @36
    @1
    cr
    wcel
    #
    wtru
    @1
    c1
    cpnf
    elioore
    adantl
    #
    c1
    crp
    wcel
    @37
    1rp
    a1i
    @37
    c1
    @1
    @37
    1red
    @43
    @37
    c1
    @1
    clt
    wbr
    #
    @1
    cpnf
    clt
    wbr
    #
    @36
    @44
    @45
    wa
    wtru
    @1
    c1
    cpnf
    eliooord
    adantl
    simpld
    #
    ltled
    rpgecld
    #
    relogcld
    #
    recnd
    #
    2timesd
    oveq2d
    @37
    @27
    @3
    @3
    @37
    @27
    @37
    @26
    @1
    @37
    @20
    @25
    @37
    @19
    @3
    @37
    @42
    @19
    cr
    wcel
    @43
    @1
    chpcl
    syl
    #
    @48
    remulcld
    #
    @37
    @5
    @24
    @37
    c2
    @3
    c2
    cr
    wcel
    @37
    2re
    a1i
    #
    @37
    @1
    @43
    @46
    rplogcld
    #
    rerpdivcld
    #
    @37
    @7
    @23
    vn
    @37
    c1
    @6
    fzfid
    #
    @37
    @8
    @7
    wcel
    #
    wa
    #
    @22
    @12
    @57
    @9
    @21
    @57
    @8
    cn
    wcel
    #
    @9
    cr
    wcel
    @56
    @58
    @37
    @8
    @6
    elfznn
    adantl
    #
    @8
    vmacl
    syl
    #
    @57
    @10
    cr
    wcel
    @21
    cr
    wcel
    @57
    @1
    @8
    @37
    @42
    @56
    @43
    adantr
    @59
    nndivred
    #
    @10
    chpcl
    syl
    #
    remulcld
    @57
    @8
    @57
    @8
    @59
    nnrpd
    #
    relogcld
    #
    remulcld
    #
    fsumrecl
    #
    remulcld
    #
    readdcld
    #
    @47
    rerpdivcld
    #
    recnd
    #
    @49
    @49
    subsub4d
    eqtr4d
    oveq1d
    @37
    @38
    @33
    @3
    @37
    @27
    @3
    @70
    @49
    subcld
    @37
    @5
    @32
    @37
    c2
    @3
    c2
    cc
    wcel
    #
    @37
    2cn
    a1i
    @49
    @37
    @3
    @53
    rpne0d
    #
    divcld
    #
    @37
    @32
    @37
    @7
    @31
    vn
    @55
    @57
    @30
    @12
    @57
    @9
    @8
    @60
    @59
    nndivred
    @64
    remulcld
    #
    fsumrecl
    #
    recnd
    #
    mulcld
    #
    @49
    nnncan2d
    @37
    @4
    @25
    caddc
    co
    #
    @1
    @33
    cmul
    co
    #
    cmin
    co
    #
    @1
    cdiv
    co
    @78
    @1
    cdiv
    co
    #
    @79
    @1
    cdiv
    co
    #
    cmin
    co
    @17
    @40
    @37
    @78
    @79
    @1
    @37
    @4
    @25
    @37
    @2
    @3
    @37
    @2
    @37
    @1
    crp
    wcel
    #
    @2
    cr
    wcel
    @47
    crp
    cr
    @1
    cR
    cR
    va
    pntrval.r
    pntrf
    #
    ffvelrni
    syl
    recnd
    @49
    mulcld
    #
    @37
    @25
    @67
    recnd
    #
    addcld
    @37
    @1
    @33
    @37
    @1
    @43
    recnd
    #
    @77
    mulcld
    #
    @87
    @37
    @1
    @47
    rpne0d
    #
    divsubdird
    @37
    @80
    @16
    @1
    cdiv
    @37
    @80
    @4
    @25
    @79
    cmin
    co
    #
    caddc
    co
    @16
    @37
    @4
    @25
    @79
    @85
    @86
    @88
    addsubassd
    @37
    @90
    @15
    @4
    caddc
    @37
    @5
    @24
    @1
    @32
    cmul
    co
    #
    cmin
    co
    #
    cmul
    co
    @25
    @5
    @91
    cmul
    co
    #
    cmin
    co
    @15
    @90
    @37
    @5
    @24
    @91
    @73
    @37
    @24
    @66
    recnd
    @37
    @1
    @32
    @87
    @76
    mulcld
    subdid
    @37
    @92
    @14
    @5
    cmul
    @37
    @92
    @7
    @23
    @1
    @31
    cmul
    co
    #
    cmin
    co
    #
    vn
    csu
    #
    @14
    @37
    @92
    @24
    @7
    @94
    vn
    csu
    #
    cmin
    co
    @96
    @37
    @91
    @97
    @24
    cmin
    @37
    @7
    @31
    @1
    vn
    @55
    @87
    @57
    @31
    @74
    recnd
    #
    fsummulc2
    oveq2d
    @37
    @7
    @23
    @94
    vn
    @55
    @57
    @23
    @65
    recnd
    @57
    @1
    @31
    @37
    @1
    cc
    wcel
    @56
    @87
    adantr
    #
    @98
    mulcld
    fsumsub
    eqtr4d
    @37
    @7
    @95
    @13
    vn
    @57
    @95
    @9
    @12
    cmul
    co
    #
    @11
    cmul
    co
    #
    @13
    @57
    @95
    @100
    @21
    cmul
    co
    #
    @100
    @10
    cmul
    co
    #
    cmin
    co
    #
    @101
    @57
    @23
    @102
    @94
    @103
    cmin
    @57
    @9
    @21
    @12
    @57
    @9
    @60
    recnd
    #
    @57
    @21
    @62
    recnd
    #
    @57
    @12
    @64
    recnd
    #
    mul32d
    @57
    @1
    @100
    @8
    cdiv
    co
    #
    cmul
    co
    @94
    @103
    @57
    @108
    @31
    @1
    cmul
    @57
    @9
    @12
    @8
    @105
    @107
    @57
    @8
    @59
    nncnd
    #
    @57
    @8
    @59
    nnne0d
    #
    div23d
    oveq2d
    @57
    @1
    @100
    @8
    @99
    @57
    @9
    @12
    @105
    @107
    mulcld
    #
    @109
    @110
    div12d
    eqtr3d
    oveq12d
    @57
    @101
    @100
    @21
    @10
    cmin
    co
    #
    cmul
    co
    @104
    @57
    @11
    @112
    @100
    cmul
    @57
    @10
    crp
    wcel
    #
    @11
    @112
    wceq
    @57
    @1
    @8
    @37
    @83
    @56
    @47
    adantr
    @63
    rpdivcld
    #
    @10
    cR
    va
    pntrval.r
    pntrval
    syl
    oveq2d
    @57
    @100
    @21
    @10
    @111
    @106
    @57
    @10
    @61
    recnd
    subdid
    eqtrd
    eqtr4d
    @57
    @9
    @11
    @12
    @105
    @57
    @11
    @57
    @113
    @11
    cr
    wcel
    @114
    crp
    cr
    @10
    cR
    @84
    ffvelrni
    syl
    recnd
    @107
    mul32d
    eqtr4d
    sumeq2dv
    eqtrd
    oveq2d
    @37
    @93
    @79
    @25
    cmin
    @37
    @5
    @1
    @32
    @73
    @87
    @76
    mul12d
    oveq2d
    3eqtr3rd
    oveq2d
    eqtrd
    oveq1d
    @37
    @81
    @38
    @82
    @33
    cmin
    @37
    @81
    @26
    @1
    @3
    cmul
    co
    #
    cmin
    co
    #
    @1
    cdiv
    co
    #
    @38
    @37
    @78
    @116
    @1
    cdiv
    @37
    @78
    @20
    @115
    cmin
    co
    #
    @25
    caddc
    co
    @116
    @37
    @4
    @118
    @25
    caddc
    @37
    @4
    @19
    @1
    cmin
    co
    #
    @3
    cmul
    co
    @118
    @37
    @2
    @119
    @3
    cmul
    @37
    @83
    @2
    @119
    wceq
    @47
    @1
    cR
    va
    pntrval.r
    pntrval
    syl
    oveq1d
    @37
    @19
    @1
    @3
    @37
    @19
    @50
    recnd
    @87
    @49
    subdird
    eqtrd
    oveq1d
    @37
    @20
    @25
    @115
    @37
    @20
    @51
    recnd
    @86
    @37
    @1
    @3
    @87
    @49
    mulcld
    #
    addsubd
    eqtr4d
    oveq1d
    @37
    @117
    @27
    @115
    @1
    cdiv
    co
    #
    cmin
    co
    @38
    @37
    @26
    @115
    @1
    @37
    @26
    @68
    recnd
    @120
    @87
    @89
    divsubdird
    @37
    @121
    @3
    @27
    cmin
    @37
    @3
    @1
    @49
    @87
    @89
    divcan3d
    oveq2d
    eqtrd
    eqtrd
    @37
    @33
    @1
    @77
    @87
    @89
    divcan3d
    oveq12d
    3eqtr3rd
    3eqtrrd
    mpteq2dva
    wtru
    vx
    @0
    @29
    @34
    cr
    @37
    @27
    @28
    @69
    @37
    c2
    @3
    @52
    @48
    remulcld
    resubcld
    @37
    @33
    @3
    @37
    @5
    @32
    @54
    @75
    remulcld
    @48
    resubcld
    vx
    @0
    @29
    cmpt
    co1
    wcel
    wtru
    vx
    vn
    selberg3
    a1i
    wtru
    vx
    @0
    c2
    @32
    @3
    cdiv
    co
    #
    @3
    c2
    cdiv
    co
    #
    cmin
    co
    #
    cmul
    co
    #
    cmpt
    vx
    @0
    @34
    cmpt
    co1
    wtru
    vx
    @0
    @125
    @34
    @37
    @125
    c2
    @122
    cmul
    co
    #
    c2
    @123
    cmul
    co
    #
    cmin
    co
    @34
    @37
    c2
    @122
    @123
    @37
    c2
    @52
    recnd
    #
    @37
    @122
    @37
    @32
    @3
    @75
    @53
    rerpdivcld
    #
    recnd
    @37
    @123
    @37
    @3
    @48
    rehalfcld
    #
    recnd
    subdid
    @37
    @126
    @33
    @127
    @3
    cmin
    @37
    @33
    @126
    @37
    c2
    @3
    @32
    @128
    @49
    @76
    @72
    div32d
    eqcomd
    @37
    @3
    c2
    @49
    @128
    c2
    cc0
    wne
    @37
    2ne0
    a1i
    divcan2d
    oveq12d
    eqtrd
    mpteq2dva
    wtru
    vx
    @0
    c2
    @124
    cr
    @52
    @37
    @122
    @123
    @129
    @130
    resubcld
    vx
    @0
    c2
    cmpt
    co1
    wcel
    #
    wtru
    @0
    cr
    wss
    @71
    @131
    c1
    cpnf
    ioossre
    2cn
    vx
    @0
    c2
    o1const
    mp2an
    a1i
    vx
    @0
    @124
    cmpt
    co1
    wcel
    wtru
    vx
    vn
    vmalogdivsum
    a1i
    o1mul2
    eqeltrrd
    o1sub2
    eqeltrd
    trud
end
