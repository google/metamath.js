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
include "cmin.mm"
include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "wtru.mm"
include "cchp.mm"
include "caddc.mm"
include "wa.mm"
include "crp.mm"
include "wceq.mm"
include "cr.mm"
include "elioore.mm"
include "adantl.mm"
include "1rp.mm"
include "a1i.mm"
include "1red.mm"
include "clt.mm"
include "wbr.mm"
include "eliooord.mm"
include "simpld.mm"
include "ltled.mm"
include "rpgecld.mm"
include "pntrval.mm"
include "syl.mm"
include "oveq1d.mm"
include "chpcl.mm"
include "recnd.mm"
include "relogcld.mm"
include "subdird.mm"
include "eqtrd.mm"
include "ad2antrr.mm"
include "cn.mm"
include "elfznn.mm"
include "nnrpd.mm"
include "adantr.mm"
include "rpdivcld.mm"
include "oveq2d.mm"
include "vmacl.mm"
include "nndivred.mm"
include "subdid.mm"
include "sumeq2dv.mm"
include "fzfid.mm"
include "remulcld.mm"
include "mulcld.mm"
include "fsumsub.mm"
include "fsumrecl.mm"
include "fsumcl.mm"
include "2re.mm"
include "rplogcld.mm"
include "rerpdivcld.mm"
include "oveq12d.mm"
include "sub4d.mm"
include "resubcld.mm"
include "rpne0d.mm"
include "divsubdird.mm"
include "divcan3d.mm"
include "divassd.mm"
include "fsumdivc.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "div12d.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "div32d.mm"
include "eqtr3d.mm"
include "3eqtr4d.mm"
include "divcld.mm"
include "subsub2d.mm"
include "mpteq2dva.mm"
include "selberg4.mm"
include "2cnd.mm"
include "rehalfcld.mm"
include "eqcomd.mm"
include "2ne0.mm"
include "divcan2d.mm"
include "wss.mm"
include "ioossre.mm"
include "o1const.mm"
include "sylancr.mm"
include "2vmadivsum.mm"
include "o1mul2.mm"
include "eqeltrrd.mm"
include "o1add2.mm"
include "eqeltrd.mm"
include "trud.mm"

theorem selberg4r
  let vx: setvar x
  let cR: class R
  let vm: setvar m
  let vn: setvar n
  let va: setvar a
  let vd: setvar d
  let vk: setvar k
  let cA: class A
  let vb: setvar b
  let vc: setvar c
  let vy: setvar y
  assume pntrval.r: |- R = ( a e. RR+ |-> ( ( psi ` a ) - a ) )

  disjoint a m
  disjoint a n
  disjoint a x
  disjoint m n
  disjoint m x
  disjoint n x
  disjoint R m
  disjoint R n
  disjoint R x
  disjoint a d
  disjoint a k
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
  disjoint n y
  disjoint x y
  disjoint R y
  assert |- ( x e. ( 1 (,) +oo ) |-> ( ( ( ( R ` x ) x. ( log ` x ) ) - ( ( 2 / ( log ` x ) ) x. sum_ n e. ( 1 ... ( |_ ` x ) ) ( ( Lam ` n ) x. sum_ m e. ( 1 ... ( |_ ` ( x / n ) ) ) ( ( Lam ` m ) x. ( R ` ( ( x / n ) / m ) ) ) ) ) ) / x ) ) e. O(1)

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
    c1
    @1
    @8
    cdiv
    co
    #
    cfl
    cfv
    #
    cfz
    co
    #
    vm
    cv
    #
    cvma
    cfv
    #
    @10
    @13
    cdiv
    co
    #
    cR
    cfv
    #
    cmul
    co
    #
    vm
    csu
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
    cmin
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
    @24
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
    @12
    @14
    @15
    cchp
    cfv
    #
    cmul
    co
    #
    vm
    csu
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
    cmin
    co
    #
    @1
    cdiv
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
    @14
    @13
    cdiv
    co
    #
    vm
    csu
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
    @3
    cmin
    co
    #
    caddc
    co
    #
    cmpt
    co1
    wtru
    vx
    @0
    @23
    @42
    wtru
    @1
    @0
    wcel
    #
    wa
    #
    @23
    @33
    @1
    @3
    cmul
    co
    #
    @5
    @7
    @9
    @12
    @14
    @15
    cmul
    co
    #
    vm
    csu
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
    cmin
    co
    #
    cmin
    co
    #
    @1
    cdiv
    co
    #
    @42
    @44
    @22
    @52
    @1
    cdiv
    @44
    @22
    @26
    @45
    cmin
    co
    #
    @32
    @50
    cmin
    co
    #
    cmin
    co
    @52
    @44
    @4
    @54
    @21
    @55
    cmin
    @44
    @4
    @25
    @1
    cmin
    co
    #
    @3
    cmul
    co
    @54
    @44
    @2
    @56
    @3
    cmul
    @44
    @1
    crp
    wcel
    #
    @2
    @56
    wceq
    @44
    @1
    c1
    @43
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
    @44
    1rp
    a1i
    @44
    c1
    @1
    @44
    1red
    @59
    @44
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
    @43
    @60
    @61
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
    @1
    cR
    va
    pntrval.r
    pntrval
    syl
    oveq1d
    @44
    @25
    @1
    @3
    @44
    @25
    @44
    @58
    @25
    cr
    wcel
    @59
    @1
    chpcl
    syl
    #
    recnd
    @44
    @1
    @59
    recnd
    #
    @44
    @3
    @44
    @1
    @63
    relogcld
    #
    recnd
    #
    subdird
    eqtrd
    @44
    @21
    @5
    @31
    @49
    cmin
    co
    #
    cmul
    co
    @55
    @44
    @20
    @68
    @5
    cmul
    @44
    @20
    @7
    @30
    @48
    cmin
    co
    #
    vn
    csu
    @68
    @44
    @7
    @19
    @69
    vn
    @44
    @8
    @7
    wcel
    #
    wa
    #
    @19
    @9
    @29
    @47
    cmin
    co
    #
    cmul
    co
    @69
    @71
    @18
    @72
    @9
    cmul
    @71
    @18
    @12
    @28
    @46
    cmin
    co
    #
    vm
    csu
    @72
    @71
    @12
    @17
    @73
    vm
    @71
    @13
    @12
    wcel
    #
    wa
    #
    @17
    @14
    @27
    @15
    cmin
    co
    #
    cmul
    co
    @73
    @75
    @16
    @76
    @14
    cmul
    @75
    @15
    crp
    wcel
    @16
    @76
    wceq
    @75
    @10
    @13
    @75
    @1
    @8
    @44
    @57
    @70
    @74
    @63
    ad2antrr
    @71
    @8
    crp
    wcel
    @74
    @71
    @8
    @70
    @8
    cn
    wcel
    #
    @44
    @8
    @6
    elfznn
    adantl
    #
    nnrpd
    adantr
    rpdivcld
    @75
    @13
    @74
    @13
    cn
    wcel
    #
    @71
    @13
    @11
    elfznn
    adantl
    #
    nnrpd
    rpdivcld
    @15
    cR
    va
    pntrval.r
    pntrval
    syl
    oveq2d
    @75
    @14
    @27
    @15
    @75
    @14
    @75
    @79
    @14
    cr
    wcel
    @80
    @13
    vmacl
    syl
    #
    recnd
    #
    @75
    @27
    @75
    @15
    cr
    wcel
    @27
    cr
    wcel
    @75
    @10
    @13
    @71
    @10
    cr
    wcel
    @74
    @71
    @1
    @8
    @44
    @58
    @70
    @59
    adantr
    @78
    nndivred
    adantr
    #
    @80
    nndivred
    #
    @15
    chpcl
    syl
    #
    recnd
    @75
    @15
    @84
    recnd
    #
    subdid
    eqtrd
    sumeq2dv
    @71
    @12
    @28
    @46
    vm
    @71
    c1
    @11
    fzfid
    #
    @75
    @28
    @75
    @14
    @27
    @81
    @85
    remulcld
    #
    recnd
    @75
    @14
    @15
    @82
    @86
    mulcld
    #
    fsumsub
    eqtrd
    oveq2d
    @71
    @9
    @29
    @47
    @71
    @9
    @71
    @77
    @9
    cr
    wcel
    @78
    @8
    vmacl
    syl
    #
    recnd
    #
    @71
    @29
    @71
    @12
    @28
    vm
    @87
    @88
    fsumrecl
    #
    recnd
    @71
    @12
    @46
    vm
    @87
    @89
    fsumcl
    #
    subdid
    eqtrd
    sumeq2dv
    @44
    @7
    @30
    @48
    vn
    @44
    c1
    @6
    fzfid
    #
    @71
    @30
    @71
    @9
    @29
    @90
    @92
    remulcld
    #
    recnd
    @71
    @9
    @47
    @91
    @93
    mulcld
    #
    fsumsub
    eqtrd
    oveq2d
    @44
    @5
    @31
    @49
    @44
    @5
    @44
    c2
    @3
    c2
    cr
    wcel
    @44
    2re
    a1i
    #
    @44
    @1
    @59
    @62
    rplogcld
    #
    rerpdivcld
    #
    recnd
    #
    @44
    @31
    @44
    @7
    @30
    vn
    @94
    @95
    fsumrecl
    #
    recnd
    @44
    @7
    @48
    vn
    @94
    @96
    fsumcl
    #
    subdid
    eqtrd
    oveq12d
    @44
    @26
    @45
    @32
    @50
    @44
    @26
    @44
    @25
    @3
    @64
    @66
    remulcld
    #
    recnd
    @44
    @1
    @3
    @65
    @67
    mulcld
    @44
    @32
    @44
    @5
    @31
    @99
    @101
    remulcld
    #
    recnd
    @44
    @5
    @49
    @100
    @102
    mulcld
    sub4d
    eqtrd
    oveq1d
    @44
    @53
    @34
    @51
    @1
    cdiv
    co
    #
    cmin
    co
    #
    @42
    @44
    @33
    @51
    @1
    @44
    @33
    @44
    @26
    @32
    @103
    @104
    resubcld
    #
    recnd
    #
    @44
    @51
    @44
    @45
    @50
    @44
    @1
    @3
    @59
    @66
    remulcld
    #
    @44
    @5
    @49
    @99
    @44
    @7
    @48
    vn
    @94
    @71
    @9
    @47
    @90
    @71
    @12
    @46
    vm
    @87
    @75
    @14
    @15
    @81
    @84
    remulcld
    #
    fsumrecl
    #
    remulcld
    #
    fsumrecl
    #
    remulcld
    resubcld
    recnd
    @65
    @44
    @1
    @63
    rpne0d
    #
    divsubdird
    @44
    @106
    @34
    @3
    @40
    cmin
    co
    #
    cmin
    co
    @42
    @44
    @105
    @115
    @34
    cmin
    @44
    @105
    @45
    @1
    cdiv
    co
    #
    @50
    @1
    cdiv
    co
    #
    cmin
    co
    @115
    @44
    @45
    @50
    @1
    @44
    @45
    @109
    recnd
    @44
    @5
    @49
    @100
    @44
    @49
    @113
    recnd
    #
    mulcld
    @65
    @114
    divsubdird
    @44
    @116
    @3
    @117
    @40
    cmin
    @44
    @3
    @1
    @67
    @65
    @114
    divcan3d
    @44
    @117
    @5
    @49
    @1
    cdiv
    co
    #
    cmul
    co
    @40
    @44
    @5
    @49
    @1
    @100
    @118
    @65
    @114
    divassd
    @44
    @119
    @39
    @5
    cmul
    @44
    @119
    @7
    @48
    @1
    cdiv
    co
    #
    vn
    csu
    @39
    @44
    @7
    @48
    @1
    vn
    @94
    @65
    @71
    @48
    @112
    recnd
    @114
    fsumdivc
    @44
    @7
    @120
    @38
    vn
    @71
    @9
    @47
    @1
    cdiv
    co
    #
    cmul
    co
    @9
    @37
    @8
    cdiv
    co
    #
    cmul
    co
    @120
    @38
    @71
    @121
    @122
    @9
    cmul
    @71
    @12
    @46
    @1
    cdiv
    co
    #
    vm
    csu
    @12
    @36
    @8
    cdiv
    co
    #
    vm
    csu
    @121
    @122
    @71
    @12
    @123
    @124
    vm
    @75
    @123
    @1
    @124
    cmul
    co
    #
    @1
    cdiv
    co
    @124
    @75
    @46
    @125
    @1
    cdiv
    @75
    @10
    @36
    cmul
    co
    @46
    @125
    @75
    @10
    @14
    @13
    @75
    @10
    @83
    recnd
    @82
    @75
    @13
    @80
    nncnd
    @75
    @13
    @80
    nnne0d
    div12d
    @75
    @1
    @8
    @36
    @71
    @1
    cc
    wcel
    #
    @74
    @44
    @126
    @70
    @65
    adantr
    #
    adantr
    #
    @71
    @8
    cc
    wcel
    @74
    @71
    @8
    @78
    nncnd
    #
    adantr
    @75
    @36
    @75
    @14
    @13
    @81
    @80
    nndivred
    #
    recnd
    #
    @71
    @8
    cc0
    wne
    @74
    @71
    @8
    @78
    nnne0d
    #
    adantr
    div32d
    eqtr3d
    oveq1d
    @75
    @124
    @1
    @75
    @124
    @75
    @36
    @8
    @130
    @71
    @77
    @74
    @78
    adantr
    nndivred
    recnd
    @128
    @71
    @1
    cc0
    wne
    #
    @74
    @44
    @133
    @70
    @114
    adantr
    #
    adantr
    divcan3d
    eqtrd
    sumeq2dv
    @71
    @12
    @46
    @1
    vm
    @87
    @127
    @75
    @46
    @110
    recnd
    @134
    fsumdivc
    @71
    @12
    @36
    @8
    vm
    @87
    @129
    @131
    @132
    fsumdivc
    3eqtr4d
    oveq2d
    @71
    @9
    @47
    @1
    @91
    @71
    @47
    @111
    recnd
    @127
    @134
    divassd
    @71
    @9
    @8
    @37
    @91
    @129
    @71
    @37
    @71
    @12
    @36
    vm
    @87
    @130
    fsumrecl
    #
    recnd
    @132
    div32d
    3eqtr4d
    sumeq2dv
    eqtrd
    oveq2d
    eqtrd
    oveq12d
    eqtrd
    oveq2d
    @44
    @34
    @3
    @40
    @44
    @33
    @1
    @108
    @65
    @114
    divcld
    @67
    @44
    @40
    @44
    @5
    @39
    @99
    @44
    @7
    @38
    vn
    @94
    @71
    @35
    @37
    @71
    @9
    @8
    @90
    @78
    nndivred
    @135
    remulcld
    fsumrecl
    #
    remulcld
    #
    recnd
    subsub2d
    eqtrd
    eqtrd
    eqtrd
    mpteq2dva
    wtru
    vx
    @0
    @34
    @41
    cr
    @44
    @33
    @1
    @107
    @63
    rerpdivcld
    @44
    @40
    @3
    @137
    @66
    resubcld
    vx
    @0
    @34
    cmpt
    co1
    wcel
    wtru
    vx
    vm
    vn
    selberg4
    a1i
    wtru
    vx
    @0
    c2
    @39
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
    @41
    cmpt
    co1
    wtru
    vx
    @0
    @141
    @41
    @44
    @141
    c2
    @138
    cmul
    co
    #
    c2
    @139
    cmul
    co
    #
    cmin
    co
    @41
    @44
    c2
    @138
    @139
    @44
    2cnd
    #
    @44
    @138
    @44
    @39
    @3
    @136
    @98
    rerpdivcld
    #
    recnd
    @44
    @139
    @44
    @3
    @66
    rehalfcld
    #
    recnd
    subdid
    @44
    @142
    @40
    @143
    @3
    cmin
    @44
    @40
    @142
    @44
    c2
    @3
    @39
    @144
    @67
    @44
    @39
    @136
    recnd
    @44
    @3
    @98
    rpne0d
    div32d
    eqcomd
    @44
    @3
    c2
    @67
    @144
    c2
    cc0
    wne
    @44
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
    @140
    cr
    @97
    @44
    @138
    @139
    @145
    @146
    resubcld
    wtru
    @0
    cr
    wss
    c2
    cc
    wcel
    vx
    @0
    c2
    cmpt
    co1
    wcel
    c1
    cpnf
    ioossre
    wtru
    2cnd
    vx
    @0
    c2
    o1const
    sylancr
    vx
    @0
    @140
    cmpt
    co1
    wcel
    wtru
    vx
    vm
    vn
    2vmadivsum
    a1i
    o1mul2
    eqeltrrd
    o1add2
    eqeltrd
    trud
end
