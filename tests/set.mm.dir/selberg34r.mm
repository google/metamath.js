include "c1.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "clog.mm"
include "cmul.mm"
include "cfl.mm"
include "cfz.mm"
include "cdiv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn.mm"
include "crab.mm"
include "cvma.mm"
include "csu.mm"
include "cmin.mm"
include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "wtru.mm"
include "c2.mm"
include "wa.mm"
include "cr.mm"
include "2re.mm"
include "a1i.mm"
include "crp.mm"
include "elioore.mm"
include "adantl.mm"
include "1rp.mm"
include "1red.mm"
include "clt.mm"
include "eliooord.mm"
include "simpld.mm"
include "ltled.mm"
include "rpgecld.mm"
include "pntrf.mm"
include "ffvelrni.mm"
include "syl.mm"
include "relogcld.mm"
include "remulcld.mm"
include "recnd.mm"
include "rplogcld.mm"
include "rerpdivcld.mm"
include "fzfid.mm"
include "adantr.mm"
include "elfznn.mm"
include "nnrpd.mm"
include "rpdivcld.mm"
include "cfn.mm"
include "wss.mm"
include "dvdsssfz1.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "ssrab2.mm"
include "simpr.mm"
include "sseldi.mm"
include "vmacl.mm"
include "dvdsdivcl.mm"
include "sylan.mm"
include "fsumrecl.mm"
include "resubcld.mm"
include "mulcld.mm"
include "subcld.mm"
include "2cnd.mm"
include "rpne0d.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "divdiv32d.mm"
include "divcld.mm"
include "divrecd.mm"
include "divsubdird.mm"
include "divcan3d.mm"
include "rpcnd.mm"
include "div32d.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "3eqtr3d.mm"
include "mpteq2dva.mm"
include "rehalfcld.mm"
include "caddc.mm"
include "subdid.mm"
include "mul12d.mm"
include "mulassd.mm"
include "eqtr4d.mm"
include "oveq2d.mm"
include "sumeq2dv.mm"
include "fsumsub.mm"
include "fsummulc2.mm"
include "wceq.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "oveq1.mm"
include "adantrr.mm"
include "anasss.mm"
include "dvdsflsumcom.mm"
include "cc.mm"
include "ad2antrr.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divdiv1d.mm"
include "eqcomd.mm"
include "mulcomd.mm"
include "3eqtrd.mm"
include "subsub3d.mm"
include "2timesd.mm"
include "add32d.mm"
include "readdcld.mm"
include "addsubassd.mm"
include "divdird.mm"
include "selberg3r.mm"
include "selberg4r.mm"
include "o1add2.mm"
include "eqeltrd.mm"
include "ioossre.mm"
include "1cnd.mm"
include "halfcld.mm"
include "o1const.mm"
include "sylancr.mm"
include "o1mul2.mm"
include "eqeltrrd.mm"
include "trud.mm"

theorem selberg34r
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let vm: setvar m
  let vn: setvar n
  let va: setvar a
  let vd: setvar d
  let vk: setvar k
  let cA: class A
  let vb: setvar b
  let vc: setvar c
  assume pntrval.r: |- R = ( a e. RR+ |-> ( ( psi ` a ) - a ) )

  disjoint a m
  disjoint a n
  disjoint a x
  disjoint m n
  disjoint m x
  disjoint n x
  disjoint m y
  disjoint R m
  disjoint n y
  disjoint R n
  disjoint x y
  disjoint R x
  disjoint R y
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
  assert |- ( x e. ( 1 (,) +oo ) |-> ( ( ( ( R ` x ) x. ( log ` x ) ) - ( sum_ n e. ( 1 ... ( |_ ` x ) ) ( ( R ` ( x / n ) ) x. ( sum_ m e. { y e. NN | y || n } ( ( Lam ` m ) x. ( Lam ` ( n / m ) ) ) - ( ( Lam ` n ) x. ( log ` n ) ) ) ) / ( log ` x ) ) ) / x ) ) e. O(1)

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
    c1
    @1
    cfl
    cfv
    #
    cfz
    co
    #
    @1
    vn
    cv
    #
    cdiv
    co
    #
    cR
    cfv
    #
    vy
    cv
    @7
    cdvds
    wbr
    #
    vy
    cn
    crab
    #
    vm
    cv
    #
    cvma
    cfv
    #
    @7
    @12
    cdiv
    co
    #
    cvma
    cfv
    #
    cmul
    co
    #
    vm
    csu
    #
    @7
    cvma
    cfv
    #
    @7
    clog
    cfv
    #
    cmul
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
    @3
    cdiv
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
    vx
    @0
    c2
    @4
    cmul
    co
    #
    c2
    @3
    cdiv
    co
    #
    @23
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
    c1
    c2
    cdiv
    co
    #
    cmul
    co
    #
    cmpt
    @27
    co1
    wtru
    vx
    @0
    @34
    @26
    wtru
    @1
    @0
    wcel
    #
    wa
    #
    @32
    c2
    cdiv
    co
    @31
    c2
    cdiv
    co
    #
    @1
    cdiv
    co
    @34
    @26
    @36
    @31
    @1
    c2
    @36
    @28
    @30
    @36
    @28
    @36
    c2
    @4
    c2
    cr
    wcel
    @36
    2re
    a1i
    #
    @36
    @2
    @3
    @36
    @1
    crp
    wcel
    #
    @2
    cr
    wcel
    @36
    @1
    c1
    @35
    @1
    cr
    wcel
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
    @36
    1rp
    a1i
    @36
    c1
    @1
    @36
    1red
    #
    @40
    @36
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
    @35
    @42
    @43
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
    @36
    @1
    @45
    relogcld
    remulcld
    #
    remulcld
    #
    recnd
    #
    @36
    @29
    @23
    @36
    @29
    @36
    c2
    @3
    @38
    @36
    @1
    @40
    @44
    rplogcld
    #
    rerpdivcld
    #
    recnd
    #
    @36
    @23
    @36
    @6
    @22
    vn
    @36
    c1
    @5
    fzfid
    #
    @36
    @7
    @6
    wcel
    #
    wa
    #
    @9
    @21
    @55
    @8
    crp
    wcel
    @9
    cr
    wcel
    #
    @55
    @1
    @7
    @36
    @39
    @54
    @45
    adantr
    @55
    @7
    @54
    @7
    cn
    wcel
    #
    @36
    @7
    @5
    elfznn
    adantl
    #
    nnrpd
    #
    rpdivcld
    crp
    cr
    @8
    cR
    @46
    ffvelrni
    syl
    #
    @55
    @17
    @20
    @55
    @11
    @16
    vm
    @55
    c1
    @7
    cfz
    co
    #
    cfn
    wcel
    @11
    @61
    wss
    #
    @11
    cfn
    wcel
    @55
    c1
    @7
    fzfid
    @55
    @57
    @62
    @58
    @7
    vy
    dvdsssfz1
    syl
    @61
    @11
    ssfi
    syl2anc
    #
    @55
    @12
    @11
    wcel
    #
    wa
    #
    @13
    @15
    @65
    @12
    cn
    wcel
    #
    @13
    cr
    wcel
    #
    @65
    @11
    cn
    @12
    @10
    vy
    cn
    ssrab2
    #
    @55
    @64
    simpr
    sseldi
    @12
    vmacl
    #
    syl
    #
    @65
    @14
    cn
    wcel
    @15
    cr
    wcel
    #
    @65
    @11
    cn
    @14
    @68
    @55
    @57
    @64
    @14
    @11
    wcel
    @58
    vy
    @12
    @7
    dvdsdivcl
    sylan
    sseldi
    @14
    vmacl
    syl
    #
    remulcld
    #
    fsumrecl
    #
    @55
    @18
    @19
    @55
    @57
    @18
    cr
    wcel
    @58
    @7
    vmacl
    syl
    #
    @55
    @7
    @59
    relogcld
    #
    remulcld
    resubcld
    remulcld
    fsumrecl
    #
    recnd
    #
    mulcld
    #
    subcld
    #
    @36
    @1
    @40
    recnd
    #
    @36
    2cnd
    #
    @36
    @1
    @45
    rpne0d
    #
    c2
    cc0
    wne
    @36
    2ne0
    a1i
    #
    divdiv32d
    @36
    @32
    c2
    @36
    @31
    @1
    @80
    @81
    @83
    divcld
    @82
    @84
    divrecd
    @36
    @37
    @25
    @1
    cdiv
    @36
    @37
    @28
    c2
    cdiv
    co
    #
    @30
    c2
    cdiv
    co
    #
    cmin
    co
    @25
    @36
    @28
    @30
    c2
    @49
    @79
    @82
    @84
    divsubdird
    @36
    @85
    @4
    @86
    @24
    cmin
    @36
    @4
    c2
    @36
    @4
    @47
    recnd
    #
    @82
    @84
    divcan3d
    @36
    @86
    c2
    @24
    cmul
    co
    #
    c2
    cdiv
    co
    @24
    @36
    @30
    @88
    c2
    cdiv
    @36
    c2
    @3
    @23
    @82
    @36
    @3
    @50
    rpcnd
    @78
    @36
    @3
    @50
    rpne0d
    div32d
    oveq1d
    @36
    @24
    c2
    @36
    @24
    @36
    @23
    @3
    @77
    @50
    rerpdivcld
    recnd
    @82
    @84
    divcan3d
    eqtrd
    oveq12d
    eqtrd
    oveq1d
    3eqtr3d
    mpteq2dva
    wtru
    vx
    @0
    @32
    @33
    cr
    @36
    @31
    @1
    @36
    @28
    @30
    @48
    @36
    @29
    @23
    @51
    @77
    remulcld
    resubcld
    @45
    rerpdivcld
    @36
    c1
    @41
    rehalfcld
    wtru
    vx
    @0
    @32
    cmpt
    vx
    @0
    @4
    @29
    @6
    @18
    @9
    cmul
    co
    #
    @19
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
    @4
    @29
    @6
    @13
    c1
    @1
    @12
    cdiv
    co
    #
    cfl
    cfv
    #
    cfz
    co
    #
    vk
    cv
    #
    cvma
    cfv
    #
    @95
    @98
    cdiv
    co
    #
    cR
    cfv
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
    vm
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
    caddc
    co
    #
    cmpt
    co1
    wtru
    vx
    @0
    @32
    @109
    @36
    @32
    @93
    @107
    caddc
    co
    #
    @1
    cdiv
    co
    @109
    @36
    @31
    @110
    @1
    cdiv
    @36
    @31
    @28
    @92
    caddc
    co
    #
    @106
    cmin
    co
    #
    @93
    @4
    caddc
    co
    #
    @106
    cmin
    co
    @110
    @36
    @31
    @28
    @106
    @92
    cmin
    co
    #
    cmin
    co
    @112
    @36
    @30
    @114
    @28
    cmin
    @36
    @30
    @29
    @105
    @91
    cmin
    co
    #
    cmul
    co
    @114
    @36
    @23
    @115
    @29
    cmul
    @36
    @23
    @6
    @9
    @17
    cmul
    co
    #
    @90
    cmin
    co
    #
    vn
    csu
    @6
    @116
    vn
    csu
    #
    @91
    cmin
    co
    @115
    @36
    @6
    @22
    @117
    vn
    @55
    @22
    @116
    @9
    @20
    cmul
    co
    #
    cmin
    co
    @117
    @55
    @9
    @17
    @20
    @55
    @9
    @60
    recnd
    #
    @55
    @17
    @74
    recnd
    #
    @55
    @18
    @19
    @55
    @18
    @75
    recnd
    #
    @55
    @19
    @76
    recnd
    #
    mulcld
    subdid
    @55
    @119
    @90
    @116
    cmin
    @55
    @119
    @18
    @9
    @19
    cmul
    co
    cmul
    co
    @90
    @55
    @9
    @18
    @19
    @120
    @122
    @123
    mul12d
    @55
    @18
    @9
    @19
    @122
    @120
    @123
    mulassd
    eqtr4d
    oveq2d
    eqtrd
    sumeq2dv
    @36
    @6
    @116
    @90
    vn
    @53
    @55
    @9
    @17
    @120
    @121
    mulcld
    @55
    @89
    @19
    @55
    @18
    @9
    @122
    @120
    mulcld
    @123
    mulcld
    fsumsub
    @36
    @118
    @105
    @91
    cmin
    @36
    @118
    @6
    @11
    @9
    @16
    cmul
    co
    #
    vm
    csu
    #
    vn
    csu
    @6
    @97
    @1
    @12
    @98
    cmul
    co
    #
    cdiv
    co
    #
    cR
    cfv
    #
    @13
    @126
    @12
    cdiv
    co
    #
    cvma
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    vm
    csu
    @105
    @36
    @6
    @116
    @125
    vn
    @55
    @11
    @16
    @9
    vm
    @63
    @120
    @65
    @16
    @73
    recnd
    fsummulc2
    sumeq2dv
    @36
    vy
    @1
    @124
    @132
    vk
    vn
    vm
    @7
    @126
    wceq
    #
    @9
    @128
    @16
    @131
    cmul
    @134
    @8
    @127
    cR
    @7
    @126
    @1
    cdiv
    oveq2
    fveq2d
    @134
    @15
    @130
    @13
    cmul
    @134
    @14
    @129
    cvma
    @7
    @126
    @12
    cdiv
    oveq1
    fveq2d
    oveq2d
    oveq12d
    @40
    @36
    @54
    @64
    wa
    wa
    #
    @124
    @135
    @9
    @16
    @36
    @54
    @56
    @64
    @60
    adantrr
    @135
    @13
    @15
    @36
    @54
    @64
    @67
    @70
    anasss
    @36
    @54
    @64
    @71
    @72
    anasss
    remulcld
    remulcld
    recnd
    dvdsflsumcom
    @36
    @6
    @133
    @104
    vm
    @36
    @12
    @6
    wcel
    #
    wa
    #
    @133
    @97
    @13
    @102
    cmul
    co
    #
    vk
    csu
    @104
    @137
    @97
    @132
    @138
    vk
    @137
    @98
    @97
    wcel
    #
    wa
    #
    @132
    @101
    @13
    @99
    cmul
    co
    #
    cmul
    co
    @141
    @101
    cmul
    co
    @138
    @140
    @128
    @101
    @131
    @141
    cmul
    @140
    @127
    @100
    cR
    @140
    @100
    @127
    @140
    @1
    @12
    @98
    @36
    @1
    cc
    wcel
    @136
    @139
    @81
    ad2antrr
    @140
    @12
    @137
    @12
    crp
    wcel
    @139
    @137
    @12
    @136
    @66
    @36
    @12
    @5
    elfznn
    adantl
    #
    nnrpd
    adantr
    #
    rpcnd
    #
    @140
    @98
    @139
    @98
    cn
    wcel
    #
    @137
    @98
    @96
    elfznn
    adantl
    #
    nncnd
    #
    @140
    @12
    @143
    rpne0d
    #
    @140
    @98
    @146
    nnne0d
    divdiv1d
    eqcomd
    fveq2d
    @140
    @130
    @99
    @13
    cmul
    @140
    @129
    @98
    cvma
    @140
    @98
    @12
    @147
    @144
    @148
    divcan3d
    fveq2d
    oveq2d
    oveq12d
    @140
    @101
    @141
    @140
    @101
    @140
    @100
    crp
    wcel
    @101
    cr
    wcel
    @140
    @95
    @98
    @140
    @1
    @12
    @36
    @39
    @136
    @139
    @45
    ad2antrr
    @143
    rpdivcld
    @140
    @98
    @146
    nnrpd
    rpdivcld
    crp
    cr
    @100
    cR
    @46
    ffvelrni
    syl
    #
    recnd
    #
    @140
    @13
    @99
    @137
    @13
    cc
    wcel
    @139
    @137
    @13
    @137
    @66
    @67
    @142
    @69
    syl
    #
    recnd
    #
    adantr
    #
    @140
    @99
    @140
    @145
    @99
    cr
    wcel
    @146
    @98
    vmacl
    syl
    #
    recnd
    #
    mulcld
    mulcomd
    @140
    @13
    @99
    @101
    @153
    @155
    @150
    mulassd
    3eqtrd
    sumeq2dv
    @137
    @97
    @102
    @13
    vk
    @137
    c1
    @96
    fzfid
    #
    @152
    @140
    @102
    @140
    @99
    @101
    @154
    @149
    remulcld
    #
    recnd
    fsummulc2
    eqtr4d
    sumeq2dv
    3eqtrd
    oveq1d
    3eqtrd
    oveq2d
    @36
    @29
    @105
    @91
    @52
    @36
    @105
    @36
    @6
    @104
    vm
    @53
    @137
    @13
    @103
    @151
    @137
    @97
    @102
    vk
    @156
    @157
    fsumrecl
    remulcld
    fsumrecl
    #
    recnd
    #
    @36
    @91
    @36
    @6
    @90
    vn
    @53
    @55
    @89
    @19
    @55
    @18
    @9
    @75
    @60
    remulcld
    @76
    remulcld
    fsumrecl
    #
    recnd
    subdid
    eqtrd
    oveq2d
    @36
    @28
    @106
    @92
    @49
    @36
    @29
    @105
    @52
    @159
    mulcld
    #
    @36
    @92
    @36
    @29
    @91
    @51
    @160
    remulcld
    #
    recnd
    #
    subsub3d
    eqtrd
    @36
    @111
    @113
    @106
    cmin
    @36
    @111
    @4
    @4
    caddc
    co
    #
    @92
    caddc
    co
    @113
    @36
    @28
    @164
    @92
    caddc
    @36
    @4
    @87
    2timesd
    oveq1d
    @36
    @4
    @92
    @4
    @87
    @163
    @87
    add32d
    eqtr4d
    oveq1d
    @36
    @93
    @4
    @106
    @36
    @93
    @36
    @4
    @92
    @47
    @162
    readdcld
    #
    recnd
    #
    @87
    @161
    addsubassd
    3eqtrd
    oveq1d
    @36
    @93
    @107
    @1
    @166
    @36
    @4
    @106
    @87
    @161
    subcld
    @81
    @83
    divdird
    eqtrd
    mpteq2dva
    wtru
    vx
    @0
    @94
    @108
    cr
    @36
    @93
    @1
    @165
    @45
    rerpdivcld
    @36
    @107
    @1
    @36
    @4
    @106
    @47
    @36
    @29
    @105
    @51
    @158
    remulcld
    resubcld
    @45
    rerpdivcld
    vx
    @0
    @94
    cmpt
    co1
    wcel
    wtru
    vx
    cR
    vn
    va
    pntrval.r
    selberg3r
    a1i
    vx
    @0
    @108
    cmpt
    co1
    wcel
    wtru
    vx
    cR
    vk
    vm
    va
    pntrval.r
    selberg4r
    a1i
    o1add2
    eqeltrd
    wtru
    @0
    cr
    wss
    @33
    cc
    wcel
    vx
    @0
    @33
    cmpt
    co1
    wcel
    c1
    cpnf
    ioossre
    wtru
    c1
    wtru
    1cnd
    halfcld
    vx
    @0
    @33
    o1const
    sylancr
    o1mul2
    eqeltrrd
    trud
end
