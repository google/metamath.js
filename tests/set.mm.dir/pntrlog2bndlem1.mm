include "c1.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cabs.mm"
include "clog.mm"
include "cmul.mm"
include "cfl.mm"
include "cfz.mm"
include "cdiv.mm"
include "cmin.mm"
include "csu.mm"
include "cmpt.mm"
include "clo1.mm"
include "wcel.mm"
include "wtru.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn.mm"
include "crab.mm"
include "cvma.mm"
include "cr.mm"
include "1red.mm"
include "co1.mm"
include "selberg34r.mm"
include "wa.mm"
include "crp.mm"
include "elioore.mm"
include "adantl.mm"
include "1rp.mm"
include "a1i.mm"
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
include "rplogcld.mm"
include "rerpdivcld.mm"
include "recnd.mm"
include "lo1o12.mm"
include "mpbii.mm"
include "abscld.mm"
include "nnred.mm"
include "pntsf.mm"
include "cle.mm"
include "mulcld.mm"
include "rpne0d.mm"
include "divcld.mm"
include "subcld.mm"
include "fsumabs.mm"
include "absmuld.mm"
include "absge0d.mm"
include "caddc.mm"
include "abs2dif2d.mm"
include "addcld.mm"
include "pncan2d.mm"
include "cuz.mm"
include "elfzuz.mm"
include "readdcld.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "breq2.mm"
include "rabbidv.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "sumeq12rdv.mm"
include "fsumm1.mm"
include "pntsval2.mm"
include "cz.mm"
include "nnzd.mm"
include "flid.mm"
include "sumeq1d.mm"
include "eqtrd.mm"
include "1zzd.mm"
include "zsubcld.mm"
include "addcomd.mm"
include "3eqtr4d.mm"
include "oveq1d.mm"
include "cc0.mm"
include "vmage0.mm"
include "mulge0d.mm"
include "fsumge0.mm"
include "absidd.mm"
include "nnge1d.mm"
include "logge0d.mm"
include "breqtrrd.mm"
include "lemul2ad.mm"
include "eqbrtrd.mm"
include "fsumle.mm"
include "letrd.mm"
include "lediv1dd.mm"
include "lesub2dd.mm"
include "absdivd.mm"
include "abs2difd.mm"
include "eqbrtrrd.mm"
include "rpge0d.mm"
include "adantrr.mm"
include "lo1le.mm"
include "trud.mm"

theorem pntrlog2bndlem1
  let vx: setvar x
  let cR: class R
  let cS: class S
  let vi: setvar i
  let vn: setvar n
  let va: setvar a
  let vc: setvar c
  let vk: setvar k
  let vm: setvar m
  let vy: setvar y
  let cA: class A
  let cB: class B
  let wph: wff ph
  let cT: class T
  assume pntsval.1: |- S = ( a e. RR |-> sum_ i e. ( 1 ... ( |_ ` a ) ) ( ( Lam ` i ) x. ( ( log ` i ) + ( psi ` ( a / i ) ) ) ) )
  assume pntrlog2bnd.r: |- R = ( a e. RR+ |-> ( ( psi ` a ) - a ) )

  disjoint a i
  disjoint a n
  disjoint a x
  disjoint i n
  disjoint i x
  disjoint n x
  disjoint S n
  disjoint S x
  disjoint R n
  disjoint R x
  disjoint a c
  disjoint a k
  disjoint a m
  disjoint a y
  disjoint A a
  disjoint c i
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c x
  disjoint c y
  disjoint A c
  disjoint i k
  disjoint i m
  disjoint i y
  disjoint A i
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n y
  disjoint A n
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B n
  disjoint B x
  disjoint B y
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint S c
  disjoint S k
  disjoint S m
  disjoint S y
  disjoint R c
  disjoint R m
  disjoint R y
  disjoint T m
  disjoint T n
  assert |- ( x e. ( 1 (,) +oo ) |-> ( ( ( ( abs ` ( R ` x ) ) x. ( log ` x ) ) - ( sum_ n e. ( 1 ... ( |_ ` x ) ) ( ( abs ` ( R ` ( x / n ) ) ) x. ( ( S ` n ) - ( S ` ( n - 1 ) ) ) ) / ( log ` x ) ) ) / x ) ) e. <_O(1)

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
    cabs
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
    cabs
    cfv
    #
    @8
    cS
    cfv
    #
    @8
    c1
    cmin
    co
    #
    cS
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
    @4
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
    clo1
    wcel
    wtru
    vx
    @0
    @2
    @4
    cmul
    co
    #
    @7
    @10
    vy
    cv
    #
    @8
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
    @8
    @25
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
    @8
    cvma
    cfv
    #
    @8
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
    @4
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
    cabs
    cfv
    #
    @20
    c1
    cr
    wtru
    1red
    wtru
    vx
    @0
    @39
    cmpt
    co1
    wcel
    vx
    @0
    @40
    cmpt
    clo1
    wcel
    vx
    vy
    cR
    vm
    vn
    va
    pntrlog2bnd.r
    selberg34r
    wtru
    vx
    @0
    @39
    wtru
    @1
    @0
    wcel
    #
    wa
    #
    @39
    @42
    @38
    @1
    @42
    @21
    @37
    @42
    @2
    @4
    @42
    @1
    crp
    wcel
    #
    @2
    cr
    wcel
    @42
    @1
    c1
    @41
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
    @42
    1rp
    a1i
    @42
    c1
    @1
    @42
    1red
    @44
    @42
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
    @41
    @45
    @46
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
    #
    rpgecld
    #
    crp
    cr
    @1
    cR
    cR
    va
    pntrlog2bnd.r
    pntrf
    #
    ffvelrni
    syl
    #
    @42
    @1
    @49
    relogcld
    #
    remulcld
    @42
    @36
    @4
    @42
    @7
    @35
    vn
    @42
    c1
    @6
    fzfid
    #
    @42
    @8
    @7
    wcel
    #
    wa
    #
    @10
    @34
    @55
    @9
    crp
    wcel
    @10
    cr
    wcel
    @55
    @1
    @8
    @42
    @43
    @54
    @49
    adantr
    @55
    @8
    @54
    @8
    cn
    wcel
    #
    @42
    @8
    @6
    elfznn
    adantl
    #
    nnrpd
    #
    rpdivcld
    crp
    cr
    @9
    cR
    @50
    ffvelrni
    syl
    #
    @55
    @30
    @33
    @55
    @24
    @29
    vm
    @55
    c1
    @8
    cfz
    co
    #
    cfn
    wcel
    @24
    @60
    wss
    #
    @24
    cfn
    wcel
    @55
    c1
    @8
    fzfid
    @55
    @56
    @61
    @57
    @8
    vy
    dvdsssfz1
    syl
    @60
    @24
    ssfi
    syl2anc
    #
    @55
    @25
    @24
    wcel
    #
    wa
    #
    @26
    @28
    @64
    @25
    cn
    wcel
    #
    @26
    cr
    wcel
    #
    @64
    @24
    cn
    @25
    @23
    vy
    cn
    ssrab2
    #
    @55
    @63
    simpr
    sseldi
    #
    @25
    vmacl
    #
    syl
    #
    @64
    @27
    cn
    wcel
    #
    @28
    cr
    wcel
    @64
    @24
    cn
    @27
    @67
    @55
    @56
    @63
    @27
    @24
    wcel
    @57
    vy
    @25
    @8
    dvdsdivcl
    sylan
    sseldi
    #
    @27
    vmacl
    syl
    #
    remulcld
    #
    fsumrecl
    #
    @55
    @31
    @32
    @55
    @56
    @31
    cr
    wcel
    @57
    @8
    vmacl
    syl
    #
    @55
    @8
    @58
    relogcld
    #
    remulcld
    #
    resubcld
    #
    remulcld
    #
    fsumrecl
    #
    @42
    @1
    @44
    @47
    rplogcld
    #
    rerpdivcld
    resubcld
    #
    @49
    rerpdivcld
    recnd
    #
    lo1o12
    mpbii
    @42
    @39
    @84
    abscld
    @42
    @19
    @1
    @42
    @5
    @18
    @42
    @3
    @4
    @42
    @2
    @42
    @2
    @51
    recnd
    #
    abscld
    @52
    remulcld
    #
    @42
    @17
    @4
    @42
    @7
    @16
    vn
    @53
    @55
    @11
    @15
    @55
    @10
    @55
    @10
    @59
    recnd
    #
    abscld
    #
    @55
    @12
    @14
    @55
    @8
    cr
    wcel
    #
    @12
    cr
    wcel
    @55
    @8
    @57
    nnred
    #
    cr
    cr
    @8
    cS
    cS
    vi
    va
    pntsval.1
    pntsf
    #
    ffvelrni
    syl
    @55
    @13
    cr
    wcel
    #
    @14
    cr
    wcel
    @55
    @8
    c1
    @90
    @55
    1red
    resubcld
    #
    cr
    cr
    @13
    cS
    @91
    ffvelrni
    syl
    #
    resubcld
    #
    remulcld
    #
    fsumrecl
    #
    @82
    rerpdivcld
    #
    resubcld
    #
    @49
    rerpdivcld
    wtru
    @41
    @20
    @40
    cle
    wbr
    c1
    @1
    cle
    wbr
    @42
    @20
    @38
    cabs
    cfv
    #
    @1
    cdiv
    co
    #
    @40
    cle
    @42
    @19
    @100
    @1
    @99
    @42
    @38
    @42
    @21
    @37
    @42
    @2
    @4
    @85
    @42
    @4
    @52
    recnd
    #
    mulcld
    #
    @42
    @36
    @4
    @42
    @36
    @81
    recnd
    #
    @102
    @42
    @4
    @82
    rpne0d
    #
    divcld
    #
    subcld
    abscld
    #
    @49
    @42
    @19
    @5
    @36
    cabs
    cfv
    #
    @4
    cdiv
    co
    #
    cmin
    co
    #
    @100
    @99
    @42
    @5
    @109
    @86
    @42
    @108
    @4
    @42
    @36
    @104
    abscld
    #
    @82
    rerpdivcld
    #
    resubcld
    @107
    @42
    @109
    @18
    @5
    @112
    @98
    @86
    @42
    @108
    @17
    @4
    @111
    @97
    @82
    @42
    @108
    @7
    @35
    cabs
    cfv
    #
    vn
    csu
    @17
    @111
    @42
    @7
    @113
    vn
    @53
    @55
    @35
    @55
    @35
    @80
    recnd
    #
    abscld
    #
    fsumrecl
    @97
    @42
    @7
    @35
    vn
    @53
    @114
    fsumabs
    @42
    @7
    @113
    @16
    vn
    @53
    @115
    @96
    @55
    @113
    @11
    @34
    cabs
    cfv
    #
    cmul
    co
    @16
    cle
    @55
    @10
    @34
    @87
    @55
    @34
    @79
    recnd
    #
    absmuld
    @55
    @116
    @15
    @11
    @55
    @34
    @117
    abscld
    @95
    @88
    @55
    @10
    @87
    absge0d
    @55
    @116
    @30
    cabs
    cfv
    #
    @33
    cabs
    cfv
    #
    caddc
    co
    #
    @15
    cle
    @55
    @30
    @33
    @55
    @30
    @75
    recnd
    #
    @55
    @33
    @78
    recnd
    #
    abs2dif2d
    @55
    @14
    @30
    @33
    caddc
    co
    #
    caddc
    co
    #
    @14
    cmin
    co
    @123
    @15
    @120
    @55
    @14
    @123
    @55
    @14
    @94
    recnd
    @55
    @30
    @33
    @121
    @122
    addcld
    pncan2d
    @55
    @12
    @124
    @14
    cmin
    @55
    @60
    vk
    cv
    #
    cvma
    cfv
    #
    @125
    clog
    cfv
    #
    cmul
    co
    #
    @22
    @125
    cdvds
    wbr
    #
    vy
    cn
    crab
    #
    @26
    @125
    @25
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
    caddc
    co
    #
    vk
    csu
    #
    c1
    @13
    cfz
    co
    #
    @135
    vk
    csu
    #
    @33
    @30
    caddc
    co
    #
    caddc
    co
    @12
    @124
    @55
    @135
    @139
    vk
    c1
    @8
    @54
    @8
    c1
    cuz
    cfv
    wcel
    @42
    @8
    c1
    @6
    elfzuz
    adantl
    @55
    @125
    @60
    wcel
    #
    wa
    #
    @135
    @141
    @128
    @134
    @141
    @126
    @127
    @141
    @125
    cn
    wcel
    #
    @126
    cr
    wcel
    @140
    @142
    @55
    @125
    @8
    elfznn
    adantl
    #
    @125
    vmacl
    syl
    @141
    @125
    @141
    @125
    @143
    nnrpd
    relogcld
    remulcld
    @141
    @130
    @133
    vm
    @141
    c1
    @125
    cfz
    co
    #
    cfn
    wcel
    @130
    @144
    wss
    #
    @130
    cfn
    wcel
    @141
    c1
    @125
    fzfid
    @141
    @142
    @145
    @143
    @125
    vy
    dvdsssfz1
    syl
    @144
    @130
    ssfi
    syl2anc
    @141
    @25
    @130
    wcel
    #
    wa
    #
    @26
    @132
    @147
    @65
    @66
    @147
    @130
    cn
    @25
    @129
    vy
    cn
    ssrab2
    #
    @141
    @146
    simpr
    sseldi
    @69
    syl
    @147
    @131
    cn
    wcel
    @132
    cr
    wcel
    @147
    @130
    cn
    @131
    @148
    @141
    @142
    @146
    @131
    @130
    wcel
    @143
    vy
    @25
    @125
    dvdsdivcl
    sylan
    sseldi
    @131
    vmacl
    syl
    remulcld
    fsumrecl
    readdcld
    recnd
    @125
    @8
    wceq
    #
    @128
    @33
    @134
    @30
    caddc
    @149
    @126
    @31
    @127
    @32
    cmul
    @125
    @8
    cvma
    fveq2
    @125
    @8
    clog
    fveq2
    oveq12d
    @149
    @130
    @24
    @133
    @29
    vm
    @149
    @129
    @23
    vy
    cn
    @125
    @8
    @22
    cdvds
    breq2
    rabbidv
    @149
    @133
    @29
    wceq
    @63
    @149
    @132
    @28
    @26
    cmul
    @149
    @131
    @27
    cvma
    @125
    @8
    @25
    cdiv
    oveq1
    fveq2d
    oveq2d
    adantr
    sumeq12rdv
    oveq12d
    fsumm1
    @55
    @12
    c1
    @8
    cfl
    cfv
    #
    cfz
    co
    #
    @135
    vk
    csu
    #
    @136
    @55
    @89
    @12
    @152
    wceq
    @90
    vy
    @8
    cS
    vi
    vm
    vk
    va
    pntsval.1
    pntsval2
    syl
    @55
    @151
    @60
    @135
    vk
    @55
    @150
    @8
    c1
    cfz
    @55
    @8
    cz
    wcel
    @150
    @8
    wceq
    @55
    @8
    @57
    nnzd
    #
    @8
    flid
    syl
    oveq2d
    sumeq1d
    eqtrd
    @55
    @14
    @138
    @123
    @139
    caddc
    @55
    @14
    c1
    @13
    cfl
    cfv
    #
    cfz
    co
    #
    @135
    vk
    csu
    #
    @138
    @55
    @92
    @14
    @156
    wceq
    @93
    vy
    @13
    cS
    vi
    vm
    vk
    va
    pntsval.1
    pntsval2
    syl
    @55
    @155
    @137
    @135
    vk
    @55
    @154
    @13
    c1
    cfz
    @55
    @13
    cz
    wcel
    @154
    @13
    wceq
    @55
    @8
    c1
    @153
    @55
    1zzd
    zsubcld
    @13
    flid
    syl
    oveq2d
    sumeq1d
    eqtrd
    @55
    @30
    @33
    @121
    @122
    addcomd
    oveq12d
    3eqtr4d
    oveq1d
    @55
    @118
    @30
    @119
    @33
    caddc
    @55
    @30
    @75
    @55
    @24
    @29
    vm
    @62
    @74
    @64
    @26
    @28
    @70
    @73
    @64
    @65
    cc0
    @26
    cle
    wbr
    @68
    @25
    vmage0
    syl
    @64
    @71
    cc0
    @28
    cle
    wbr
    @72
    @27
    vmage0
    syl
    mulge0d
    fsumge0
    absidd
    @55
    @33
    @78
    @55
    @31
    @32
    @76
    @77
    @55
    @56
    cc0
    @31
    cle
    wbr
    @57
    @8
    vmage0
    syl
    @55
    @8
    @90
    @55
    @8
    @57
    nnge1d
    logge0d
    mulge0d
    absidd
    oveq12d
    3eqtr4d
    breqtrrd
    lemul2ad
    eqbrtrd
    fsumle
    letrd
    lediv1dd
    lesub2dd
    @42
    @21
    cabs
    cfv
    #
    @37
    cabs
    cfv
    #
    cmin
    co
    @110
    @100
    cle
    @42
    @157
    @5
    @158
    @109
    cmin
    @42
    @157
    @3
    @4
    cabs
    cfv
    #
    cmul
    co
    @5
    @42
    @2
    @4
    @85
    @102
    absmuld
    @42
    @159
    @4
    @3
    cmul
    @42
    @4
    @52
    @42
    @1
    @44
    @48
    logge0d
    absidd
    #
    oveq2d
    eqtrd
    @42
    @158
    @108
    @159
    cdiv
    co
    @109
    @42
    @36
    @4
    @104
    @102
    @105
    absdivd
    @42
    @159
    @4
    @108
    cdiv
    @160
    oveq2d
    eqtrd
    oveq12d
    @42
    @21
    @37
    @103
    @106
    abs2difd
    eqbrtrrd
    letrd
    lediv1dd
    @42
    @40
    @100
    @1
    cabs
    cfv
    #
    cdiv
    co
    @101
    @42
    @38
    @1
    @42
    @38
    @83
    recnd
    @42
    @1
    @44
    recnd
    @42
    @1
    @49
    rpne0d
    absdivd
    @42
    @161
    @1
    @100
    cdiv
    @42
    @1
    @44
    @42
    @1
    @49
    rpge0d
    absidd
    oveq2d
    eqtrd
    breqtrrd
    adantrr
    lo1le
    trud
end
