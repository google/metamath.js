include "cn0.mm"
include "wcel.mm"
include "cfv.mm"
include "cfa.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "cv.mm"
include "cexp.mm"
include "cdiv.mm"
include "csu.mm"
include "cmul.mm"
include "wceq.mm"
include "caddc.mm"
include "wa.mm"
include "fveq2.mm"
include "subfac0.mm"
include "syl6eq.mm"
include "fac0.mm"
include "oveq2.mm"
include "sumeq1d.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "oveq1.mm"
include "0p1e1.mm"
include "fveq2d.mm"
include "subfac1.mm"
include "fac1.mm"
include "oveq2d.mm"
include "anbi12d.mm"
include "cz.mm"
include "cc.mm"
include "0z.mm"
include "ax-1cn.mm"
include "neg1cn.mm"
include "exp0.mm"
include "ax-mp.mm"
include "div1i.mm"
include "fsum1.mm"
include "mp2an.mm"
include "oveq2i.mm"
include "1t1e1.mm"
include "eqtr2i.mm"
include "wtru.mm"
include "nn0uz.mm"
include "1e0p1.mm"
include "exp1.mm"
include "cr.mm"
include "neg1rr.mm"
include "reexpcl.mm"
include "mpan.mm"
include "faccl.mm"
include "nndivred.mm"
include "recnd.mm"
include "adantl.mm"
include "0nn0.mm"
include "pm3.2i.mm"
include "a1i.mm"
include "1pneg1e0.mm"
include "fsump1i.mm"
include "trud.mm"
include "simpri.mm"
include "mul01i.mm"
include "wi.mm"
include "simpr.mm"
include "oveq12.mm"
include "ancoms.mm"
include "cmin.mm"
include "cn.mm"
include "nn0p1nn.mm"
include "subfacp1.mm"
include "syl.mm"
include "nn0cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "eqtrd.mm"
include "peano2nn0.mm"
include "nncnd.mm"
include "fzfid.mm"
include "elfznn0.mm"
include "fsumcl.mm"
include "expcl.mm"
include "sylancr.mm"
include "nnne0d.mm"
include "divcld.mm"
include "adddid.mm"
include "cuz.mm"
include "id.mm"
include "syl6eleq.mm"
include "fsump1.mm"
include "facp1.mm"
include "mulcomd.mm"
include "oveq1d.mm"
include "nn0cnd.mm"
include "mulassd.mm"
include "3eqtrd.mm"
include "div12d.mm"
include "divcan3d.mm"
include "divcan2d.mm"
include "mulcld.mm"
include "negsub.mm"
include "eqtr3d.mm"
include "expp1.mm"
include "3eqtr4d.mm"
include "addassd.mm"
include "add32d.mm"
include "eqcomd.mm"
include "mulid1d.mm"
include "adddird.mm"
include "syl5ibr.mm"
include "jcad.mm"
include "nn0ind.mm"
include "simpld.mm"

theorem subfacval2
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cS: class S
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let cN: class N
  let vg: setvar g
  let vh: setvar h
  let vm: setvar m
  let vs: setvar s
  let vz: setvar z
  let cA: class A
  let vb: setvar b
  let vc: setvar c
  let cF: class F
  let cB: class B
  let cC: class C
  let wph: wff ph
  let cK: class K
  let cM: class M
  let cV: class V
  assume derang.d: |- D = ( x e. Fin |-> ( # ` { f | ( f : x -1-1-onto-> x /\ A. y e. x ( f ` y ) =/= y ) } ) )
  assume subfac.n: |- S = ( n e. NN0 |-> ( D ` ( 1 ... n ) ) )

  disjoint f n
  disjoint f x
  disjoint f y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint f k
  disjoint N f
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint N k
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint D n
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint f g
  disjoint f h
  disjoint f m
  disjoint f s
  disjoint f z
  disjoint A f
  disjoint g h
  disjoint g m
  disjoint g n
  disjoint g s
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint h m
  disjoint h n
  disjoint h s
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint A h
  disjoint m n
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n s
  disjoint n z
  disjoint A n
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint b c
  disjoint b f
  disjoint b g
  disjoint b x
  disjoint b y
  disjoint F b
  disjoint c f
  disjoint c g
  disjoint c x
  disjoint c y
  disjoint F c
  disjoint F f
  disjoint F g
  disjoint F x
  disjoint F y
  disjoint c h
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c z
  disjoint N c
  disjoint g k
  disjoint N g
  disjoint h k
  disjoint N h
  disjoint k m
  disjoint k z
  disjoint N m
  disjoint N z
  disjoint b k
  disjoint b m
  disjoint b n
  disjoint b h
  disjoint b s
  disjoint b z
  disjoint B b
  disjoint c s
  disjoint B c
  disjoint B f
  disjoint B g
  disjoint B h
  disjoint B s
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C b
  disjoint C c
  disjoint C x
  disjoint C y
  disjoint b ph
  disjoint c ph
  disjoint ph x
  disjoint ph y
  disjoint K c
  disjoint K f
  disjoint K n
  disjoint K x
  disjoint K y
  disjoint M b
  disjoint M f
  disjoint M g
  disjoint M x
  disjoint M y
  disjoint S m
  disjoint V f
  assert |- ( N e. NN0 -> ( S ` N ) = ( ( ! ` N ) x. sum_ k e. ( 0 ... N ) ( ( -u 1 ^ k ) / ( ! ` k ) ) ) )

  proof
    cN
    cn0
    wcel
    cN
    cS
    cfv
    #
    cN
    cfa
    cfv
    #
    cc0
    cN
    cfz
    co
    #
    c1
    cneg
    #
    vk
    cv
    #
    cexp
    co
    #
    @4
    cfa
    cfv
    #
    cdiv
    co
    #
    vk
    csu
    #
    cmul
    co
    #
    wceq
    #
    cN
    c1
    caddc
    co
    #
    cS
    cfv
    #
    @11
    cfa
    cfv
    #
    cc0
    @11
    cfz
    co
    #
    @7
    vk
    csu
    #
    cmul
    co
    #
    wceq
    #
    vx
    cv
    #
    cS
    cfv
    #
    @18
    cfa
    cfv
    #
    cc0
    @18
    cfz
    co
    #
    @7
    vk
    csu
    #
    cmul
    co
    #
    wceq
    #
    @18
    c1
    caddc
    co
    #
    cS
    cfv
    #
    @25
    cfa
    cfv
    #
    cc0
    @25
    cfz
    co
    #
    @7
    vk
    csu
    #
    cmul
    co
    #
    wceq
    #
    wa
    c1
    c1
    cc0
    cc0
    cfz
    co
    #
    @7
    vk
    csu
    #
    cmul
    co
    #
    wceq
    #
    cc0
    c1
    cc0
    c1
    cfz
    co
    #
    @7
    vk
    csu
    #
    cmul
    co
    #
    wceq
    #
    wa
    vm
    cv
    #
    cS
    cfv
    #
    @40
    cfa
    cfv
    #
    cc0
    @40
    cfz
    co
    #
    @7
    vk
    csu
    #
    cmul
    co
    #
    wceq
    #
    @40
    c1
    caddc
    co
    #
    cS
    cfv
    #
    @47
    cfa
    cfv
    #
    cc0
    @47
    cfz
    co
    #
    @7
    vk
    csu
    #
    cmul
    co
    #
    wceq
    #
    wa
    #
    @53
    @47
    c1
    caddc
    co
    #
    cS
    cfv
    #
    @55
    cfa
    cfv
    #
    cc0
    @55
    cfz
    co
    #
    @7
    vk
    csu
    #
    cmul
    co
    #
    wceq
    #
    wa
    @10
    @17
    wa
    vx
    vm
    cN
    @18
    cc0
    wceq
    #
    @24
    @35
    @31
    @39
    @62
    @19
    c1
    @23
    @34
    @62
    @19
    cc0
    cS
    cfv
    c1
    @18
    cc0
    cS
    fveq2
    vx
    vy
    cD
    cS
    vf
    vn
    derang.d
    subfac.n
    subfac0
    syl6eq
    @62
    @20
    c1
    @22
    @33
    cmul
    @62
    @20
    cc0
    cfa
    cfv
    #
    c1
    @18
    cc0
    cfa
    fveq2
    fac0
    syl6eq
    @62
    @21
    @32
    @7
    vk
    @18
    cc0
    cc0
    cfz
    oveq2
    sumeq1d
    oveq12d
    eqeq12d
    @62
    @26
    cc0
    @30
    @38
    @62
    @26
    c1
    cS
    cfv
    cc0
    @62
    @25
    c1
    cS
    @62
    @25
    cc0
    c1
    caddc
    co
    c1
    @18
    cc0
    c1
    caddc
    oveq1
    0p1e1
    syl6eq
    #
    fveq2d
    vx
    vy
    cD
    cS
    vf
    vn
    derang.d
    subfac.n
    subfac1
    syl6eq
    @62
    @27
    c1
    @29
    @37
    cmul
    @62
    @27
    c1
    cfa
    cfv
    #
    c1
    @62
    @25
    c1
    cfa
    @64
    fveq2d
    fac1
    syl6eq
    @62
    @28
    @36
    @7
    vk
    @62
    @25
    c1
    cc0
    cfz
    @64
    oveq2d
    sumeq1d
    oveq12d
    eqeq12d
    anbi12d
    @18
    @40
    wceq
    #
    @24
    @46
    @31
    @53
    @66
    @19
    @41
    @23
    @45
    @18
    @40
    cS
    fveq2
    @66
    @20
    @42
    @22
    @44
    cmul
    @18
    @40
    cfa
    fveq2
    @66
    @21
    @43
    @7
    vk
    @18
    @40
    cc0
    cfz
    oveq2
    sumeq1d
    oveq12d
    eqeq12d
    @66
    @26
    @48
    @30
    @52
    @66
    @25
    @47
    cS
    @18
    @40
    c1
    caddc
    oveq1
    #
    fveq2d
    @66
    @27
    @49
    @29
    @51
    cmul
    @66
    @25
    @47
    cfa
    @67
    fveq2d
    @66
    @28
    @50
    @7
    vk
    @66
    @25
    @47
    cc0
    cfz
    @67
    oveq2d
    sumeq1d
    oveq12d
    eqeq12d
    anbi12d
    @18
    @47
    wceq
    #
    @24
    @53
    @31
    @61
    @68
    @19
    @48
    @23
    @52
    @18
    @47
    cS
    fveq2
    @68
    @20
    @49
    @22
    @51
    cmul
    @18
    @47
    cfa
    fveq2
    @68
    @21
    @50
    @7
    vk
    @18
    @47
    cc0
    cfz
    oveq2
    sumeq1d
    oveq12d
    eqeq12d
    @68
    @26
    @56
    @30
    @60
    @68
    @25
    @55
    cS
    @18
    @47
    c1
    caddc
    oveq1
    #
    fveq2d
    @68
    @27
    @57
    @29
    @59
    cmul
    @68
    @25
    @55
    cfa
    @69
    fveq2d
    @68
    @28
    @58
    @7
    vk
    @68
    @25
    @55
    cc0
    cfz
    @69
    oveq2d
    sumeq1d
    oveq12d
    eqeq12d
    anbi12d
    @18
    cN
    wceq
    #
    @24
    @10
    @31
    @17
    @70
    @19
    @0
    @23
    @9
    @18
    cN
    cS
    fveq2
    @70
    @20
    @1
    @22
    @8
    cmul
    @18
    cN
    cfa
    fveq2
    @70
    @21
    @2
    @7
    vk
    @18
    cN
    cc0
    cfz
    oveq2
    sumeq1d
    oveq12d
    eqeq12d
    @70
    @26
    @12
    @30
    @16
    @70
    @25
    @11
    cS
    @18
    cN
    c1
    caddc
    oveq1
    #
    fveq2d
    @70
    @27
    @13
    @29
    @15
    cmul
    @70
    @25
    @11
    cfa
    @71
    fveq2d
    @70
    @28
    @14
    @7
    vk
    @70
    @25
    @11
    cc0
    cfz
    @71
    oveq2d
    sumeq1d
    oveq12d
    eqeq12d
    anbi12d
    @35
    @39
    @34
    c1
    c1
    cmul
    co
    c1
    @33
    c1
    c1
    cmul
    cc0
    cz
    wcel
    c1
    cc
    wcel
    #
    @33
    c1
    wceq
    #
    0z
    ax-1cn
    @7
    c1
    vk
    cc0
    @4
    cc0
    wceq
    #
    @7
    c1
    c1
    cdiv
    co
    c1
    @74
    @5
    c1
    @6
    c1
    cdiv
    @74
    @5
    @3
    cc0
    cexp
    co
    #
    c1
    @4
    cc0
    @3
    cexp
    oveq2
    @3
    cc
    wcel
    #
    @75
    c1
    wceq
    neg1cn
    @3
    exp0
    ax-mp
    syl6eq
    @74
    @6
    @63
    c1
    @4
    cc0
    cfa
    fveq2
    fac0
    syl6eq
    oveq12d
    c1
    ax-1cn
    div1i
    syl6eq
    fsum1
    mp2an
    #
    oveq2i
    1t1e1
    eqtr2i
    @38
    c1
    cc0
    cmul
    co
    cc0
    @37
    cc0
    c1
    cmul
    c1
    cn0
    wcel
    #
    @37
    cc0
    wceq
    #
    @78
    @79
    wa
    wtru
    @7
    @3
    c1
    cc0
    vk
    cc0
    cc0
    c1
    cn0
    nn0uz
    1e0p1
    @4
    c1
    wceq
    #
    @7
    @3
    c1
    cdiv
    co
    @3
    @80
    @5
    @3
    @6
    c1
    cdiv
    @80
    @5
    @3
    c1
    cexp
    co
    #
    @3
    @4
    c1
    @3
    cexp
    oveq2
    @76
    @81
    @3
    wceq
    neg1cn
    @3
    exp1
    ax-mp
    syl6eq
    @80
    @6
    @65
    c1
    @4
    c1
    cfa
    fveq2
    fac1
    syl6eq
    oveq12d
    @3
    neg1cn
    div1i
    syl6eq
    @4
    cn0
    wcel
    #
    @7
    cc
    wcel
    #
    wtru
    @82
    @7
    @82
    @5
    @6
    @3
    cr
    wcel
    @82
    @5
    cr
    wcel
    neg1rr
    @3
    @4
    reexpcl
    mpan
    @4
    faccl
    nndivred
    recnd
    #
    adantl
    cc0
    cn0
    wcel
    #
    @73
    wa
    wtru
    @85
    @73
    0nn0
    @77
    pm3.2i
    a1i
    c1
    @3
    caddc
    co
    cc0
    wceq
    wtru
    1pneg1e0
    a1i
    fsump1i
    trud
    simpri
    oveq2i
    c1
    ax-1cn
    mul01i
    eqtr2i
    pm3.2i
    @40
    cn0
    wcel
    #
    @54
    @53
    @61
    @54
    @53
    wi
    @86
    @46
    @53
    simpr
    a1i
    @54
    @61
    @86
    @47
    @48
    @41
    caddc
    co
    #
    cmul
    co
    #
    @47
    @52
    @45
    caddc
    co
    #
    cmul
    co
    #
    wceq
    @54
    @87
    @89
    @47
    cmul
    @53
    @46
    @87
    @89
    wceq
    @48
    @52
    @41
    @45
    caddc
    oveq12
    ancoms
    oveq2d
    @86
    @56
    @88
    @60
    @90
    @86
    @56
    @47
    @48
    @47
    c1
    cmin
    co
    #
    cS
    cfv
    #
    caddc
    co
    #
    cmul
    co
    #
    @88
    @86
    @47
    cn
    wcel
    @56
    @94
    wceq
    @40
    nn0p1nn
    #
    vx
    vy
    cD
    cS
    vf
    vn
    @47
    derang.d
    subfac.n
    subfacp1
    syl
    @86
    @93
    @87
    @47
    cmul
    @86
    @92
    @41
    @48
    caddc
    @86
    @91
    @40
    cS
    @86
    @40
    cc
    wcel
    @72
    @91
    @40
    wceq
    @40
    nn0cn
    ax-1cn
    @40
    c1
    pncan
    sylancl
    fveq2d
    oveq2d
    oveq2d
    eqtrd
    @86
    @57
    @51
    @3
    @55
    cexp
    co
    #
    @57
    cdiv
    co
    #
    caddc
    co
    #
    cmul
    co
    #
    @47
    @42
    @55
    cmul
    co
    #
    @44
    cmul
    co
    #
    @3
    @47
    cexp
    co
    #
    caddc
    co
    #
    cmul
    co
    #
    @60
    @90
    @86
    @99
    @57
    @51
    cmul
    co
    #
    @57
    @97
    cmul
    co
    #
    caddc
    co
    @47
    @100
    cmul
    co
    #
    @44
    cmul
    co
    #
    @102
    @55
    cmul
    co
    #
    caddc
    co
    #
    @96
    caddc
    co
    #
    @104
    @86
    @57
    @51
    @97
    @86
    @57
    @86
    @55
    cn0
    wcel
    #
    @57
    cn
    wcel
    @86
    @47
    cn0
    wcel
    #
    @112
    @40
    peano2nn0
    #
    @47
    peano2nn0
    syl
    #
    @55
    faccl
    syl
    #
    nncnd
    #
    @86
    @50
    @7
    vk
    @86
    cc0
    @47
    fzfid
    @86
    @4
    @50
    wcel
    #
    wa
    @82
    @83
    @118
    @82
    @86
    @4
    @47
    elfznn0
    adantl
    @84
    syl
    #
    fsumcl
    @86
    @96
    @57
    @86
    @76
    @112
    @96
    cc
    wcel
    neg1cn
    @115
    @3
    @55
    expcl
    sylancr
    #
    @117
    @86
    @57
    @116
    nnne0d
    #
    divcld
    adddid
    @86
    @105
    @110
    @106
    @96
    caddc
    @86
    @105
    @57
    @44
    @102
    @49
    cdiv
    co
    #
    caddc
    co
    #
    cmul
    co
    @57
    @44
    cmul
    co
    #
    @57
    @122
    cmul
    co
    #
    caddc
    co
    @110
    @86
    @51
    @123
    @57
    cmul
    @86
    @7
    @122
    vk
    cc0
    @40
    @86
    @40
    cn0
    cc0
    cuz
    cfv
    #
    @86
    id
    nn0uz
    syl6eleq
    @119
    @4
    @47
    wceq
    @5
    @102
    @6
    @49
    cdiv
    @4
    @47
    @3
    cexp
    oveq2
    @4
    @47
    cfa
    fveq2
    oveq12d
    fsump1
    #
    oveq2d
    @86
    @57
    @44
    @122
    @117
    @86
    @43
    @7
    vk
    @86
    cc0
    @40
    fzfid
    @86
    @4
    @43
    wcel
    #
    wa
    @82
    @83
    @128
    @82
    @86
    @4
    @40
    elfznn0
    adantl
    @84
    syl
    fsumcl
    #
    @86
    @102
    @49
    @86
    @76
    @113
    @102
    cc
    wcel
    neg1cn
    @114
    @3
    @47
    expcl
    sylancr
    #
    @86
    @49
    @86
    @113
    @49
    cn
    wcel
    @114
    @47
    faccl
    syl
    #
    nncnd
    #
    @86
    @49
    @131
    nnne0d
    #
    divcld
    #
    adddid
    @86
    @124
    @108
    @125
    @109
    caddc
    @86
    @57
    @107
    @44
    cmul
    @86
    @57
    @49
    @55
    cmul
    co
    #
    @47
    @42
    cmul
    co
    #
    @55
    cmul
    co
    @107
    @86
    @113
    @57
    @135
    wceq
    @114
    @47
    facp1
    syl
    #
    @86
    @49
    @136
    @55
    cmul
    @86
    @49
    @42
    @47
    cmul
    co
    #
    @136
    @40
    facp1
    #
    @86
    @42
    @47
    @86
    @42
    @40
    faccl
    nncnd
    #
    @86
    @47
    @95
    nncnd
    #
    mulcomd
    eqtrd
    oveq1d
    @86
    @47
    @42
    @55
    @141
    @140
    @86
    @55
    @115
    nn0cnd
    #
    mulassd
    3eqtrd
    oveq1d
    @86
    @125
    @102
    @57
    @49
    cdiv
    co
    #
    cmul
    co
    @109
    @86
    @57
    @102
    @49
    @117
    @130
    @132
    @133
    div12d
    @86
    @143
    @55
    @102
    cmul
    @86
    @143
    @135
    @49
    cdiv
    co
    @55
    @86
    @57
    @135
    @49
    cdiv
    @137
    oveq1d
    @86
    @55
    @49
    @142
    @132
    @133
    divcan3d
    eqtrd
    oveq2d
    eqtrd
    oveq12d
    3eqtrd
    @86
    @96
    @57
    @120
    @117
    @121
    divcan2d
    oveq12d
    @86
    @108
    @109
    @96
    caddc
    co
    #
    caddc
    co
    @47
    @101
    cmul
    co
    #
    @47
    @102
    cmul
    co
    #
    caddc
    co
    @111
    @104
    @86
    @108
    @145
    @144
    @146
    caddc
    @86
    @47
    @100
    @44
    @141
    @86
    @42
    @55
    @140
    @142
    mulcld
    #
    @129
    mulassd
    @86
    @109
    @102
    @3
    cmul
    co
    #
    caddc
    co
    #
    @102
    @47
    cmul
    co
    #
    @144
    @146
    @86
    @102
    @55
    @3
    caddc
    co
    #
    cmul
    co
    @149
    @150
    @86
    @102
    @55
    @3
    @130
    @142
    @76
    @86
    neg1cn
    a1i
    adddid
    @86
    @151
    @47
    @102
    cmul
    @86
    @151
    @55
    c1
    cmin
    co
    #
    @47
    @86
    @55
    cc
    wcel
    @72
    @151
    @152
    wceq
    @142
    ax-1cn
    @55
    c1
    negsub
    sylancl
    @86
    @47
    cc
    wcel
    @72
    @152
    @47
    wceq
    @141
    ax-1cn
    @47
    c1
    pncan
    sylancl
    eqtrd
    oveq2d
    eqtr3d
    @86
    @96
    @148
    @109
    caddc
    @86
    @76
    @113
    @96
    @148
    wceq
    neg1cn
    @114
    @3
    @47
    expp1
    sylancr
    oveq2d
    @86
    @47
    @102
    @141
    @130
    mulcomd
    3eqtr4d
    oveq12d
    @86
    @108
    @109
    @96
    @86
    @107
    @44
    @86
    @47
    @100
    @141
    @147
    mulcld
    @129
    mulcld
    @86
    @102
    @55
    @130
    @142
    mulcld
    @120
    addassd
    @86
    @47
    @101
    @102
    @141
    @86
    @100
    @44
    @147
    @129
    mulcld
    @130
    adddid
    3eqtr4d
    3eqtrd
    @86
    @59
    @98
    @57
    cmul
    @86
    @7
    @97
    vk
    cc0
    @47
    @86
    @47
    cn0
    @126
    @114
    nn0uz
    syl6eleq
    @86
    @4
    @58
    wcel
    #
    wa
    @82
    @83
    @153
    @82
    @86
    @4
    @55
    elfznn0
    adantl
    @84
    syl
    @4
    @55
    wceq
    @5
    @96
    @6
    @57
    cdiv
    @4
    @55
    @3
    cexp
    oveq2
    @4
    @55
    cfa
    fveq2
    oveq12d
    fsump1
    oveq2d
    @86
    @89
    @103
    @47
    cmul
    @86
    @49
    @44
    cmul
    co
    #
    @102
    caddc
    co
    #
    @45
    caddc
    co
    @154
    @45
    caddc
    co
    #
    @102
    caddc
    co
    @89
    @103
    @86
    @154
    @102
    @45
    @86
    @49
    @44
    @132
    @129
    mulcld
    @130
    @86
    @42
    @44
    @140
    @129
    mulcld
    add32d
    @86
    @52
    @155
    @45
    caddc
    @86
    @52
    @49
    @123
    cmul
    co
    @154
    @49
    @122
    cmul
    co
    #
    caddc
    co
    @155
    @86
    @51
    @123
    @49
    cmul
    @127
    oveq2d
    @86
    @49
    @44
    @122
    @132
    @129
    @134
    adddid
    @86
    @157
    @102
    @154
    caddc
    @86
    @102
    @49
    @130
    @132
    @133
    divcan2d
    oveq2d
    3eqtrd
    oveq1d
    @86
    @101
    @156
    @102
    caddc
    @86
    @101
    @49
    @42
    caddc
    co
    #
    @44
    cmul
    co
    @156
    @86
    @100
    @158
    @44
    cmul
    @86
    @100
    @138
    @42
    c1
    cmul
    co
    #
    caddc
    co
    @158
    @86
    @42
    @47
    c1
    @140
    @141
    @72
    @86
    ax-1cn
    a1i
    adddid
    @86
    @138
    @49
    @159
    @42
    caddc
    @86
    @49
    @138
    @139
    eqcomd
    @86
    @42
    @140
    mulid1d
    oveq12d
    eqtrd
    oveq1d
    @86
    @49
    @42
    @44
    @132
    @140
    @129
    adddird
    eqtrd
    oveq1d
    3eqtr4d
    oveq2d
    3eqtr4d
    eqeq12d
    syl5ibr
    jcad
    nn0ind
    simpld
end
