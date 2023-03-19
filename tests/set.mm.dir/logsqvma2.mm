include "cn.mm"
include "wcel.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "cvma.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "csu.mm"
include "clog.mm"
include "caddc.mm"
include "cmpt.mm"
include "cmu.mm"
include "c2.mm"
include "cexp.mm"
include "cc.mm"
include "c1.mm"
include "cfz.mm"
include "cfn.mm"
include "wss.mm"
include "fzfid.mm"
include "dvdsssfz1.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "wa.mm"
include "cr.mm"
include "ssrab2.mm"
include "simpr.mm"
include "sseldi.mm"
include "vmacl.mm"
include "syl.mm"
include "dvdsdivcl.mm"
include "remulcld.mm"
include "fsumrecl.mm"
include "nnrp.mm"
include "relogcld.mm"
include "readdcld.mm"
include "recnd.mm"
include "adantl.mm"
include "eqid.mm"
include "fmptd.mm"
include "wceq.mm"
include "breq2.mm"
include "rabbidv.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "adantr.mm"
include "sumeq12dv.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "ovex.mm"
include "fvmpt3i.mm"
include "sumeq2dv.mm"
include "logsqvma.mm"
include "eqtr2d.mm"
include "mpteq2dva.mm"
include "muinv.mm"
include "fveq1d.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "cbvsumv.mm"
include "syl5eq.mm"
include "mpteq2ia.mm"
include "sumex.mm"
include "3eqtr3rd.mm"

theorem logsqvma2
  let vx: setvar x
  let cN: class N
  let vd: setvar d
  let vc: setvar c
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vu: setvar u
  let vy: setvar y

  disjoint d x
  disjoint N d
  disjoint N x
  disjoint c d
  disjoint c i
  disjoint c j
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c u
  disjoint c x
  disjoint c y
  disjoint N c
  disjoint d i
  disjoint d j
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint d u
  disjoint d y
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i u
  disjoint i x
  disjoint i y
  disjoint N i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j u
  disjoint j x
  disjoint j y
  disjoint N j
  disjoint k m
  disjoint k n
  disjoint k u
  disjoint k x
  disjoint k y
  disjoint N k
  disjoint m n
  disjoint m u
  disjoint m x
  disjoint m y
  disjoint N m
  disjoint n u
  disjoint n x
  disjoint n y
  disjoint N n
  disjoint u x
  disjoint u y
  disjoint N u
  disjoint x y
  disjoint N y
  assert |- ( N e. NN -> sum_ d e. { x e. NN | x || N } ( ( mmu ` d ) x. ( ( log ` ( N / d ) ) ^ 2 ) ) = ( sum_ d e. { x e. NN | x || N } ( ( Lam ` d ) x. ( Lam ` ( N / d ) ) ) + ( ( Lam ` N ) x. ( log ` N ) ) ) )

  proof
    cN
    cn
    wcel
    #
    cN
    vk
    cn
    vx
    cv
    #
    vk
    cv
    #
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    vd
    cv
    #
    cvma
    cfv
    #
    @2
    @5
    cdiv
    co
    #
    cvma
    cfv
    #
    cmul
    co
    #
    vd
    csu
    #
    @2
    cvma
    cfv
    #
    @2
    clog
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    #
    cfv
    cN
    vi
    cn
    @1
    vi
    cv
    #
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    vj
    cv
    #
    cmu
    cfv
    #
    @16
    @19
    cdiv
    co
    #
    vn
    cn
    vn
    cv
    #
    clog
    cfv
    #
    c2
    cexp
    co
    #
    cmpt
    #
    cfv
    #
    cmul
    co
    #
    vj
    csu
    #
    cmpt
    #
    cfv
    @1
    cN
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    @6
    cN
    @5
    cdiv
    co
    #
    cvma
    cfv
    #
    cmul
    co
    #
    vd
    csu
    #
    cN
    cvma
    cfv
    #
    cN
    clog
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    @31
    @5
    cmu
    cfv
    #
    @32
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
    @0
    cN
    @15
    @29
    @0
    vx
    vj
    vm
    vi
    vn
    @15
    @25
    @0
    vk
    cn
    @14
    cc
    @15
    @2
    cn
    wcel
    #
    @14
    cc
    wcel
    @0
    @45
    @14
    @45
    @10
    @13
    @45
    @4
    @9
    vd
    @45
    c1
    @2
    cfz
    co
    #
    cfn
    wcel
    @4
    @46
    wss
    @4
    cfn
    wcel
    @45
    c1
    @2
    fzfid
    @2
    vx
    dvdsssfz1
    @46
    @4
    ssfi
    syl2anc
    @45
    @5
    @4
    wcel
    #
    wa
    #
    @6
    @8
    @48
    @5
    cn
    wcel
    @6
    cr
    wcel
    @48
    @4
    cn
    @5
    @3
    vx
    cn
    ssrab2
    #
    @45
    @47
    simpr
    sseldi
    @5
    vmacl
    syl
    @48
    @7
    cn
    wcel
    @8
    cr
    wcel
    @48
    @4
    cn
    @7
    @49
    vx
    @5
    @2
    dvdsdivcl
    sseldi
    @7
    vmacl
    syl
    remulcld
    fsumrecl
    @45
    @11
    @12
    @2
    vmacl
    @45
    @2
    @2
    nnrp
    relogcld
    remulcld
    readdcld
    recnd
    adantl
    @15
    eqid
    #
    fmptd
    @0
    vn
    cn
    @24
    @1
    @22
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    vm
    cv
    #
    @15
    cfv
    #
    vm
    csu
    #
    @0
    @22
    cn
    wcel
    #
    wa
    #
    @55
    @52
    @1
    @53
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    @6
    @53
    @5
    cdiv
    co
    #
    cvma
    cfv
    #
    cmul
    co
    #
    vd
    csu
    #
    @53
    cvma
    cfv
    #
    @53
    clog
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    vm
    csu
    #
    @24
    @57
    @52
    @54
    @67
    vm
    @57
    @53
    @52
    wcel
    #
    wa
    #
    @53
    cn
    wcel
    @54
    @67
    wceq
    @70
    @52
    cn
    @53
    @51
    vx
    cn
    ssrab2
    @57
    @69
    simpr
    sseldi
    vk
    @53
    @14
    @67
    cn
    @15
    @2
    @53
    wceq
    #
    @10
    @63
    @13
    @66
    caddc
    @71
    @4
    @59
    @9
    @62
    vd
    @71
    @3
    @58
    vx
    cn
    @2
    @53
    @1
    cdvds
    breq2
    rabbidv
    @71
    @9
    @62
    wceq
    @47
    @71
    @8
    @61
    @6
    cmul
    @71
    @7
    @60
    cvma
    @2
    @53
    @5
    cdiv
    oveq1
    fveq2d
    oveq2d
    adantr
    sumeq12dv
    @71
    @11
    @64
    @12
    @65
    cmul
    @2
    @53
    cvma
    fveq2
    @2
    @53
    clog
    fveq2
    oveq12d
    oveq12d
    @50
    @10
    @13
    caddc
    ovex
    #
    fvmpt3i
    syl
    sumeq2dv
    @56
    @68
    @24
    wceq
    @0
    vx
    vd
    @22
    vm
    logsqvma
    adantl
    eqtr2d
    mpteq2dva
    muinv
    fveq1d
    vk
    cN
    @14
    @39
    cn
    @15
    @2
    cN
    wceq
    #
    @10
    @35
    @13
    @38
    caddc
    @73
    @4
    @31
    @9
    @34
    vd
    @73
    @3
    @30
    vx
    cn
    @2
    cN
    @1
    cdvds
    breq2
    rabbidv
    @73
    @9
    @34
    wceq
    @47
    @73
    @8
    @33
    @6
    cmul
    @73
    @7
    @32
    cvma
    @2
    cN
    @5
    cdiv
    oveq1
    fveq2d
    oveq2d
    adantr
    sumeq12dv
    @73
    @11
    @36
    @12
    @37
    cmul
    @2
    cN
    cvma
    fveq2
    @2
    cN
    clog
    fveq2
    oveq12d
    oveq12d
    @50
    @72
    fvmpt3i
    vi
    cN
    @18
    @20
    @21
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
    vj
    csu
    #
    @44
    cn
    @29
    @16
    cN
    wceq
    #
    @77
    @18
    @40
    @16
    @5
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
    @44
    @18
    @76
    @82
    vj
    vd
    @19
    @5
    wceq
    #
    @20
    @40
    @75
    @81
    cmul
    @19
    @5
    cmu
    fveq2
    @83
    @74
    @80
    c2
    cexp
    @83
    @21
    @79
    clog
    @19
    @5
    @16
    cdiv
    oveq2
    fveq2d
    oveq1d
    oveq12d
    cbvsumv
    @78
    @18
    @31
    @82
    @43
    vd
    @78
    @17
    @30
    vx
    cn
    @16
    cN
    @1
    cdvds
    breq2
    rabbidv
    @78
    @82
    @43
    wceq
    @5
    @18
    wcel
    @78
    @81
    @42
    @40
    cmul
    @78
    @80
    @41
    c2
    cexp
    @78
    @79
    @32
    clog
    @16
    cN
    @5
    cdiv
    oveq1
    fveq2d
    oveq1d
    oveq2d
    adantr
    sumeq12dv
    syl5eq
    vi
    cn
    @28
    @77
    @16
    cn
    wcel
    #
    @18
    @27
    @76
    vj
    @84
    @19
    @18
    wcel
    wa
    #
    @26
    @75
    @20
    cmul
    @85
    @21
    cn
    wcel
    @26
    @75
    wceq
    @85
    @18
    cn
    @21
    @17
    vx
    cn
    ssrab2
    vx
    @19
    @16
    dvdsdivcl
    sseldi
    vn
    @21
    @24
    @75
    cn
    @25
    @22
    @21
    wceq
    @23
    @74
    c2
    cexp
    @22
    @21
    clog
    fveq2
    oveq1d
    @25
    eqid
    @23
    c2
    cexp
    ovex
    fvmpt3i
    syl
    oveq2d
    sumeq2dv
    mpteq2ia
    @18
    @76
    vj
    sumex
    fvmpt3i
    3eqtr3rd
end
